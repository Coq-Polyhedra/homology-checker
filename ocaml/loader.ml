exception Malformed of int64 * string

type reader = {
  channel : in_channel;
  buffer : bytes;
  mutable position : int;
  mutable available : int;
  mutable offset : int64;
}

let buffer_size = 1 lsl 20

let malformed reader message = raise (Malformed (reader.offset, message))

let refill reader =
  reader.position <- 0;
  reader.available <- input reader.channel reader.buffer 0 buffer_size

let read_byte reader =
  if reader.position = reader.available then refill reader;
  if reader.available = 0 then malformed reader "unexpected end of file";
  let value = Char.code (Bytes.unsafe_get reader.buffer reader.position) in
  reader.position <- reader.position + 1;
  reader.offset <- Int64.succ reader.offset;
  value

let read_word_slow reader =
  let result = ref 0L in
  for shift = 0 to 7 do
    let byte = Int64.of_int (read_byte reader) in
    result := Int64.logor !result (Int64.shift_left byte (8 * shift))
  done;
  if Int64.compare !result 0L < 0 then
    malformed reader "word does not fit in an unsigned 63-bit integer";
  !result

let read_word reader =
  if reader.available - reader.position < 8 then read_word_slow reader
  else begin
    let value = Bytes.get_int64_le reader.buffer reader.position in
    reader.position <- reader.position + 8;
    reader.offset <- Int64.add reader.offset 8L;
    if Int64.compare value 0L < 0 then
      malformed reader "word does not fit in an unsigned 63-bit integer";
    value
  end

let read_uint63 reader = Uint63.of_int64 (read_word reader)

let int_of_count reader kind value =
  if Int64.compare value (Int64.of_int Sys.max_array_length) > 0 then
    malformed reader (kind ^ " is too large");
  Int64.to_int value

let read_big_n reader =
  let count = int_of_count reader "BigN limb count" (read_word reader) in
  match count with
  | 0 -> Z.zero
  | 1 -> Z.of_int64 (read_word reader)
  | _ ->
      let value = ref Z.zero in
      let shift = ref 0 in
      for _ = 1 to count do
        let limb = Z.of_int64 (read_word reader) in
        value := Z.logor !value (Z.shift_left limb !shift);
        shift := !shift + 63
      done;
      !value

let read_big_z reader =
  let nonnegative = read_word reader <> 0L in
  let magnitude = read_big_n reader in
  if nonnegative then magnitude else Z.neg magnitude

type descriptor =
  | Int63
  | BigN
  | BigZ
  | Pair of descriptor * descriptor
  | Array of descriptor

type 'a schema = {
  descriptor : descriptor;
  read : reader -> 'a;
}

let named name schema = {
  descriptor = schema.descriptor;
  read = (fun reader ->
    let start = reader.offset in
    try schema.read reader with
    | Malformed (offset, message) ->
        raise (Malformed (offset,
          Printf.sprintf "%s (from byte %Ld): %s" name start message)));
}

let int63 = { descriptor = Int63; read = read_uint63 }
let big_n = { descriptor = BigN; read = read_big_n }
let big_z = { descriptor = BigZ; read = read_big_z }

let pair first second = {
  descriptor = Pair (first.descriptor, second.descriptor);
  read = (fun reader ->
    let first_value = first.read reader in
    let second_value = second.read reader in
    first_value, second_value);
}

let array element = {
  descriptor = Array element.descriptor;
  read = (fun reader ->
    let length = read_uint63 reader in
    if not (Uint63.le length Native_array.max_length) then
      malformed reader "persistent-array length exceeds PArray.max_length";
    let default = element.read reader in
    Native_array.init length (fun _ -> element.read reader) default);
}

(* Capacity of the Coq-side [BigArray.array] (src/BigArray.v):
   2^21 * (2^22 - 1) = 2^43 - 2^21. *)
let big_max_length = Uint63.of_int 8796090925056

(* The element combinator for the tables the Coq certificate stores in a
   [BigArray.array].  The wire format is exactly the one read by [array] above,
   and by [read_big_array] / [big_array] in src/CertificateSchema.v: the same
   length word, the same leading element supplying the array default, then the
   same element stream in the same order, aborting on the same failures.  Only
   two things differ.  The bound is [BigArray.max_length] rather than
   [PArray.max_length]; that capacity is itself far below
   [Sys.max_array_length] = 2^54 - 1 on a 64-bit runtime, so the flat OCaml
   array is the looser of the two limits.  And the backing array is built here
   rather than through [Native_array.init], which enforces the [PArray] bound;
   the record produced is the same {data; default} that [Native_array.init]
   would return, with [Array.init] applying its function to 0, 1, ..., n-1 in
   that order, exactly as [Native_array.init] does. *)
let big_array element = {
  descriptor = Array element.descriptor;
  read = (fun reader ->
    let length = read_uint63 reader in
    if not (Uint63.le length big_max_length) then
      malformed reader "big-array length exceeds BigArray.max_length";
    let default = element.read reader in
    let count = Native_array.int_of_uint63 length in
    {
      Native_array.data = Array.init count (fun _ -> element.read reader);
      Native_array.default = default;
    });
}

let rec expect_descriptor reader = function
  | Int63 -> expect_tag reader 0L
  | BigN -> expect_tag reader 1L
  | BigZ -> expect_tag reader 2L
  | Pair (first, second) ->
      expect_tag reader 4L;
      expect_descriptor reader first;
      expect_descriptor reader second
  | Array element ->
      expect_tag reader 5L;
      expect_descriptor reader element
and expect_tag reader expected =
  let actual = read_word reader in
  if actual <> expected then
    malformed reader
      (Printf.sprintf "descriptor mismatch: expected %Ld, found %Ld"
         expected actual)

let int_array = named "uint63 array" (array int63)
let big_int_matrix = named "uint63 matrix" (big_array int_array)
let z_array = named "BigZ array" (array big_z)
let z_matrix = named "BigZ matrix" (array z_array)

let inequality = named "inequality" (pair z_array big_z)
let point = named "point" (pair z_array big_n)
let flag = named "flag" (pair int_array int_array)
let item = named "vertex" (pair int_array (pair point flag))
let facet = named "facet" (pair int_array int63)
(* The tables whose length is the number of facets or the number of vertices --
   [graph] and [facets] here, the vertex table and the three geometric
   components below -- are the ones held in a [BigArray.array]; their inner
   rows and every other table stay on the [PArray]-capped [array], mirroring
   the split made on the Coq side in src/CertificateSchema.v. *)
let simplex_graph =
  named "simplex graph" (pair big_int_matrix (big_array facet))
let geom =
  named "geometric graph"
    (pair big_int_matrix (pair big_int_matrix big_int_matrix))
let full_dim = named "full-dimensional witness" (pair point (pair z_matrix z_matrix))
let sparse_entry = named "sparse entry" (pair int63 big_z)
let sparse_vector = named "sparse vector" (array sparse_entry)

let root =
  named "root witness"
    (pair int63
      (pair int_array
        (pair z_matrix
          (pair z_matrix (array sparse_vector)))))

let payload =
  named "certificate payload"
    (pair (array inequality)
      (pair (big_array item)
        (pair simplex_graph
          (pair geom
            (pair full_dim root)))))

let certificate = named "certificate" (pair int63 (pair int63 payload))

let ensure_end reader =
  if reader.position <> reader.available then
    malformed reader "trailing data";
  refill reader;
  if reader.available <> 0 then malformed reader "trailing data"

let load filename =
  let channel = open_in_bin filename in
  Fun.protect
    ~finally:(fun () -> close_in_noerr channel)
    (fun () ->
      let reader = {
        channel;
        buffer = Bytes.create buffer_size;
        position = 0;
        available = 0;
        offset = 0L;
      } in
      expect_descriptor reader certificate.descriptor;
      let value = certificate.read reader in
      ensure_end reader;
      value)
