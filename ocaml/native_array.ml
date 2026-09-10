(** Native realization of primitive arrays.  The default value implements
    out-of-bounds [PArray.get]; [set] copies its backing array to preserve the
    persistent semantics of [PArray.set]. *)

type 'a t = {
  data : 'a array;
  default : 'a;
}

(* ExtrOCamlInt63 and coq-core.kernel realize [Uint63.t] as an OCaml int on
   the required 64-bit runtime.  [%identity] makes that representation
   boundary explicit without allocating the pair returned by [to_int2]. *)
external int_of_uint63 : Uint63.t -> int = "%identity"
external uint63_of_int : int -> Uint63.t = "%identity"

(* Reuse the limit of the linked coq-core runtime rather than duplicating it.
   This also ensures that every valid in-bounds index has a nonnegative OCaml
   int representation. *)
let max_length = Parray.max_length
let max_length_int = int_of_uint63 max_length

let[@inline always] length a =
  uint63_of_int (Array.length a.data)

let[@inline always] get a index =
  let index = int_of_uint63 index in
  (* Uint63 values in [2^62,2^63) look negative as OCaml ints.  They are
     necessarily out of bounds because certificate arrays are much shorter. *)
  if 0 <= index && index < Array.length a.data then
    Array.unsafe_get a.data index
  else
    a.default

let init length f default =
  let length = int_of_uint63 length in
  if length < 0 || max_length_int < length then
    invalid_arg "Native_array.init: length exceeds PArray.max_length";
  {
    data = Array.init length (fun i -> f (uint63_of_int i));
    default;
  }

let make length default =
  let length = int_of_uint63 length in
  if length < 0 || max_length_int < length then
    invalid_arg "Native_array.make: length exceeds PArray.max_length";
  { data = Array.make length default; default }

let set a index value =
  let index = int_of_uint63 index in
  if index < 0 || Array.length a.data <= index then
    a
  else
    let data = Array.copy a.data in
    Array.unsafe_set data index value;
    { a with data }
