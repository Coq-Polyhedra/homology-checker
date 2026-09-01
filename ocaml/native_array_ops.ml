(** Optimized realizations of generic Gallina operations over [PArray].

    This module contains no certificate-specific check. *)

external int_of_uint63 : Uint63.t -> int = "%identity"
external uint63_of_int : int -> Uint63.t = "%identity"

let fold f a initial =
  let data = a.Native_array.data in
  let accumulator = ref initial in
  for i = 0 to Array.length data - 1 do
    accumulator := f (Array.unsafe_get data i) !accumulator
  done;
  !accumulator

let foldi f a initial =
  let data = a.Native_array.data in
  let accumulator = ref initial in
  for i = 0 to Array.length data - 1 do
    accumulator :=
      f (uint63_of_int i) (Array.unsafe_get data i) !accumulator
  done;
  !accumulator

let fold_from_until f a first stop initial =
  let data = a.Native_array.data in
  let first_int = int_of_uint63 first in
  if 0 <= first_int && first_int <= Array.length data then begin
    let i = ref first_int in
    let accumulator = ref initial in
    while
      !i < Array.length data
      && not (stop (uint63_of_int !i) !accumulator)
    do
      accumulator := f (Array.unsafe_get data !i) !accumulator;
      incr i
    done;
    !accumulator
  end else
    Native_loop.ifold_from_until
      (fun index accumulator -> f (Native_array.get a index) accumulator)
      first (Native_array.length a) stop initial

let foldi_from_until f a first stop initial =
  let data = a.Native_array.data in
  let first_int = int_of_uint63 first in
  if 0 <= first_int && first_int <= Array.length data then begin
    let i = ref first_int in
    let accumulator = ref initial in
    while
      !i < Array.length data
      && not (stop (uint63_of_int !i) !accumulator)
    do
      accumulator :=
        f (uint63_of_int !i) (Array.unsafe_get data !i) !accumulator;
      incr i
    done;
    !accumulator
  end else
    Native_loop.ifold_from_until
      (fun index accumulator ->
        f index (Native_array.get a index) accumulator)
      first (Native_array.length a) stop initial

let fold2 f first second initial =
  let first_data = first.Native_array.data in
  let second_data = second.Native_array.data in
  let length = min (Array.length first_data) (Array.length second_data) in
  let accumulator = ref initial in
  for i = 0 to length - 1 do
    accumulator :=
      f (Array.unsafe_get first_data i)
        (Array.unsafe_get second_data i) !accumulator
  done;
  !accumulator

let fold3 f first second third initial =
  let first_data = first.Native_array.data in
  let second_data = second.Native_array.data in
  let third_data = third.Native_array.data in
  let length =
    min (Array.length first_data)
      (min (Array.length second_data) (Array.length third_data))
  in
  let accumulator = ref initial in
  for i = 0 to length - 1 do
    accumulator :=
      f (Array.unsafe_get first_data i)
        (Array.unsafe_get second_data i)
        (Array.unsafe_get third_data i) !accumulator
  done;
  !accumulator

let mem equal (array : 'a Native_array.t) value =
  let data = array.data in
  let i = ref 0 in
  let found = ref false in
  while !i < Array.length data && not !found do
    found := equal value (Array.unsafe_get data !i);
    incr i
  done;
  !found

let mem_sorted less_than (array : 'a Native_array.t) value =
  let data = array.data in
  let low = ref 0 in
  let high = ref (Array.length data) in
  let found = ref false in
  while !low < !high && not !found do
    let middle = !low + ((!high - !low) / 2) in
    let candidate = Array.unsafe_get data middle in
    if less_than value candidate then
      high := middle
    else if less_than candidate value then
      low := middle + 1
    else
      found := true
  done;
  !found

(** Native implementations of generic operations on read-only arrays. *)
let diff less_than
    (first : 'a Native_array.t)
    (second : 'a Native_array.t) =
  let first_data = first.Native_array.data in
  let second_data = second.Native_array.data in
  let first_length = Array.length first_data in
  let second_length = Array.length second_data in

  let i = ref 0 in
  let j = ref 0 in
  let result = ref [] in

  while !i < first_length do
    let x = Array.unsafe_get first_data !i in

    if !j >= second_length then begin
      result := x :: !result;
      incr i
    end else begin
      let y = Array.unsafe_get second_data !j in

      if less_than x y then begin
        result := x :: !result;
        incr i
      end else if less_than y x then
        incr j
      else begin
        incr i;
        incr j
      end
    end
  done;

  !result