let mem equal (array : 'a Native_array.t) value =
  let data = array.data in
  let i = ref 0 in
  let found = ref false in
  while !i < Array.length data && not !found do
    found := equal value (Array.get data !i);
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
    let candidate = Array.get data middle in
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
    let x = Array.get first_data !i in

    if !j >= second_length then begin
      result := x :: !result;
      incr i
    end else begin
      let y = Array.get second_data !j in

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