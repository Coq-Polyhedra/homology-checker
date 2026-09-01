(**
  A stable name for Zarith inside extracted code.  Coq also extracts an
  internal module named [Z] through arithmetic dependencies; referring to
  Zarith through this module prevents that generated name from shadowing it.
*)
type t = Z.t

let zero = Z.zero
let equal = Z.equal
let add = Z.add
let mul = Z.mul
let lt = Z.lt
let leq = Z.leq
