(** Realizations with allocation-free loop control for the two Uint63 folds
    used by the checker.

    [LowLevelChecker.ifold_] uses a depth-63 binary recursion as fuel.  It can
    perform [2^63-1] increments, so for Uint63 indices it reaches any distinct
    final index before exhausting its fuel.  These tail-recursive loops have
    the same observable result, including wraparound and the test-before-step
    behavior of [ifold_from_until], without constructing a pair at each step. *)

let rec ifold_loop f final index accumulator =
  if Uint63.equal index final then
    accumulator
  else
    ifold_loop f final (Uint63.add index Uint63.one)
      (f index accumulator)

let ifold f final accumulator =
  ifold_loop f final Uint63.zero accumulator

let rec ifold_until_loop f final stop index accumulator =
  if Uint63.equal index final || stop index accumulator then
    accumulator
  else
    ifold_until_loop f final stop (Uint63.add index Uint63.one)
      (f index accumulator)

let ifold_from_until f first final stop accumulator =
  ifold_until_loop f final stop first accumulator
