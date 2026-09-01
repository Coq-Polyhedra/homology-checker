From Coq Require Import Extraction.
Extraction Language OCaml.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt.
From Coq Require Import ExtrOCamlInt63 ExtrOCamlPArray.
From Bignums Require Import BigN BigZ.
From Cert Require Import LowLevelChecker.

Set Extraction Optimize.

(**
  [Extraction Language] clears the inlining table.  Reassert this directive
  after selecting OCaml; otherwise Coq 8.20 emits the literal type variable
  from [ExtrOCamlPArray] and produces types such as ['a1 'a Parray.t].
*)
Extract Constant PArray.array "'a" => "Native_array.t".
Extraction Inline PArray.array.

(**
  Only [get] and [length] are reachable from [check_data].  In particular,
  the persistent-array updates in the unused BFS checker are not extracted.
  The native representation therefore stores certificate data in ordinary,
  read-only OCaml arrays while retaining PArray's out-of-bounds default.
*)
Extract Constant PArray.get => "Native_array.get".
Extract Constant PArray.length => "Native_array.length".

(**
  The proof-oriented definition of [ifold_] is a depth-63 binary recursion.
  Its extracted form allocates and destructures an [(index, accumulator)] pair
  at every logical iteration.  A Uint63 loop can reach every final index in at
  most [2^63-1] increments, exactly the fuel supplied by [Uint63.size], so the
  tail-recursive native realizations preserve its observable behavior.
*)
Extract Constant ifold => "Native_loop.ifold".
Extract Constant ifold_from_until => "Native_loop.ifold_from_until".

(**
  Preserve the Gallina membership algorithms while avoiding their extracted
  tuple-valued loop state.  No certificate-specific predicate is replaced.
*)
Extract Constant mem_sorted => "Native_membership.mem_sorted".
Extract Constant mem => "Native_membership.mem".

(**
  The checker never observes the representation of the two bignum types.
  Mapping the small interface in [LowLevelChecker.NativeBig] to Zarith keeps
  the extracted program compact and lets the native loader construct numbers
  directly from the base-2^63 limbs stored by coq-binreader.
*)
Extraction Blacklist Z Big_int_Z.

Extract Constant NativeBig.n => "Native_z.t".
Extract Constant NativeBig.z => "Native_z.t".

Extract Constant NativeBig.n_zero => "Native_z.zero".
Extract Constant NativeBig.n_eqb => "Native_z.equal".

Extract Constant NativeBig.z_zero => "Native_z.zero".
Extract Constant NativeBig.z_of_n => "(fun x -> x)".
Extract Constant NativeBig.z_add => "Native_z.add".
Extract Constant NativeBig.z_mul => "Native_z.mul".
Extract Constant NativeBig.z_eqb => "Native_z.equal".
Extract Constant NativeBig.z_ltb => "Native_z.lt".
Extract Constant NativeBig.z_leb => "Native_z.leq".

Extraction "ocaml/extracted_checker.ml" 
  build_cert
  VtxContainment.check_certificate 
  VtxEquality.check_certificate
  GraphEquality.check_certificate.
