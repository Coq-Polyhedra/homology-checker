From Coq Require Import Extraction.
Extraction Language OCaml.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt.
From Coq Require Import ExtrOCamlInt63 ExtrOCamlPArray.
From Cert Require Import LowLevelChecker.

(** The OCaml loader returns the nested value consumed by [build_cert]. *)
Definition vertex_containment_check c : bool :=
  VtxContainment.check_certificate (build_cert c).

Definition vertex_equality_check c : bool :=
  VtxEquality.check_certificate (build_cert c).

Definition graph_equality_check c : bool :=
  GraphEquality.check_certificate (build_cert c).

Set Extraction Optimize.

(**
  [Extraction Language] clears the inlining table.  Reassert this directive
  after selecting OCaml; otherwise Coq 8.20 emits the literal type variable
  from [ExtrOCamlPArray] and produces types such as ['a1 'a Parray.t].
*)
Extract Constant PArray.array "'a" => "Native_array.t".
Extraction Inline PArray.array.

(** Generic primitive-array realization.  Connectivity uses persistent
    [make]/[set]; all certificate traversals use the same backing arrays. *)
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
Extract Constant mem_sorted => "Native_array_ops.mem_sorted".
Extract Constant mem => "Native_array_ops.mem".
Extract Constant diff => "Native_array_ops.diff".

Extract Constant bfs => "Native_graph.bfs".

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
  vertex_containment_check vertex_equality_check graph_equality_check.
