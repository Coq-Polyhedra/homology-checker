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

Definition eccentricity_check c dc :=
  Diameter.eccentricity (build_cert c) dc.

Set Extraction Optimize.

(**
  [Extraction Language] clears the inlining table.  Reassert this directive
  after selecting OCaml; otherwise Coq 8.20 emits the literal type variable
  from [ExtrOCamlPArray] and produces types such as ['a1 'a Parray.t].
*)
Extract Constant PArray.array "'a" => "Native_array.t".
Extraction Inline PArray.array.

(** Generic primitive-array realization: all certificate traversals use the
    same backing arrays. *)
Extract Constant PArray.get => "Native_array.get".
Extract Constant PArray.length => "Native_array.length".

(**
  [BigArray.array] (see BigArray.v) is the chunked two-level array holding the
  certificate's large index-keyed tables: [BigArray.get] is a [PArray] get on
  the chunk row followed by a [PArray] get inside that row, and the shape
  invariant [wf] -- a [Prop] field of the record, erased by extraction --
  guarantees ceil(n / 2^21) rows, every row full but the last, and the empty
  row as the outer default.  OCaml native arrays reach 2^54 entries, far beyond
  [BigArray.max_length] = 2^43 - 2^21, so the chunking is only needed on the
  Coq side: the big tables are realized FLAT, by the very arrays that
  already realize [PArray].

  Observable behavior is preserved by the flattening [Mk cs n _ |-> a], where
  [a] is the [Native_array.t] whose [data] are [rget cs 0], ..., [rget cs (n-1)]
  and whose [default] is [PArray.default (PArray.default cs)]:
  - [BigArray.length (Mk cs n _)] is [n], which is [Native_array.length a];
  - for [i < n], [BigArray.get (Mk cs n _) i = rget cs i = a.data.(i)], which is
    what [Native_array.get] returns in bounds;
  - for [i >= n], [BigArray.get_out_of_bounds] gives [BigArray.default], that is
    [PArray.default (PArray.default cs)] -- exactly the [a.default] returned by
    [Native_array.get] out of bounds.  Both notions of "out of bounds" agree:
    [Native_array.get] also rejects the Uint63 values in [2^62, 2^63), which are
    negative as OCaml ints, and those are past [n] for any representable [n].
  The loader already builds flat native arrays for those tables, so the
  extracted [BGraph], [BFacets] and [BVertices] are literally the flat
  [Uint63.t Native_array.t Native_array.t], [facet Native_array.t] and
  [vertex Native_array.t] it produces; the nested tuple consumed by
  [build_cert] is unchanged.

  Only [get] and [length] are reachable from the entry points: [make] and
  [set] occur in the Coq-side decoder alone, which is not extracted.  The
  constructor therefore needs no realization, and is mapped to a deliberately
  undefined OCaml identifier: should a future revision make [BigArray.Mk]
  reachable, the extracted code fails to compile instead of silently building a
  mis-shaped value.
*)
Extract Inductive BigArray.array => "Native_array.t"
  [ "bigarray_constructor_is_not_realized" ].
Extract Constant BigArray.get => "Native_array.get".
Extract Constant BigArray.length => "Native_array.length".

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
  vertex_containment_check vertex_equality_check graph_equality_check
  eccentricity_check.
