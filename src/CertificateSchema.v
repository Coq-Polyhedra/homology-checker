From Coq Require Import BinNums PArray Uint63.
From Bignums Require Import BigN BigZ.
From BinReader Require Import BinReader.
From Cert Require BigArray.

Open Scope array_scope.
Open Scope uint63_scope.

(* -------------------------------------------------------------------------- *)
(* Support: decoding a table into [BigArray.array]                            *)
(*                                                                            *)
(* [read_big_array] mirrors [Packed.read_array] (Packed.v, lines 457-528)     *)
(* byte for byte.  THE WIRE FORMAT IS UNCHANGED: the same length word, then   *)
(* the same single leading element -- decoded only to supply the array        *)
(* default, never stored -- then the same [length] elements in the same       *)
(* order, each written at the next index.  [big_array] even emits the very    *)
(* same descriptor constructor [Packed.DArray] as [Packed.array], so existing *)
(* certificate files and the writer (lrs-postprocess) are untouched.          *)
(*                                                                            *)
(* Only the materialization differs: [BigArray.make] / [BigArray.set] instead *)
(* of [PArray.make] / [PArray.set], and the capacity bound is                 *)
(* [BigArray.max_length] = 2^43 - 2^21 instead of [PArray.max_length].  A     *)
(* declared length above that bound is rejected LOUDLY -- the decoder returns *)
(* [None] -- rather than silently clamped by [make] and then truncated by     *)
(* out-of-range [set]s.                                                       *)
(* -------------------------------------------------------------------------- *)

Record big_array_state (A : Type) := BigArrayState {
  big_array_index : int;
  big_array_value : BigArray.array A;
  big_array_position : Packed.cursor
}.

Arguments BigArrayState {A} _ _ _.

Definition big_array_step {A : Type} (element : Packed.decoder A)
    (input : Packed.bytes) (state : big_array_state A)
    : option (big_array_state A) :=
  match element input (big_array_position A state) with
  | Some (value, position') =>
    Some (BigArrayState
      (big_array_index A state + 1)
      (BigArray.set (big_array_value A state) (big_array_index A state) value)
      position')
  | None => None
  end.

(** Repeat [big_array_step] in the same binary divide-and-conquer traversal as
    [Packed.array_fill_positive]: the recursion is structural on the binary
    counter, and a malformed element aborts immediately instead of running the
    remaining iterations on [None]. *)
Fixpoint big_array_fill_positive {A : Type} (element : Packed.decoder A)
    (input : Packed.bytes) (count : positive) (state : big_array_state A)
    : option (big_array_state A) :=
  match count with
  | xH => big_array_step element input state
  | xO count' =>
    match big_array_fill_positive element input count' state with
    | Some state' => big_array_fill_positive element input count' state'
    | None => None
    end
  | xI count' =>
    match big_array_fill_positive element input count' state with
    | Some state' =>
      match big_array_fill_positive element input count' state' with
      | Some state'' => big_array_step element input state''
      | None => None
      end
    | None => None
    end
  end.

Definition big_array_fill {A : Type} (element : Packed.decoder A)
    (input : Packed.bytes) (count : N) (state : big_array_state A)
    : option (big_array_state A) :=
  match count with
  | N0 => Some state
  | Npos count' => big_array_fill_positive element input count' state
  end.

Definition read_big_array {A : Type} (element : Packed.decoder A)
    : Packed.decoder (BigArray.array A) :=
  fun input position =>
    match Packed.read_word input position with
    | Some (length, position1) =>
      if length <=? BigArray.max_length then
        match element input position1 with
        | Some (default, position2) =>
          let value := BigArray.make length default in
          if BigArray.length value =? length then
            let count := Packed.uint63_to_N length in
            match big_array_fill element input count
                    (BigArrayState 0 value position2) with
            | Some state =>
              Some (big_array_value A state, big_array_position A state)
            | None => None
            end
          else None
        | None => None
        end
      else None
    | None => None
    end.

Definition big_array {A : Type} (element : Packed.schema A)
    : Packed.schema (BigArray.array A) :=
  Packed.Schema (Packed.DArray (Packed.schema_descriptor element))
    (read_big_array (Packed.schema_value element)).

(* -------------------------------------------------------------------------- *)
(* The certificate schema                                                     *)
(* -------------------------------------------------------------------------- *)

Definition int_array_schema :=
  Packed.array Packed.int63.

Definition z_array_schema :=
  Packed.array Packed.bigZ.

Definition z_matrix_schema :=
  Packed.array z_array_schema.

Definition inequality_schema :=
  Packed.pair z_array_schema Packed.bigZ.

Definition point_schema :=
  Packed.pair z_array_schema Packed.bigN.

Definition flag_schema :=
  Packed.pair int_array_schema int_array_schema.

Definition item_schema :=
  Packed.pair int_array_schema
    (Packed.pair point_schema flag_schema).

Definition facet_schema :=
  Packed.pair int_array_schema Packed.int63.

(** The per-facet tables are indexed by facets and outgrow [PArray]: the
    outer arrays are big, every inner row stays a plain [PArray]. *)
Definition simplex_graph_schema :=
  Packed.pair (big_array int_array_schema) (big_array facet_schema).

(** The geometric graph and the two edge tables are indexed by vertices and
    outgrow [PArray] as well; here too only the outer arrays are big. *)
Definition geom_schema :=
  Packed.pair (big_array int_array_schema)
    (Packed.pair (big_array int_array_schema) (big_array int_array_schema)).

Definition full_dim_schema :=
  Packed.pair point_schema
    (Packed.pair z_matrix_schema z_matrix_schema).

Definition sparse_entry_schema :=
  Packed.pair Packed.int63 Packed.bigZ.

Definition sparse_vector_schema :=
  Packed.array sparse_entry_schema.

Definition root_schema :=
  Packed.pair Packed.int63
    (Packed.pair int_array_schema
      (Packed.pair z_matrix_schema
        (Packed.pair z_matrix_schema
          (Packed.array sparse_vector_schema)))).

(** The vertex table is indexed by vertices, hence big; the inequality table
    is indexed by inequalities and stays a plain [PArray], as does [weights]
    inside [root_schema]. *)
Definition certificate_payload_schema :=
  Packed.pair (Packed.array inequality_schema)
    (Packed.pair (big_array item_schema)
      (Packed.pair simplex_graph_schema
        (Packed.pair geom_schema
          (Packed.pair full_dim_schema root_schema)))).

Definition certificate_wire_schema :=
  Packed.pair Packed.int63
    (Packed.pair Packed.int63 certificate_payload_schema).
