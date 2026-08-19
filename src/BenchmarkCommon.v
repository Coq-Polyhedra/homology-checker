From Coq Require Import PArray Uint63.
From Bignums Require Import BigN BigZ.
From BinReader Require Import BinReader.

Open Scope array_scope.
Open Scope uint63_scope.

(** Exact pre-flatten wire schema used by the August 2026 measurements.
    Each vertex owns its pair of flag arrays.  The older eight-phase checker
    decodes these arrays but does not inspect them. *)
Definition int_array_schema :=
  Packed.array Packed.int63.

Definition int_matrix_schema :=
  Packed.array int_array_schema.

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

Definition simplex_graph_schema :=
  Packed.pair int_matrix_schema (Packed.array facet_schema).

Definition geom_schema :=
  Packed.pair int_matrix_schema
    (Packed.pair int_matrix_schema int_matrix_schema).

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

Definition certificate_payload_schema :=
  Packed.pair (Packed.array inequality_schema)
    (Packed.pair (Packed.array item_schema)
      (Packed.pair simplex_graph_schema
        (Packed.pair geom_schema
          (Packed.pair full_dim_schema root_schema)))).

Definition certificate_wire_schema :=
  Packed.pair Packed.int63
    (Packed.pair Packed.int63 certificate_payload_schema).
