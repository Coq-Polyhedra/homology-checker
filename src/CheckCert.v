(* From mathcomp Require Import all_ssreflect. *)
From Ltac2 Require Import Printf.
From BinReader Require Import BinReader.
From Cert Require Import LowLevelChecker.

Section Benchmark.

Ltac2 Eval printf "poly20dim21".
Time LoadData "../lrs-postprocess/data/poly20dim21-cert.bin" As cert.

(* Ltac2 Eval printf "poly23dim24".
Time LoadData "../lrs-postprocess/data/poly23dim24-cert.bin" As cert. *) 

(* Time LoadData "../lrs-postprocess/data/cross8-cert.bin" As cert. *)
(* Time LoadData "../lrs-postprocess/data/birkhoff3-cert.bin" As cert. *)
(* Time LoadData "../lrs-postprocess/data/birkhoff6-cert.bin" As cert. *)
(* Time LoadData "../lrs-postprocess/data/dual_cyclic_d13_n26-cert.bin" As cert. *)
(* Time LoadData "../lrs-postprocess/data/dual_cyclic_d14_n28-cert.bin" As cert. *)
(* Time LoadData "../lrs-postprocess/data/permutohedron3-cert.bin" As cert. *)
(* Time LoadData "../lrs-postprocess/data/permutohedron7-cert.bin" As cert. *)
(* Time LoadData "../lrs-postprocess/data/permutohedron8-cert.bin" As cert. *)
(* Time LoadData "../lrs-postprocess/data/hypersimplex15-cert.bin" As cert. *)
(* Time LoadData "../lrs-postprocess/data/hypersimplex16-cert.bin" As cert.  *)

(* Time Eval vm_compute in check_certificate cert. *)

Let built_cert := build_cert cert.

Theorem check_cert : check_certificate built_cert = true.
Proof.
vm_cast_no_check (eq_refl true).
Time Qed.


(* Time Eval vm_compute in 
  check_certificate cert. *)

(* Ltac2 Eval printf "".
Ltac2 Eval printf "Well-formedness check".
Time Eval vm_compute in 
  well_formedness_check cert.

Ltac2 Eval printf "".
Ltac2 Eval printf "Uniqueness check".
Time Eval vm_compute in 
  uniqueness_check cert.

Ltac2 Eval printf "".
Ltac2 Eval printf "Feasibility check".
Time Eval vm_compute in 
  feasibility_check cert.

Ltac2 Eval printf "".
Ltac2 Eval printf "Graph check".
Time Eval vm_compute in
  graph_check cert.

Ltac2 Eval printf "".
Ltac2 Eval printf "Mapping check".
Time Eval vm_compute in
  mapping_check cert.

Ltac2 Eval printf "".
Ltac2 Eval printf "Root check".
Time Eval vm_compute in
  root_check cert.

(* Ltac2 Eval printf "".
Ltac2 Eval printf "Vertex check (local edge test)".
Time Eval vm_compute in
  vertex_check cert. *)

Ltac2 Eval printf "".
Ltac2 Eval printf "Vertex check (flag test)".
Time Eval vm_compute in
  flag_check cert.

Ltac2 Eval printf "".
Ltac2 Eval printf "Graph image check".
Time Eval vm_compute in
  graph_image_check cert.

Ltac2 Eval printf "".
Ltac2 Eval printf "Full dimension check".
Time Eval vm_compute in
  full_dim_check cert. *)

Time End Benchmark.