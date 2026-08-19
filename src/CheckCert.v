From Ltac2 Require Import Printf.
From BinReader Require Import BinReader.
From Cert Require Import LowLevelChecker CertificateSchema.

Section BenchmarkPacked.
Ltac2 Eval printf "Packed version".

Definition check_packed_certificate cert :=
  match Packed.decode certificate_wire_schema cert with
  | Some cert => check_certificate (build_cert cert)
  | None => false
  end.

Ltac2 Eval printf "poly20dim21".
Time LoadDataPacked "../lrs-postprocess/data/poly20dim21-cert.bin" As packed_cert. 

(* Ltac2 Eval printf "poly23dim24". 
Time LoadDataPacked "../lrs-postprocess/data/poly23dim24-cert.bin" As packed_cert.  *)

(* Ltac2 Eval printf "cross8". 
Time LoadDataPacked "../lrs-postprocess/data/cross8-cert.bin" As packed_cert. *)

(* Ltac2 Eval printf "birkhoff3". *)
(* Time LoadDataPacked "../lrs-postprocess/data/birkhoff3-cert.bin" As packed_cert. *)

(* Ltac2 Eval printf "birkhoff6".
Time LoadDataPacked "../lrs-postprocess/data/birkhoff6-cert.bin" As packed_cert. *)

(* Ltac2 Eval printf "dual_cyclic_d13_n26". 
Time LoadDataPacked "../lrs-postprocess/data/dual_cyclic_d13_n26-cert.bin" As packed_cert. *)

(* Ltac2 Eval printf "dual_cyclic_d14_n28".
Time LoadDataPacked "../lrs-postprocess/data/dual_cyclic_d14_n28-cert.bin" As packed_cert. *)

(* Ltac2 Eval printf "permutohedron3". *)
(* Time LoadDataPacked "../lrs-postprocess/data/permutohedron3-cert.bin" As packed_cert. *)

(* Ltac2 Eval printf "permutohedron7".
Time LoadDataPacked "../lrs-postprocess/data/permutohedron7-cert.bin" As packed_cert. *)

(* Ltac2 Eval printf "permutohedron8".
Time LoadDataPacked "../lrs-postprocess/data/permutohedron8-cert.bin" As packed_cert. *)

(* Ltac2 Eval printf "hypersimplex15". 
Time LoadDataPacked "../lrs-postprocess/data/hypersimplex15-cert.bin" As packed_cert. *)

(* Ltac2 Eval printf "hypersimplex16". 
Time LoadDataPacked "../lrs-postprocess/data/hypersimplex16-cert.bin" As packed_cert.  *)

Time Eval vm_compute in check_packed_certificate packed_cert.

Time End BenchmarkPacked.

Section Benchmark.
Ltac2 Eval printf "Unpacked version".

Ltac2 Eval printf "poly20dim21".
Time LoadData "../lrs-postprocess/data/poly20dim21-cert.bin" As cert. 

(* Ltac2 Eval printf "poly23dim24".
Time LoadData "../lrs-postprocess/data/poly23dim24-cert.bin" As cert.  *)

(* Ltac2 Eval printf "cross8".
Time LoadData "../lrs-postprocess/data/cross8-cert.bin" As cert. *)

(* Ltac2 Eval printf "birkhoff3".
Time LoadData "../lrs-postprocess/data/birkhoff3-cert.bin" As cert. *)

(* Ltac2 Eval printf "birkhoff6".
Time LoadData "../lrs-postprocess/data/birkhoff6-cert.bin" As cert. *)

(* Ltac2 Eval printf "dual_cyclic_d13_n26". 
Time LoadData "../lrs-postprocess/data/dual_cyclic_d13_n26-cert.bin" As cert. *)

(* Ltac2 Eval printf "dual_cyclic_d14_n28".
Time LoadData "../lrs-postprocess/data/dual_cyclic_d14_n28-cert.bin" As cert. *)

(* Ltac2 Eval printf "permutohedron3". *)
(* Time LoadData "../lrs-postprocess/data/permutohedron3-cert.bin" As cert. *)

(* Ltac2 Eval printf "permutohedron7".
Time LoadData "../lrs-postprocess/data/permutohedron7-cert.bin" As cert. *)

(* Ltac2 Eval printf "permutohedron8".
Time LoadData "../lrs-postprocess/data/permutohedron8-cert.bin" As cert. *)

(* Ltac2 Eval printf "hypersimplex15". 
Time LoadData "../lrs-postprocess/data/hypersimplex15-cert.bin" As cert. *)

(* Ltac2 Eval printf "hypersimplex16". 
Time LoadData "../lrs-postprocess/data/hypersimplex16-cert.bin" As cert.  *)

Time Eval vm_compute in check_certificate (build_cert cert).

Time End Benchmark.
