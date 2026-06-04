From Coq Require Import Uint63 BinNat.
From mathcomp Require Import all_ssreflect.
From Bignums Require Import BigQ.
From BinReader Require Import BinReader.
Require Import PArray.
Import Order.Theory.

Section Uint63.

Fixpoint ifold_ {T : Type} (n : nat) (f : int -> T -> T) (i M : int) (x : T) :=
  if (i =? M)%uint63 then (i, x) else
    if n is n.+1 then
      let: (i, x) := ((i + 1)%uint63, f i x) in
      let: (i, x) := ifold_ n f i M x in
      let: (i, x) := ifold_ n f i M x in
      (i, x)
    else (i, x).

Definition ifold {T : Type} (f : int -> T -> T) (i : int) (x : T) :=
  (ifold_ Uint63.size f 0 i x).2.

End Uint63.

Section Array.

Definition fold {T A : Type} (f : T -> A -> A) (a : array T) (x0 : A) :=
  ifold (fun i acc => f a.[i] acc) (length a) x0.

Definition foldi {T A : Type} (f : int -> T -> A -> A) (a : array T) (x0 : A) :=
  ifold (fun i acc => f i a.[i] acc) (length a) x0.

Definition fold2 {T1 T2 A : Type} (f : T1 -> T2 -> A -> A) (a1 : array T1) (a2 : array T2) (x0 : A) :=
  ifold (fun i acc => f a1.[i] a2.[i] acc) (if (length a1 <? length a2)%uint63 then length a1 else length a2) x0.

Definition fold_alt {T A : Type} (f_in f_notin : T -> A -> A) (s : array T) (notin : array int) (x : A) :=
  let res := foldi (fun i x acc =>
    if (acc.2 <? length notin)%uint63 ==> (i <? notin.[acc.2])%uint63 then 
      (f_notin x acc.1, acc.2) 
      else (f_in x acc.1, (acc.2+1)%uint63)
    ) s (x, 0%uint63) in
    res.1.

Definition for_alli {T : Type} (f : int -> T -> bool) (a : array T) :=
  foldi (fun i x acc => acc && f i x) a true.

Definition for_all {T : Type} (f : T -> bool) (a : array T) :=
  fold (fun x acc => acc && f x) a true.

Definition for_all_alt {T : Type} (f_in f_notin : T -> bool) (s : array T) (notin : array int) :=
  fold_alt (fun x acc => f_in x && acc) (fun x acc => f_notin x && acc) s notin true.

Definition existi {T : Type} (f : int -> T -> bool) (a : array T) :=
  foldi (fun i x acc => acc || f i x) a false.

Definition exist {T : Type} (f : T -> bool) (a : array T) :=
  fold (fun x acc => acc || f x) a false.

Definition mem {T : Type} (eqT : T -> T -> bool) (x : T) (a : array T) : bool :=
  exist (fun y => eqT x y) a.

Definition mem_sorted {T : Type} (ltT eqT : T -> T -> bool) (x : T) (a : array T) : bool :=
  fold (fun y acc => if (ltT y x) then acc else if (eqT y x) then true else false) a false.

End Array.

Definition array_bigZ_dot (x y : array bigZ) : bigZ :=
  fold2 (fun x y res=> BigZ.add res (BigZ.mul x y)) x y 0%bigZ.

Definition check_ineqs (ineqs : array (array bigZ * bigZ)) (x : array bigZ * bigN) (saturated : array int) :=
  for_all_alt 
    (fun ineq => (array_bigZ_dot ineq.1 x.1 =? BigZ.mul ineq.2 (BigZ.Pos x.2))%bigZ)
    (fun ineq => (array_bigZ_dot ineq.1 x.1 <? BigZ.mul ineq.2 (BigZ.Pos x.2))%bigZ)
    ineqs saturated.

Record Certificate := {
  ineqs : array (array bigZ * bigZ);
  vert : array (array bigZ * bigN * (array int * array (array int * int)));
  graph : array (array int);
  lbl : array (array int * (int * int));
  root : int * (array int * (array (array bigQ) * array int))
}.

Definition build_cert cert := 
  let ineqs := cert.1 in 
  let vert := cert.2.1 in
  let graph := cert.2.2.1.1 in
  let lbl := cert.2.2.1.2 in
  let root := cert.2.2.2 in
  {| ineqs := ineqs; vert := vert; graph := graph; lbl := lbl; root := root |}.

Definition feasibility_check (cert : Certificate) := 
  let ineqs := cert.(ineqs) in
  let vertices := cert.(vert) in
  ifold (fun i acc => acc && check_ineqs ineqs vertices.[i].1 vertices.[i].2.1) 
    (length vertices) true.

Time LoadData "../lrs-postprocess/data/poly23dim24-cert.bin" As cert.

Section Benchmark.

Let cert := build_cert cert.
Time Eval vm_compute in 
  feasibility_check cert.

End Benchmark.
