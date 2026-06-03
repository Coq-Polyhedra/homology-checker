From Coq Require Import Uint63 BinNat.
From mathcomp Require Import all_ssreflect.
From Bignums Require Import BigQ.
From BinReader Require Import BinReader.
Require Import PArray.
Import Order.Theory.

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

Definition fold_pair {T1 T2 A : Type} (f : T1 -> T2 -> A -> A) (a1 : array T1) (a2 : array T2) (x0 : A) :=
  ifold (fun i s=> f a1.[i] a2.[i] s) (if (length a1 <? length a2)%uint63 then length a1 else length a2) x0.

(* iterate of the elements of universe
 * apply f_in to elements of universe \ s and f_notin otherwise *)
Definition iter_in_notin {T1 T2 : Type} (f_in f_notin : int -> T1 -> T1) (lt_T2 : rel T2) (universe s : array T2) (x : T1) :=
  let res := ifold (fun i acc => 
    if ((acc.2 <? length s)%uint63 && (lt_T2 universe.[i] s.[acc.2])%uint63) then 
      (f_notin i acc.1, acc.2) 
      else (f_in i acc.1, (acc.2+1)%uint63)
    ) (length universe) (x, 0%uint63) in
    res.1.

(* TODO : change this as soon as we can create a universe equal to [|0; 1; ...; m-1|] *)
Definition iter_in_not_in_int {T : Type} (f_in f_notin : int -> T -> T) (s : array int) (m : int) (x : T) :=
  let res := ifold (fun i acc => 
    if ((acc.2 <? length s)%uint63 ==> (i <? s.[acc.2])%uint63) then 
      (f_notin i acc.1, acc.2) 
      else (f_in i acc.1, (acc.2+1)%uint63)
    ) m (x, 0%uint63) in
    res.1.

Definition array_dot {T : Type} (addf mulf: T -> T -> T) (x0 : T)
  (a b : array T):=
  fold_pair (fun x y res=> addf res (mulf x y)) a b x0.

Definition bigQ_dot (x y : array bigQ) : bigQ :=
  array_dot BigQ.add BigQ.mul 0%bigQ x y.

Definition BigQ_ltb (x y : bigQ) :=
  match BigQ.compare x y with
  | Lt => true
  | _  => false
  end.

Notation "x <?bq y" := (BigQ_ltb x y)
  (at level 70).

Notation "x <=?bq y" := (~~ (BigQ_ltb y x))
  (at level 70).

Notation "x =?bq y" := (BigQ.eq_bool x y)
  (at level 70).
 
Definition check_ineqs (ineqs : array (array bigQ * bigQ)) (x : array bigQ) (saturated : array int) :=
  iter_in_not_in_int 
    (fun i acc => (acc && (bigQ_dot ineqs.[i].1 x =?bq ineqs.[i].2))) 
    (fun i acc => (acc && (bigQ_dot ineqs.[i].1 x <?bq ineqs.[i].2))) 
    saturated (length ineqs) true.

Record Certificate := {
  ineqs
     : array (array bigQ * bigQ);
  vert
     : array (array bigQ * (array int * array (array int * int)));
  graph
     : array (array int);
  lbl
     : array (array int * (int * int));
  root
     : int * (array int * (array (array bigQ) * array int))
}.

Definition build_cert cert := 
  let ineqs := fst cert in 
  let vert := fst (snd cert) in
  let graph := fst (fst (snd (snd cert))) in 
  let lbl := snd (fst (snd (snd cert))) in
  let root := snd (snd (snd cert)) in
  {| ineqs := ineqs; vert := vert; graph := graph; lbl := lbl; root := root |}.

Definition feasibility_check (cert : Certificate) := 
  let ineqs := cert.(ineqs) in
  let vertices := cert.(vert) in
  ifold (fun i acc => acc && check_ineqs ineqs vertices.[i].1 vertices.[i].2.1) 
    (length vertices) true.

LoadData "../lrs-postprocess/data/poly20dim21-cert.bin" As cert.

Section Benchmark.

Let cert := build_cert cert.
Time Eval vm_compute in 
  (check_ineqs cert.(ineqs) (cert.(vert).[0].1) (cert.(vert).[0].2.1)) 
  && (check_ineqs cert.(ineqs) (cert.(vert).[1].1) (cert.(vert).[1].2.1))
  && (check_ineqs cert.(ineqs) (cert.(vert).[2].1) (cert.(vert).[2].2.1))
  && (check_ineqs cert.(ineqs) (cert.(vert).[3].1) (cert.(vert).[3].2.1))
  && (check_ineqs cert.(ineqs) (cert.(vert).[4].1) (cert.(vert).[4].2.1))
  && (check_ineqs cert.(ineqs) (cert.(vert).[5].1) (cert.(vert).[5].2.1))
  && (check_ineqs cert.(ineqs) (cert.(vert).[6].1) (cert.(vert).[6].2.1))
  && (check_ineqs cert.(ineqs) (cert.(vert).[7].1) (cert.(vert).[7].2.1))
  && (check_ineqs cert.(ineqs) (cert.(vert).[8].1) (cert.(vert).[8].2.1))
  && (check_ineqs cert.(ineqs) (cert.(vert).[9].1) (cert.(vert).[9].2.1))
  && (check_ineqs cert.(ineqs) (cert.(vert).[10].1) (cert.(vert).[10].2.1))
  && (check_ineqs cert.(ineqs) (cert.(vert).[11].1) (cert.(vert).[11].2.1))
  && (check_ineqs cert.(ineqs) (cert.(vert).[12].1) (cert.(vert).[12].2.1))
  && (check_ineqs cert.(ineqs) (cert.(vert).[13].1) (cert.(vert).[13].2.1))
  && (check_ineqs cert.(ineqs) (cert.(vert).[14].1) (cert.(vert).[14].2.1))
  && (check_ineqs cert.(ineqs) (cert.(vert).[15].1) (cert.(vert).[15].2.1))
  && (check_ineqs cert.(ineqs) (cert.(vert).[16].1) (cert.(vert).[16].2.1))
  && (check_ineqs cert.(ineqs) (cert.(vert).[17].1) (cert.(vert).[17].2.1))
  && (check_ineqs cert.(ineqs) (cert.(vert).[18].1) (cert.(vert).[18].2.1)) 
  && (check_ineqs cert.(ineqs) (cert.(vert).[19].1) (cert.(vert).[19].2.1)).

End Benchmark.
(*
Definition index : array int := make 1 0%uint63.
Definition a0 : array (array bigQ) := (make 2 (make 2 1%bigQ)).
Definition a := a0.[1 <- a0.[1].[1 <- 2%bigQ]].
Definition b0 : array bigQ := make 2 2%bigQ.
Definition b := b0.[1 <- 2%bigQ].
Definition x : array bigQ := make 2 1%bigQ.

Definition a1 : array (array bigQ) := (make 5 (make 5 0%bigQ)).
Definition b1 : array bigQ := make 5 0%bigQ.
Definition index1 : array int := (make 5 0%uint63).[1 <- 1%uint63].[2 <- 2%uint63].[3 <- 3%uint63].[4 <- 4%uint63].

Eval compute in Check_ineq index a x b.
Eval compute in Check_ineq index1 a1 x b1.
*)




