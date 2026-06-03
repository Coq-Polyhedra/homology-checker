From Coq Require Import Uint63 BinNat.
From mathcomp Require Import all_ssreflect.
From Bignums Require Import BigQ.
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

Notation "x =?bq y" := (BigQ.eq_bool x y)
  (at level 70).
 
  
Definition Check_ineq_aux (index : array int) (a : array (array bigQ)) (x b : array bigQ) :=
    fold_pair (fun a1 b1 s => let: (c,i,k) := s
                              in let c := if (k =? index.[i])%uint63 
                                       then ((bigQ_dot a1 x =?bq b1) && c) 
                                       else ((bigQ_dot a1 x) <?bq b1) && c
                              in let i := if (k <? index.[i])%uint63 
                                       then i 
                                       else if ((i+1)%uint63 <? length index - 1)%uint63 then (i+1)%uint63 else (length index - 1)%uint63
                              in let k := (k + 1)%uint63
                              in (c,i,k)) a b (true, 0%uint63, 0%uint63).

Definition Check_ineq (index : array int) (a : array (array bigQ)) (x b : array bigQ) :=
    let: (c,i,k) := 

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





