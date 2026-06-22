From mathcomp Require Import finmap all_ssreflect all_algebra.
From Polyhedra Require Import polyhedron row_submx poly_base affine.

Section Arithmetics.

Definition even (n : nat) := ~~ (odd n).

End Arithmetics.

Section RelaxationTheorem.

Context (m : nat).

Definition simplicialComplex := {set {set 'I_m}}.

Definition isClosedBySubsets (K : simplicialComplex) :=
    forall (F G : {set 'I_m}), (F \in K) -> (G \subset F) -> (G \in K).

Record asc := {
    simplices : simplicialComplex;
    isAsc : isClosedBySubsets simplices
}.

Definition simplex := {set 'I_m}.

Definition dim (F : simplex) := #|F|.

Definition isMaximal (K: asc) (F : simplex) : Prop :=
    (F \in simplices K) /\
    (forall G : simplex, (G \in simplices K) -> (F \subset G) -> (F = G)).

(* Since natural numbers do not include -1, all dimensions are shifted by an offset of 1. *)
Definition isDPure (d : nat) (K : asc) : Prop :=
    forall F : simplex, isMaximal K F -> dim F = d.+1.

Context (p : nat).
Local Notation d := p.+1.

(* Because of the previous convention, a facet is a d+1 simplex. *)
Definition isFacet (sig : simplex) :=
    dim sig == d.+1.

Definition isFacetP (sig : simplex) :=
    dim sig = d.+1.

(* Because of the previous convention, a ridge is a d simplex. *)
Definition isRidge (sig : simplex) :=
    dim sig == d.

Definition isRidgeP (sig : simplex) :=
    dim sig = d.

Definition allRidgesHaveEvenIncidence (K : asc) :=
    forall tau : simplex, tau \in (simplices K) -> isRidge tau -> 
    even #|[set F : simplex | [&& isFacet F, F \in (simplices K) & tau \subset F]]|.

Context (R : realFieldType) (normals : 'I_m -> 'cV[R]_d).

Definition coneOfSimplex (K : asc) (sig : simplex) :=
    cone [fset (normals i) | i : 'I_m & i \in sig]%fset.

Definition areFacetsPointed (K : asc) :=
    forall sig : simplex, sig \in (simplices K) -> isFacet sig ->
    pointed (coneOfSimplex K sig).

Local Notation "\pdim P" := (adim (hull P)).

Notation "[ 'forallf' x 'in' A , P ]" :=
  (all (fun x => P) (enum_fset A))
  (at level 0, x ident, A at level 99, P at level 99).

Definition isInInt (P : 'poly_d) (z : 'cV[R]_d) :=
    (z \in P) && [forallf F in face_set P, ~~(\pdim F < d) || ~~(z \in F)].

Definition existsSpecialPoint (K : asc) :=
    exists z : 'cV[R]_d, odd #|[set F : simplex | [&& isFacet F, F \in simplices K, 
    ~~(z \in (coneOfSimplex K F)) & isInInt (coneOfSimplex K F) z]]|.

Definition conesCoverSpace (K : asc) :=
    forall x : 'cV[R]_d, exists sig : simplex, (sig \in simplices K) -> (isFacet sig)
    -> (x \in coneOfSimplex K sig).

Theorem relaxationTheorem (K : asc) :
    (isDPure d K) -> (allRidgesHaveEvenIncidence K) -> (areFacetsPointed K) -> (existsSpecialPoint K)
    -> (conesCoverSpace K).
Admitted.

End RelaxationTheorem.






