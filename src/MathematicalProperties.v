From mathcomp Require Import finmap all_ssreflect all_algebra.
From Polyhedra Require Import polyhedron row_submx.

Section Arithmetics.

Definition even (n : nat) := negb (odd n).

End Arithmetics.

Section Matrix.

Definition rowsfSet_of_M (R : realFieldType) (m d : nat) (M : 'M[R]_(m,d)) :=
    seq_fset tt (map (fun i => trmx (row i M)) (enum 'I_m)).

End Matrix.

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

Definition dimSimpl (F : simplex) := #|F| - 1.

Definition isMaximal (K: asc) (F : simplex) : Prop :=
    (F \in simplices K) /\
    (forall G : simplex, (G \in simplices K) -> (F \subset G) -> (F = G)).

Definition isPure (K : asc) : Prop := 
    forall F G : simplex, (isMaximal K F) -> (isMaximal K G) -> (dimSimpl F = dimSimpl G).

(* Since natural numbers do not include -1, all dimensions are shifted by an offset of 1. *)
(* Faut-il l'existence d'un simplexe de dimension d+2 ? *)
Definition isDPure (K : asc) (d : nat) : Prop :=
    forall F : simplex, (isMaximal K F) -> dimSimpl F = d+2.

Context (d : nat).

(* Because of the previous convention, a facet is a d+1 simplex. *)
Record facet := {
    facetValue : simplex;
    isFacet : dimSimpl (facetValue) = d+1
}.

(* Because of the previous convention, a ridge is a d simplex. *)
Record ridge := {
    ridgeValue : simplex;
    isRidge : dimSimpl (ridgeValue) = d
}.

Definition ridgeHasEvenIncidence (K : asc) (tau : ridge) :=
    even (size (filter (fun F => (dimSimpl F == d+1) && (ridgeValue tau \subset F)) (enum (simplices K)))).

Definition allRidgesHaveEvenIncidence (K : asc) :=
    forall tau : ridge, ridgeHasEvenIncidence K tau.

Context (R : realFieldType) (vectors : 'M[R]_(m,d)).

Definition generatorsOfFacet (sig : facet) :=
    row_submx vectors (facetValue sig).

Definition coneOfFacet (sig : facet) :=
    cone (rowsfSet_of_M R (#|facetValue sig|) d (generatorsOfFacet sig)).

Definition isFacetPointed (sig : facet) :=
    pointed (coneOfFacet sig).

Definition areFacetsPointed (K : asc) :=
    forall sig : facet, (facetValue sig \in simplices K) -> (isFacetPointed sig).

End RelaxationTheorem.
