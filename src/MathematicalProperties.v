From mathcomp Require Import finmap all_ssreflect.

Section AbstractSimplicialComplexes.

Context (m : nat).

Definition simplicialComplex := {set {set 'I_m}}.

Definition isClosedBySubsets (K : simplicialComplex) :=
    forall (F G : {set 'I_m}), (F \in K) -> (G \subset F) -> (G \in K).

Record asc := {
    simplices : simplicialComplex;
    isAsc : isClosedBySubsets simplices
}.

(* To encode dimensions as nat rather than int, we adopt the convention that the empty 
simplex has dimension 0, vertices have dimension 1, and edges have dimension 2. *)

Definition simplex := {set 'I_m}.

Definition dimSimpl (F : simplex) := #|F| - 1.

Record vertex := {
    vertexValue : simplex;
    isVertex : (dimSimpl vertexValue) = 1
}.
Record edge := {
    edgeValue : simplex;
    isEdge : (dimSimpl edgeValue) = 2 
}.

Definition isMaximal (K: asc) (F : simplex) : Prop :=
    (F \in simplices K) /\
    (forall G : simplex, (G \in simplices K) -> ((dimSimpl G) <= (dimSimpl F))).

Definition isPure (K : asc) : Prop := 
    forall F G : simplex, (isMaximal K F) -> (isMaximal K G) -> (dimSimpl F = dimSimpl G).

(* Because of the previous convention, d-purity corresponds to having dimension d + 2. *)
Definition isDPure (K : asc) (d : nat) : Prop :=
    forall F : simplex, (isMaximal K F) -> dimSimpl F = d+2.

(*We define (d-1)-Pure Abstract Simplicial Complexes. *)
Record pasc (d : nat) := {
    complex : asc;
    isComplexDPure : isDPure complex (d-1)
}.

(* Because of the previous convention, a facet is a d+1 simplex. *)
Record facet (d : nat) := {
    facetValue : simplex;
    isFacet : dimSimpl (facetValue) = d+1
}.

(* Because of the previous convention, a ridge is a d simplex. *)
Record ridge (d : nat) := {
    ridgeValue : simplex;
    isRidge : dimSimpl (ridgeValue) = d
}.

Definition ridgeHasEvenIncidence (d : nat) (K : asc) (tau : ridge d) :=
    negb (odd #|[set F in simplices K | (dimSimpl F == d+1) && ((ridgeValue d) tau \subset F)]|).

Definition allRidgesHaveEvenIncidence (d : nat) (K : asc) :=
    forall tau : ridge d, ridgeHasEvenIncidence d K tau.

End AbstractSimplicialComplexes.



