From mathcomp Require Import finmap all_ssreflect all_algebra.
From Polyhedra Require Import polyhedron row_submx poly_base affine.

Section Arithmetics.

Definition even (n : nat) := ~~ (odd n).

End Arithmetics.

Section RelaxationTheorem.

Context (m : nat).

Definition isClosedBySubsets (K : {set {set 'I_m}}) :=
    forall (F G : {set 'I_m}), (F \in K) -> (G \subset F) -> (G \in K).

Definition simplicialComplex := {set {set 'I_m}}.

Record asc := {
    simplices : simplicialComplex;
    isAsc : isClosedBySubsets simplices
}.

Definition build_asc (K : simplicialComplex) (HK : isClosedBySubsets K) : asc :=
    {| simplices := K; isAsc := HK|}.

Definition simplex := {set 'I_m}.

Definition dim (F : simplex) := #|F|.

Definition isMaximal (K: asc) (F : simplex) :=
    (F \in simplices K) &&
    [forall G : simplex, (G \in simplices K) ==> (F \subset G) ==> (F == G)].

(* Since natural numbers do not include -1, all dimensions are shifted by an offset of 1. *)
Definition isDPure (d : nat) (K : asc) : Prop :=
    forall F : simplex, isMaximal K F -> dim F = d.+1.

Context (d : nat).

(* Because of the previous convention, a facet is a d+1 simplex. *)
Definition isFacet (sig : simplex) :=
    dim sig == d.+1.

(* Because of the previous convention, a ridge is a d simplex. *)
Definition isRidge (sig : simplex) :=
    dim sig == d.

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

Section DPurity.

Context (m : nat).

Definition powerSet (A : {set 'I_m}) :=
    [set X : {set 'I_m} | X \subset A]. 

Definition map_cup {A B : finType} (X : {set A}) (f : A -> {set B}) :=
    [set y : B | [exists x : A, (x \in X) && (y \in (f x))]].

Definition unionPS (X : {set {set 'I_m}}) := (map_cup X powerSet).

Lemma unionPS_is_asc : forall J : {set {set 'I_m}}, isClosedBySubsets m (unionPS J).
    unfold unionPS. intro. unfold isClosedBySubsets. intro. intro.
    unfold map_cup. rewrite inE. rewrite inE. intros.
    move/existsP in H. apply/existsP. destruct H.
    exists x. apply/andP. split. move/andP in H. destruct H.
    exact H. move/andP in H. destruct H. unfold powerSet in H1. rewrite inE in H1.
    unfold powerSet. rewrite inE. apply: (@subset_trans _ G F x).
    exact H0. exact H1.
Qed.

Definition set_to_asc (J : simplicialComplex m) := build_asc m (unionPS J) (unionPS_is_asc J).

Context (d : nat).

Lemma maximal_simplices_are_at_the_top : forall J : simplicialComplex m, 
forall F : simplex m, (isMaximal m (set_to_asc J) F) -> (F \in J).
Proof.
    intros. unfold isMaximal in H. move/andP in H. destruct H. 
    move/forallP in H0. unfold set_to_asc in H. simpl in H. unfold unionPS in H.
    unfold map_cup in H. rewrite inE in H. move/existsP in H. destruct H.
    move/andP in H. destruct H. have H2 := H0 x. unfold set_to_asc in H2.
    simpl in H2. unfold unionPS in H2. unfold map_cup in H2.
    rewrite inE in H2. move/implyP in H2. have H3 : (F \subset x) ==> (F == x).
    apply H2. apply/existsP. exists x. apply/andP. split. exact H.
    unfold powerSet. rewrite inE. trivial.
    have H4 : F = x. apply/eqP. move/implyP in H3. apply H3.
    unfold powerSet in H1. rewrite inE in H1. exact H1.
    rewrite H4. exact H.
Qed.

Definition isDRegular (K : simplicialComplex m) := forall F : simplex m, 
(F \in K) -> (isFacet m d F).

Lemma is_d_pure (K : simplicialComplex m) : isDRegular K -> isDPure m d (set_to_asc K).
Proof.
    intro. unfold isDPure. intros. have H1 : F \in K. apply maximal_simplices_are_at_the_top.
    exact H0. unfold isDRegular in H. have H2 := H F. have H3 : isFacet m d F.
    apply H2. exact H1. unfold isFacet in H3. apply/eqP. exact H3.
Qed.

End DPurity.


