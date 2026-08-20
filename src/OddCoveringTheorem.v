From mathcomp Require Import finmap all_ssreflect all_algebra.
Import GRing.Theory Num.Theory Order.Theory.
From Polyhedra Require Import hpolyhedron row_submx inner_product polyhedron poly_base affine vector_order barycenter lrel.
From DepotThese Require Import high_graph.
Import HPolyhedron.
Open Scope polyh_scope.

Section Arithmetics.

Definition even (n : nat) := ~~ (odd n).

End Arithmetics.


Section AbstractSimplicialComplex.

Definition simplex (T : finType):= {set T}.
Definition simplicialComplex (T : finType) := {set simplex T}.

Definition isAsc {T : finType} (K : simplicialComplex T) :=
  forall (F G : simplex T), (F \in K) -> (G \subset F) -> (G \in K).

Lemma empty_set_is_asc {T : finType} : @isAsc T set0.
Proof.
  move=> F G HF _.
  by rewrite inE in HF.
Qed.

Definition set_to_asc {T : finType} (J : {set simplex T}) :=
  [set G : simplex T | [exists F : simplex T, (F \in J) && (G \subset F)]].

Lemma in_set_to_ascE {T : finType} (J : {set simplex T}) (G : simplex T) :
  G \in set_to_asc J = [exists F : simplex T, (F \in J) && (G \subset F)].
Proof. by rewrite inE. Qed.

Lemma in_set_to_ascP {T : finType} (J : {set simplex T}) (G : simplex T) :
  reflect (exists F : simplex T, F \in J /\ G \subset F) (G \in set_to_asc J).
Proof.
  rewrite in_set_to_ascE.
  apply: (iffP existsP).
  - move=> [F /andP HF].
    by exists F.
  - move=> [F HF].
    by exists F; apply/andP.
Qed.

Lemma set_to_asc_set0 {T : finType} :
  @set_to_asc T set0 = set0.
Proof.
  apply/setP => x.
  rewrite in_set0.
  apply/in_set_to_ascP.
  move=> [F [HF _]].
  by rewrite in_set0 in HF.
Qed.

Lemma set_to_asc_subset {T : finType} (J : {set simplex T}) :
  {subset J <= set_to_asc J}.
Proof.
  move=> F HF; apply/in_set_to_ascP.
  by exists F.
Qed.

Lemma set_to_asc_closed {T : finType} (J : {set simplex T}) (F : simplex T):
  F \in set_to_asc J -> forall G : simplex T, G \subset F -> G \in set_to_asc J.
Proof.
  move=> /in_set_to_ascP [F0 [HF0J HFF0]] G HGF.
  apply/in_set_to_ascP.
  by exists F0; split=> //; exact: subset_trans HGF HFF0.
Qed.

Lemma set_to_asc_is_asc {T : finType} (J : {set simplex T}) :
  isAsc (set_to_asc J).
Proof.
  move=> F G HF HGF.
  exact: set_to_asc_closed J F HF G HGF.
Qed.

End AbstractSimplicialComplex.


Section Dimension.

Definition sdim {T : finType} (F : simplex T) := #|F|.

Lemma sdimS {T : finType} : 
  {homo (@sdim T) : F G / F \subset G >-> F <= G}.
Proof.
  by move=> F G HFG; apply: subset_leq_card.
Qed.

Definition dim {T : finType} (K : simplicialComplex T) := 
  \max_(F in K) sdim F.

Lemma dim_empty_set_eq0 {T : finType} : @dim T set0 = 0.
Proof.
  rewrite/dim. 
  apply: big_pred0 => x.
  by rewrite inE.
Qed.

Lemma dim_is_geq {T : finType} (K : simplicialComplex T) :
  forall F : simplex T, F \in K -> dim K >= sdim F.
Proof.
  move=> F HFK. by rewrite/dim; exact: leq_bigmax_cond HFK.
Qed.

Lemma dim_argmax {T : finType} (K : simplicialComplex T) (F : simplex T):
  (forall G : simplex T, G \in K -> sdim G <= sdim F) -> F \in K -> sdim F = dim K.
Proof.
  move=> Hmax HFK.
  apply/eqP; rewrite eqn_leq; apply/andP; split=> //.
  - exact: dim_is_geq HFK.
  - by apply/bigmax_leqP.
Qed.

Lemma dim_exists {T : finType} (K : simplicialComplex T) :
  reflect (exists F, F \in K /\ sdim F = dim K) (K != set0).
Proof.
  apply: (iffP idP).
  - move/set0Pn => [F0 HF0K].
    have [F HFK Hmax] := arg_maxnP sdim HF0K.
    exists F. 
    split=> //; exact (dim_argmax K F Hmax HFK).
  - move=> H. case: H=> F [HF _]. by apply/set0Pn; exists F.
Qed.

Definition isDRegular {T : finType} (d : nat) (J : {set simplex T}) :=
  J != set0 /\ forall F : simplex T, F \in J -> sdim F = d.

Lemma dim_regular_set {T : finType} (d : nat) (J : {set simplex T}) :
  isDRegular d J -> dim (set_to_asc J) = d.
Proof.
  move=> [/set0Pn [F HFJ] Hreg].
  apply/eqP; rewrite eqn_leq; apply/andP; split.
  - apply/bigmax_leqP=> G /in_set_to_ascP [F0 [HF0J HGF0]].
    rewrite -(Hreg F0 HF0J).
    exact: sdimS HGF0.
  - rewrite -(Hreg F HFJ).
    exact: dim_is_geq F (set_to_asc_subset J F HFJ).
Qed.

End Dimension.


Section Facets.

Definition facetsOf {T : finType} (K : simplicialComplex T) :=
  [set F : simplex T | (F \in K) && (sdim F == dim K)].

Lemma in_facetsOfE {T : finType} (K : simplicialComplex T) (F : simplex T) :
  F \in facetsOf K = (F \in K) && (sdim F == dim K).
Proof. by rewrite inE. Qed.

Lemma in_facetsOfP {T : finType} (K : simplicialComplex T) (F : simplex T) :
  reflect (F \in K /\ sdim F = dim K) (F \in facetsOf K).
Proof.
  rewrite in_facetsOfE.
  apply: (iffP andP).
  - by move=> [HFK /eqP Hdim]; split.
  - by move=> [HFK /eqP Hdim]; split.
Qed.

Lemma facetsOf_set0 {T : finType} :
  @facetsOf T set0 = set0.
Proof.
  apply/setP => x.
  rewrite in_set0.
  apply/in_facetsOfP.
  move=> [Hx _].
  by rewrite in_set0 in Hx.
Qed.

Lemma facetsOf_subset {T : finType} (K : simplicialComplex T) :
  {subset facetsOf K <= K}.
Proof.
  move=> F /in_facetsOfP HF.
  by case: HF => HF _.
Qed.

Lemma facets_of_set_subset {T : finType} (J : {set simplex T}):
  {subset facetsOf (set_to_asc J) <= J}.
Proof.
  move=> F /in_facetsOfP [HFasc HFdim].
  move/in_set_to_ascP: HFasc => [F0 [HF0J HFF0]].
  have Hcard : sdim F = sdim F0.
  - apply/eqP; rewrite eqn_leq; apply/andP; split.
    - exact: sdimS HFF0.
    - rewrite HFdim. 
      exact: dim_is_geq (set_to_asc_subset J F0 HF0J).
  have /setP Heq := subset_cardP Hcard HFF0. 
  by rewrite Heq.
Qed.
   
Lemma facets_of_set {T : finType} (J : {set simplex T}) :
  (exists d, isDRegular d J) -> facetsOf (set_to_asc J) = J.
Proof.
  move=> [d Hdreg].
  apply/setP=> F.
  apply/idP/idP.
  - by apply: facets_of_set_subset F.
  - move=> HF. apply/in_facetsOfP. split=> //.
    - exact: set_to_asc_subset J F HF.
    - rewrite (dim_regular_set d J Hdreg). case: Hdreg => _ Hreg.
      exact: Hreg F HF.
Qed.

Definition incident_facets {T : finType} (K : simplicialComplex T) (R : simplex T) :=
  [set F in facetsOf K | R \subset F].

Lemma in_incident_facetsE {T : finType} (K : simplicialComplex T) (R : simplex T) (F : simplex T) :
  F \in incident_facets K R = (F \in facetsOf K) && (R \subset F).
Proof. by rewrite inE. Qed.

Lemma in_incident_facetsP {T : finType} (K : simplicialComplex T) (R : simplex T) (F : simplex T) :
  reflect (F \in facetsOf K /\ R \subset F) (F \in incident_facets K R).
Proof.
  by rewrite in_incident_facetsE; apply: (iffP andP).
Qed.

Lemma incident_facets_subset {T : finType} (K : simplicialComplex T) (R : simplex T) :
  {subset incident_facets K R <= facetsOf K}.
Proof.
  move=> F /in_incident_facetsP HF.
  by case: HF => HF _.
Qed.

End Facets.


Section Ridges.

Definition ridgesOf {T : finType} (K : simplicialComplex T) :=
  [set R : simplex T | (R \in K) && (sdim R == (dim K).-1)].

Lemma in_ridgesOfE {T : finType} (K : simplicialComplex T) (R : simplex T) :
  R \in ridgesOf K = (R \in K) && (sdim R == (dim K).-1).
Proof. by rewrite inE. Qed.

Lemma in_ridgesOfP {T : finType} (K : simplicialComplex T) (R : simplex T) :
  reflect (R \in K /\ sdim R = (dim K).-1) (R \in ridgesOf K).
Proof.
  rewrite in_ridgesOfE.
  apply: (iffP andP).
  - by move=> [HFK /eqP Hdim]; split.
  - by move=> [HFK /eqP Hdim]; split.
Qed.

Lemma ridgesOf_subset {T : finType} (K : simplicialComplex T) :
  {subset ridgesOf K <= K}.
Proof.
  move=> F /in_ridgesOfP HF.
  by case: HF => HF _.
Qed.

End Ridges.


Section Cones.

Context (m d : nat) (R : realFieldType).

Variable (normals : 'I_m -> 'cV[R]_d).

Lemma coneS : {homo @cone R d : P Q / (P `<=` Q)%fset >-> P `<=` Q}.
Proof.
  move=> P Q /fsubsetP HPQ.
  apply/poly_leP. 
  move=> z /in_coneP [w HwP Hwz].
  apply/in_coneP. exists w.  
  move/fsubsetP: HwP => HwP.
  apply/fsubsetP=> x Hxw.
  exact: HPQ x (HwP x Hxw). by [].
Qed.

Definition normalsOf (F : {set 'I_m}) :=
  [fset (normals i) | i : 'I_m & i \in F]%fset.

Lemma in_normalsOfP (F : {set 'I_m}) (z : 'cV[R]_d) :
  reflect (exists i : 'I_m, i \in F /\ z = (normals i)) (z \in normalsOf F).
Proof.
  apply: (iffP idP).
  - by move/imfsetP=> [i HiF Hiz]; exists i.
  - move => [i [HiF Hiz]]. by apply/imfsetP; exists i.
Qed.

Lemma normalsOfS :
  {homo normalsOf : F G / F \subset G >-> (F `<=` G)%fset}.
Proof.
  move=> F G /subsetP HFG.
  apply/fsubsetP=> z /in_normalsOfP [i [HiF Hiz]].
  apply/in_normalsOfP.
  by exists i; split=> //; exact: HFG HiF.
Qed.

Definition coneOf (F : {set 'I_m}) :=
  cone (normalsOf F).

Lemma in_coneOfP (F : {set 'I_m}) (z : 'cV[R]_d) :
  reflect (exists w : {conic 'cV_d ~> R}, (finsupp w `<=` (normalsOf F))%fset /\ z = combine w)
  (z \in coneOf F).
Proof.
  rewrite/coneOf.
  apply: (iffP idP).
  - by move/in_coneP => [w HwF Hzw]; exists w.
  - move=> [w [HwF Hzw]]. by apply/in_coneP; exists w.
Qed.

Lemma coneOfS :
  {homo coneOf : F G / F \subset G >-> F `<=` G}.
Proof.
  move=> F G HFG. exact: coneS (normalsOf F) (normalsOf G) (normalsOfS F G HFG).
Qed.

End Cones.


Section Genericity.

Context (m d: nat) (R : realFieldType).

Notation simplex_m := (simplex [finType of 'I_m]).
Notation simplicialComplex_m := (simplicialComplex [finType of 'I_m]).

Variable (normals : 'I_m -> 'cV[R]_d) (K : simplicialComplex_m).

Local Notation coneOf := (coneOf m d R normals).

Definition isKGeneric (k : nat) (x : 'cV[R]_d) :=
  forall F : simplex_m, F \in K -> \pdim (coneOf F) < k -> (x \notin coneOf F).

Hypothesis Hasc : (isAsc K).
Hypothesis Hdim : (dim K = d).

End Genericity.


Section OddCoveringTheorem.

Context (m d: nat) (R : realFieldType).

Local Notation simplex_m := (simplex [finType of 'I_m]).
Local Notation simplicialComplex_m := (simplicialComplex [finType of 'I_m]).

Variable (normals : 'I_m -> 'cV[R]_d) (K : simplicialComplex_m).

Local Notation coneOf := (coneOf m d R normals).
Local Notation isKGeneric := (isKGeneric m d R normals K).

Definition normalsAreNonZero :=
  forall i : 'I_m, (normals i <> 0)%R.

Hypothesis Hasc : (isAsc K).
Hypothesis Hdim : (dim K = d).
Hypothesis Hnormals : normalsAreNonZero.

Definition ridgesHaveEvenIncidence :=
  forall R : simplex_m, R \in ridgesOf K -> even #|incident_facets K R|.

Definition conesArePointed :=
  forall F : simplex_m, F \in facetsOf K -> pointed (coneOf F).

Definition existsSpecialPoint :=
  exists z : 'cV[R]_d, isKGeneric d z /\ odd #|[set F in facetsOf K | z \in coneOf F]|.

Definition conesCoverSpace :=
    forall x : 'cV[R]_d, exists F : simplex_m, F \in facetsOf K /\ x \in coneOf F.

Theorem odd_covering_theorem :
  ridgesHaveEvenIncidence -> conesArePointed -> existsSpecialPoint -> conesCoverSpace.
Admitted.

End OddCoveringTheorem.