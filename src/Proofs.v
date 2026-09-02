From mathcomp Require Import finmap all_ssreflect all_algebra.
Import GRing.Theory Num.Theory Order.Theory.
From Polyhedra Require Import hpolyhedron row_submx inner_product polyhedron poly_base affine vector_order barycenter lrel.
From DepotThese Require Import high_graph.
Import HPolyhedron.

Open Scope polyh_scope.

Notation "[ 'forallf' x 'in' A , P ]" :=
  (all (fun x => P) (enum_fset A))
  (at level 0, x ident, A at level 99, P at level 99).

Lemma forallfP (T : choiceType) (A : {fset T}) (p : pred T) :
  reflect (forall x, x \in A -> p x) ([forallf x in A, p x]).
Proof.
  apply: (iffP allP).  
  - move=> H x xA.
    exact: H xA.
  - move=> H x xA.
    exact: H xA.
Qed.

Section Arithmetics.

Definition even (n : nat) := ~~ (odd n).

End Arithmetics.

Section HPolyBase.

Context (d : nat) (R : realFieldType).

Definition base_hpoly (hp : 'hpoly[R]_d) : base_t[R,d] :=
  [fset BaseElt (trmx (row i hp.`A), hp.`b i ord0) | i : 'I_(hp.`c)]%fset.

Lemma base_hpolyP (hP : 'hpoly[R]_d) : '[hP] = 'P(base_hpoly hP)%PH.
Proof.
    apply/poly_eqP => x. apply/idP/idP.
    - intro HxInHP. rewrite/base_hpoly. rewrite in_poly_of_base.
    apply/forallP. intro x0. rewrite polyhedron.in_hs.
    have Hx0 := valP x0. move/imfsetP in Hx0. case:Hx0 => i Hi Hx0.
    simpl in Hi. rewrite Hx0. simpl. rewrite mem_mk_poly in HxInHP.
    rewrite in_hpolyE in HxInHP. rewrite/lev in HxInHP.
    move/forallP in HxInHP. have HxInHPi := HxInHP i.
    rewrite row_vdot. exact HxInHPi.
    - intro HxInPb. rewrite/base_hpoly in HxInPb. rewrite in_poly_of_base 
    in HxInPb. move/forallP in HxInPb. rewrite mem_mk_poly. rewrite in_hpolyE.
    rewrite/lev. apply/forallP. intro i. 
    have Hi : [< ((row i hP.`A)^T)%R, hP.`b i ord0 >] \in [fset [< ((row j hP.`A)^T)%R, 
    hP.`b j ord0 >] | j in 'I_hP.`c].
    apply/imfsetP. exists i. simpl. rewrite inE. trivial. reflexivity.
    have Hhs := HxInPb (Sub [< ((row i hP.`A)^T)%R, hP.`b i ord0 >] Hi).
    rewrite polyhedron.in_hs in Hhs. simpl in Hhs. rewrite -row_vdot. exact Hhs.
Qed.

End HPolyBase.

Section FinsetLemmas.

Variable (T : finType).

Lemma setD1_notin (A : {set T}) (x : T) :
  x \notin A -> A :\ x = A.
Proof.
  move=> HxA.
  apply/setP => y.
  apply/idP/idP.
  - move=> HyAx. move/setD1P in HyAx. by case: HyAx => _ HyA.
  - move=> HyA. apply/setD1P. split=> //. apply/negP => /eqP Hyx.
    rewrite -Hyx in HxA. by move/negP: HxA => HxA.
Qed.  

Lemma subset_setD1_add (A B : {set T}) (a : T) :
  A :\ a \subset B -> a \in B -> A \subset B.
Proof.
  move=> HAaB HaB.
  apply/subsetP => x HxA.
  case Hxa : (x == a).
  - move/eqP in Hxa. by rewrite Hxa.
  - move/subsetP in HAaB. have HxAa : x \in A :\ a.
    apply/setD1P. split=> //. by apply/negPf. exact: HAaB HxAa.
Qed.

Lemma simplex_subset (A B : {set T}) (x y : T) :
  x != y -> A :\ x \subset B -> A :\ y \subset B -> A \subset B.
Proof.
  move=> Hxy Hxs Hys.
  case: (boolP (x \in A)) => HxA. case: (boolP (y \in A)) => HyA.
  - have HxAy : x \in A :\ y. by apply/setD1P.
    move/subsetP in Hys. exact: subset_setD1_add A B x Hxs (Hys x HxAy).
  - by rewrite (setD1_notin A y HyA) in Hys.
  - by rewrite (setD1_notin A x HxA) in Hxs.
Qed.

Lemma subset_cardD1_exists (A B : {set T}) :
  A \subset B -> #|B| = #|A|.+1 -> exists i, i \in B /\ A = B :\ i.
Proof.
  move=> Hsub Hcard.
  have Hproper : A \proper B.
    rewrite properEcard. apply/andP; split=>//.
    by rewrite Hcard.
  move/properP: Hproper => [_ [x [HxB HxA]]].
  exists x. split=>//.
  have HsubD1 : A \subset B :\ x.
      rewrite subsetD1. by apply/andP.
  have HcardD1 : #|A| = #|B :\ x|.
      have HcardsD1 := cardsD1 x B.
      apply: succn_inj. 
      by rewrite -Hcard HcardsD1 HxB add1n.
  apply/setP.
  by apply/(subset_cardP HcardD1).
Qed.

End FinsetLemmas.

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

Section Interior.

Context (d : nat) (R : realFieldType).

Definition interior (P : 'poly[R]_d) : pred 'cV_d :=
  [pred z | (z \in P) && [forallf F in face_set P, (\pdim F < d) ==> (z \notin F)]].

Lemma in_interiorE (P : 'poly[R]_d) (z : 'cV_d) :
  z \in interior P = ((z \in P) && [forallf F in face_set P, (\pdim F < d) ==> (z \notin F)]).
Proof. by []. Qed.

Lemma in_interiorP (P : 'poly[R]_d) (z : 'cV_d) :
  reflect (z \in P /\ forall F, F \in face_set P -> \pdim F < d -> z \notin F) (z \in interior P).
Proof.
  rewrite in_interiorE.
  apply: (iffP andP).
  - move=> [zP /forallfP hF].
    split=> // F FP dimF.
    move: (hF F FP).
    by rewrite dimF.
  - move=> [zP hF].
    split=> //.
    apply/forallfP=> F FP.
    apply/implyP=> dimF.
    exact: hF F FP dimF.
Qed.

Lemma interior_subset (P : 'poly[R]_d) :
  {subset interior P <= P}.
Proof.
  by move=> z /in_interiorP [zP _].
Qed.

Lemma interior_notin_face P z F :
  z \in interior P -> F \in face_set P -> \pdim F < d -> z \notin F.
Proof.
  by move/in_interiorP=> [_ h] /h.
Qed.

Lemma not_full_dim_interior_empty P :
  \pdim P < d -> interior P =1 pred0.
Proof.
  move=> Hdim z.
  apply/negP.
  move/in_interiorP=> [HzP Hall].
  move: (Hall P (face_set_self P) Hdim).
  by rewrite HzP.
Qed.

End Interior.

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

Lemma face_of_cone (V : {fset 'cV[R]_d}) (Q : 'poly[R]_d) : 
  Q \in face_set (cone V) -> Q = [poly0] \/ exists W, (W `<=` V)%fset /\ Q = cone W.
Proof.
  move=> HQF.
  case: (Q == [poly0]) /eqP => HQ.
  - by left.
  - right.
    pose W := [fset v in V | v \in Q]. exists W; split.
    + apply/fsubsetP. move=> x Hx. rewrite/W in Hx.  move/imfsetP in Hx.
      move: Hx => [v Hv Hvx]. rewrite Hvx. simpl in Hv. rewrite inE in Hv.
      move/andP in Hv. by move: Hv => [HvV _].
    + apply/poly_eqP. move=> x. apply/idP/idP.
      * Admitted.

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

Section NormalCones.

Context (d : nat) (R : realFieldType).

Notation "'[ u , v ]" := (vdot u v).
Notation "'[' 'hp' e  ']'" := [affine <[e]> ].
Notation "[ 'affine' I ]"    := (@Core.affine_of _ _ (Phant _) I%VS).
Notation "[< A , b >]" := (BaseElt (pair A b)).

Definition normalVector (polytope : 'hpoly[R]_d) (i : 'I_(polytope.`c)) :=
  trmx (row i polytope.`A).

Definition active_constraints (P : 'hpoly[R]_d) (x : 'cV[R]_d) :=
  [set i : 'I_(P.`c) | '[trmx (row i P.`A) , x] == P.`b i 0%R].

Lemma in_active_constraintsE (P : 'hpoly[R]_d) (x : 'cV[R]_d) (i : 'I_(P.`c)) : 
  i \in active_constraints P x = ('[trmx (row i P.`A) , x] == P.`b i 0%R).
Proof. by rewrite inE. Qed.

Lemma in_active_constraintsP (P : 'hpoly[R]_d) (x : 'cV[R]_d) (i : 'I_(P.`c)) :
  reflect ('[trmx (row i P.`A) , x] = P.`b i 0%R) (i \in active_constraints P x).
Proof.
  rewrite in_active_constraintsE. 
  by apply:(iffP eqP).
Qed.

Definition normalCone (P : 'hpoly[R]_d) (x : 'cV[R]_d) :=
  coneOf P.`c d R (normalVector P) (active_constraints P x).

Lemma in_normalConeP (P : 'hpoly[R]_d) (x c : 'cV[R]_d) :
  (x \in P) -> reflect (x \in argmin '[P] c) (c \in (normalCone P x)).
Proof.
    move => HxInP. apply: (iffP idP).
    - move => HcInC. rewrite in_argmin. 
      apply/andP. split.
      - rewrite mem_mk_poly. exact HxInP.
      - rewrite poly_subset_mono. apply/poly_subsetP.
        move=> y Hy. rewrite in_hs. simpl. move/in_coneOfP in HcInC.
        case: HcInC => [w [HwInPt Hcomb]].
        rewrite combineE in Hcomb. rewrite Hcomb.
        rewrite vdot_sumDl. rewrite vdot_sumDl. 
        apply: ler_sum. intros i Huseless. destruct Huseless.
        rewrite vdotZl. rewrite vdotZl. case: i => ai Hai. simpl. 
        rewrite ler_pmul2l.
        move/fsubsetP in HwInPt.
        move/HwInPt in Hai. move/in_normalsOfP in Hai.
        case: Hai => [i [Hi Hai]]. rewrite inE in Hi. move/eqP in Hi.
        rewrite Hai. rewrite Hi.
        rewrite in_hpolyE in Hy. rewrite/lev in Hy.
        move/forallP in Hy. have HyInPi := Hy i.
        rewrite row_vdot. exact HyInPi.
        have Hwcon : conic w. exact (valP w).
        have Hwaipos : ai \in finsupp w = (0 < w ai)%R.
        apply: conic_finsuppE. exact Hwcon.
        rewrite Hwaipos in Hai. exact Hai.
    - intro HxInMin. rewrite/normalCone. simpl. 
      apply/in_coneP.
      have Hbound : polyhedron.bounded 'P(base_hpoly d R P)%PH c.
      - rewrite -base_hpolyP. apply/boundedP. exists x. rewrite mem_mk_poly.
        exact HxInP. apply/poly_subsetP. rewrite in_argmin in HxInMin. move/andP in HxInMin.
        case:HxInMin => _ HPSubHs. move=> y Hy. rewrite -mem_polyE in Hy.
        rewrite in_hs. simpl. move/poly_subsetP in HPSubHs. have HyInHS := 
        (HPSubHs y) Hy. rewrite -mem_polyE in HyInHS. rewrite (snd (polyhedron.in_hs)) in 
        HyInHS. exact HyInHS.
      have Hdual := dual_opt_sol Hbound. case:Hdual => w HwSubBase HCombine.
      have HNonEmpt : ([ poly0 ] `<` 'P^=(base_hpoly d R P; finsupp w))%PH.
      have HxInPEq : (x \in 'P^=(base_hpoly d R P; finsupp w))%PH.
      - rewrite -mem_mk_poly in HxInP. rewrite base_hpolyP in HxInP.
        apply/(compl_slack_cond HwSubBase HxInP). 
        have HArgSub := argmin_opt_value Hbound. move/poly_subsetP in HArgSub.
        rewrite -HCombine in HArgSub. rewrite base_hpolyP in HxInMin.
        rewrite mem_polyE in HxInMin. have HxInComb := (HArgSub x HxInMin).
        rewrite -mem_polyE in HxInComb. rewrite (affE x) in HxInComb. exact HxInComb.
      apply/proper0P. exists x. exact HxInPEq.
      have HArgEq := (dual_sol_argmin HwSubBase HNonEmpt).
      rewrite base_hpolyP in HxInMin. rewrite HCombine in HArgEq.
      simpl in HArgEq. rewrite HArgEq in HxInMin.
      pose p : lrel -> 'cV[R]_d := 
        fun e => let: BaseElt y := e in y.1.
      pose S0 : {fset 'cV[R]_d} :=
        [fset p e | e in finsupp w].
      pose w0_fun : {fsfun 'cV[R]_d ~> R} :=
        [fsfun a in S0 => \big[+%R/0%R]_(e <- enum_fset (finsupp w) 
        | p e == a) (val w e)].
      have Hw0con : conic w0_fun.
      - apply/conicP. intros x0 Hx0Inw0. rewrite /w0_fun in Hx0Inw0.
        have HfinSub : (finsupp [fsfun a in S0 => (\sum_(e <- finsupp w | 
        p e == a) val w e)%R] `<=`S0)%fset.
        - intro useless. apply/finsupp_sub.
        have HfinSubb := HfinSub 0%R. move/fsubsetP in HfinSubb. 
        have Hx0InS0 := (HfinSubb x0 Hx0Inw0). rewrite/w0_fun. simpl. 
        rewrite fsfunE. rewrite Hx0InS0. rewrite big_seq_cond. 
        rewrite sumr_ge0. trivial. intros i Hi. move/andP in Hi.
        case: Hi => HiInFs _. have Hwconic := valP w. simpl in Hwconic.
        move/conicP in Hwconic. have HiInCon := (Hwconic i HiInFs). exact HiInCon.
      pose w0 : {conic 'cV[R]_d ~> R} := Sub w0_fun Hw0con. exists w0.
      rewrite /w0. simpl. rewrite /w0_fun. apply/fsubsetP. move=> x0 Hx0Inw0.
      apply/imfsetP. have HfinSub : (finsupp [fsfun a in S0 => (\sum_(e <- finsupp w | 
      p e == a) val w e)%R] `<=`S0)%fset.
      - intro useless. apply/finsupp_sub.
      have HfinSubb := HfinSub 0%R. move/fsubsetP in HfinSubb. have Hx0InS0 := (HfinSubb 
      x0 Hx0Inw0). simpl. rewrite /S0 in Hx0InS0. move/imfsetP in Hx0InS0.
      case: Hx0InS0 => y Hy Hx0y. simpl in Hy. move/fsubsetP in HwSubBase.
      have HyInBase := (HwSubBase y Hy). rewrite/base_hpoly in HyInBase.
      move/imfsetP in HyInBase. case: HyInBase => i Hi Hyi. exists i.
      rewrite inE. simpl in Hi. rewrite in_polyEq in HxInMin. move/andP in HxInMin.
      case: HxInMin => HxInHp HxInBase. move/forallP in HxInHp. 
      have Hxy := HxInHp (Sub y Hy). simpl in Hxy. rewrite Hyi in Hxy.
      rewrite (snd in_hp) in Hxy. exact Hxy.
      rewrite Hyi in Hx0y. rewrite /p in Hx0y. simpl in Hx0y. exact Hx0y.
      rewrite /w0. rewrite /w0_fun. simpl. simpl in HCombine. 
      have HcComb : c = (combine w).1. rewrite HCombine. simpl. reflexivity.
      rewrite HcComb. rewrite (combineb1E HwSubBase). rewrite /combine.
      rewrite -(@big_seq_fsetE _ _ _ _ (base_hpoly d R P) predT (fun e => (w e *: e.1)%R)).
      simpl. change ((\sum_(i <- base_hpoly d R P) w i *: i.1)%R = 
      (\sum_(x0 : finsupp w0) w0 (val x0) *: val x0)%R).
      rewrite -(@big_seq_fsetE _ _ _ _ (finsupp w0) predT (fun a => (w0 a *: a)%R)).
      simpl. have Hleft : (\sum_(i <- base_hpoly d R P) w i *: i.1)%R =
      (\sum_(i <- finsupp w) w i *: i.1)%R. symmetry. apply/big_fset_incl.
      exact HwSubBase. intros x0 Hx0InBase Hx0NotInSupp. rewrite fsfun_dflt.
      rewrite scale0r. reflexivity. exact Hx0NotInSupp. rewrite Hleft.
      have Hw0Sub : (finsupp w0_fun `<=` S0)%fset. apply finsupp_sub.
      have Hw0Sum : (\sum_(i <- finsupp w0_fun) w0_fun i *: i)%R =
      (\sum_(i <- S0) w0_fun i *: i)%R. apply big_fset_incl. exact Hw0Sub.
      intros x0 Hx0InS0 Hx0NotInSupp. rewrite fsfun_dflt. rewrite scale0r. reflexivity.
      exact Hx0NotInSupp. rewrite Hw0Sum. rewrite /w0_fun.
      rewrite (@partition_big_imfset _ _ _ _ _ p _ _). simpl.
      rewrite -/S0. apply: eq_fbigr => a Ha. intro useless. 
      rewrite fsfunE Ha. rewrite scaler_suml. apply: eq_fbigr => i Hi /eqP Hpi.
      rewrite -Hpi. rewrite /p. case i. by move => p0.
Qed.

Lemma normal_cones_are_pointed (P : 'hpoly[R]_d) :
    (\pdim '[P] = d.+1) -> (forall x : 'cV[R]_d, (x \in P) -> pointed (normalCone P x)).
Proof.
    move=> HfullD x HxInP. destruct (pointed (normalCone P x)) eqn:Hpointed.
        - trivial.
        - move/eqP in Hpointed. rewrite eqbF_neg in Hpointed.
          move/pointedPn in Hpointed. case: Hpointed => x0 Hpointed.
          case: Hpointed => d0 Hd0null Hd0InP.
          have Hmin : forall z : 'cV[R]_d, forall t : R, (z \in P)
          -> ('[x0 + t*:d0, z] >= '[x0 + t*:d0, x])%R.
            - intros z t HzInP. have Hd0InPt := Hd0InP t.
              move/in_coneOfP in Hd0InPt.
              case: Hd0InPt => [w [HwInPt Hcomb]].
              rewrite combineE in Hcomb. rewrite Hcomb.
              rewrite vdot_sumDl. rewrite vdot_sumDl.
              apply: ler_sum. intros i Huseless. destruct Huseless.
              rewrite vdotZl. rewrite vdotZl. case: i => ai Hai. simpl. 
              rewrite ler_pmul2l.
              move/fsubsetP in HwInPt.
              move/HwInPt in Hai. move/in_normalsOfP in Hai.
              case: Hai => [i [Hi Hai]]. move/in_active_constraintsP in Hi. 
              rewrite Hai. rewrite Hi.
              rewrite in_hpolyE in HzInP. rewrite/lev in HzInP.
              move/forallP in HzInP. have HzInPi := HzInP i.
              rewrite row_vdot. exact HzInPi.
              have Hwcon : conic w. exact (valP w).
              have Hwaipos : ai \in finsupp w = (0 < w ai)%R.
              apply: conic_finsuppE. exact Hwcon.
              rewrite Hwaipos in Hai. exact Hai.
          have Hnull : forall z, (z \in P) -> '[d0, z - x] == 0%R.
            intros z HzInP.
            have Hminz := Hmin z. 
            destruct ('[d0, z - x] == 0%R) eqn:HzDd0.
            - trivial.
            - have Hminzt :=  Hminz (('[x0,z-x] + 1)/'[d0,x - z])%R HzInP.
              rewrite vdotDl in Hminzt. rewrite vdotDl in Hminzt. 
              rewrite <- ler_subl_addr in Hminzt.
              rewrite vdotZl in Hminzt. rewrite vdotZl in Hminzt.
              rewrite <- addrA in Hminzt. rewrite -mulrBr in Hminzt.
              rewrite -vdotBr in Hminzt. rewrite divrK in Hminzt.
              rewrite -ler_subr_addl in Hminzt. rewrite -vdotBr in Hminzt.
              rewrite ger_addl in Hminzt. have H01 : (0 <= 1 :>R)%R.
              exact ler01. have H00 : (1 == 0 :> R)%R. rewrite eq_le. 
              apply/andP. split. exact Hminzt. exact H01. rewrite oner_eq0 in H00.
              exact H00. rewrite unitfE. move/eqP in HzDd0. apply/eqP.
              rewrite -opprB. rewrite vdotNr. apply/eqP. rewrite oppr_eq0.
              apply/eqP. exact HzDd0.
              have HpInHP : ('[P] `<=` [ hp [<d0, '[ d0, x]>] ]%:PH)%PH.
              - apply/poly_leP. move=> z HzInP. rewrite (polyhedron.in_hp.1.2).
                simpl. rewrite mem_mk_poly in HzInP. have Hnullz := (Hnull z) HzInP. rewrite vdotBr in Hnullz.
                rewrite subr_eq0 in Hnullz. exact Hnullz.
              have HdimHP : adim [hp [<d0, '[d0, x]>]] = d.
              - have HadimHP := (@adim_hp R d [<d0, '[d0, x]>]).
                simpl in HadimHP. rewrite -eqbF_neg in Hd0null.
                move/eqP in Hd0null. rewrite Hd0null in HadimHP. simpl in HadimHP.
                have Haff0 : ([ affine0 ] `<` [ hp [<d0, '[ d0, x]>] ])%PH.
                - apply/affine_proper0P. exists x. rewrite (snd in_hp).
                  by apply/eqP.
                have HadimH := HadimHP Haff0. rewrite add0n in HadimH. exact HadimH.
              have HaffS : (adim (hull '[P]) <= adim [hp [<d0, '[d0, x]>]])%N.
              - have HhullP := (hullP '[P] [ hp [<d0, '[ d0, x]>] ]).
                rewrite HhullP in HpInHP. by apply/adimS.
              rewrite HdimHP in HaffS. Search "orth".
              rewrite HfullD in HaffS. by rewrite ltnn in HaffS.
Qed.

End NormalCones.

Section Genericity.

Context (m d: nat) (R : realFieldType).

Notation simplex_m := (simplex [finType of 'I_m]).
Notation simplicialComplex_m := (simplicialComplex [finType of 'I_m]).

Variable (normals : 'I_m -> 'cV[R]_d) (K : simplicialComplex_m).

Local Notation coneOf := (coneOf m d R normals).
Local Notation interior := (interior d R).
Local Notation face_of_cone := (face_of_cone m d R normals).

Definition isKGeneric (k : nat) (x : 'cV[R]_d) :=
  forall F : simplex_m, F \in K -> \pdim (coneOf F) < k -> (x \notin coneOf F).

Hypothesis Hasc : (isAsc K).
Hypothesis Hdim : (dim K = d).

Lemma dgenericityP (x : 'cV[R]_d) :
  isKGeneric d x -> forall F : simplex_m, F \in K -> 
  reflect (x \in coneOf F) (x \in interior (coneOf F)).
Proof.
  move=> Hgen F HFK.
  apply: (iffP idP).
  - exact: interior_subset (coneOf F) x.
  - move=> HxC. apply/in_interiorP; split=> //.
    move=> G HGFace HGdim. Admitted.
(* Il faudrait montrer que G est inclus dans un cone engendré par un 
sous-ensemble de F (qui sera donc dans K) et de dimension < d *)

End Genericity.

Section OddCoveringTheorem.

Context (m d: nat) (R : realFieldType).

Notation simplex_m := (simplex [finType of 'I_m]).
Notation simplicialComplex_m := (simplicialComplex [finType of 'I_m]).

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

Section HighLevelChecks.

Context (R : realFieldType) (d : nat).

Variable (P : 'hpoly[R]_d) (V : {fset 'cV[R]_d}).

Definition m := P.`c.

Notation simplex_m := (simplex [finType of 'I_m]).
Notation simplex_graph := (graph [choiceType of (simplex_m)]).
Notation vertex_graph := (graph [choiceType of ('cV[R]_d)]).
Notation "x <=m y" := (lev x y).
Notation "'[ u , v ]" := (vdot u v).
Notation normalVector := (normalVector d R).

Definition incomparable {T : finType} (A B : {set T}) :=
  ~~ (A \subset B) && ~~ (B \subset A).

Record Certificate := {
    full_dim_point : 'cV[R]_d;
    full_dim_dir : 'M[R]_(d,d);
    full_dim_inv : 'M[R]_(d,d);
    activeSets : 'cV[R]_d -> {set 'I_m};
    facets : {set simplex_m};
    mapping : simplex_m -> 'cV[R]_d;
    graph : simplex_graph;
    specialVertex : 'cV[R]_d;
    specialSimplex : 'I_d -> 'I_m;
    witnesses : 'M[R]_(d,d);
    weights : simplex_m -> 'cV[R]_d;
    geom_graph : vertex_graph
}.

(* Well-formedness condition on facets *)
Definition facetsAreDSimplices (cert : Certificate) :=
  forall f : simplex_m, f \in (facets cert) -> #|f| == d.

(* Well-formedness condition on mapping *)
Definition mappingHasImageInPoints (cert : Certificate) :=
  forall f : simplex_m, f \in facets cert -> mapping cert f \in V.

(* Well-formedness condition on graph *)
Definition graphVerticesAreFacets (cert : Certificate) :=
  vertices (graph cert) =i facets cert.

Definition graphIsUndirected (cert : Certificate) :=
  forall x y, y \in successors (graph cert) x <-> x \in successors (graph cert) y.

(* Well-formedness condition on the special simplex *)
Definition specialSimplexInSpecialCone(cert : Certificate) :=
  specialSimplex cert @: 'I_d \in facets cert /\
  mapping cert (specialSimplex cert @: 'I_d) = (specialVertex cert).

(* Well-formedness condition on the weights *)
Definition weightsAreStrictlyPositiveVectors (cert : Certificate) :=
  forall f : simplex_m, mapping cert f = (specialVertex cert)
  -> f != (specialSimplex cert @: 'I_d) -> (0 <=m (weights cert f)) /\ (weights cert f <> 0%R).
  
(* Well-formedness condition on the geometric graph *)
Definition geomGraphVerticesArePoints (cert : Certificate) :=
  vertices (geom_graph cert) = V.

Definition geomGraphIsImageOfGraph (cert : Certificate) :=
  forall v w : 'cV[R]_d, v \in vertices (geom_graph cert) -> w \in vertices (geom_graph cert)
  -> (w \in successors (geom_graph cert) v <-> exists fv fw : simplex_m, fv \in vertices (graph cert) 
  /\ fw \in successors (graph cert) fv /\ mapping cert fv = v /\ mapping cert fw = w).

(* Full dimension hypothesis *)
Definition full_dim_check (cert : Certificate) :=
  full_dim_point cert \in V
  /\ (forall i : 'I_d, (full_dim_point cert + col i (full_dim_dir cert))%R \in V)
  /\ forall (i j : 'I_d), (i = j /\ '[col i (full_dim_dir cert), col j (full_dim_inv cert)] <> 0)%R
  \/ (i <> j /\ '[col i (full_dim_dir cert), col j (full_dim_inv cert)] = 0)%R.

(* Condition T1 *)
Definition feasibility_check (cert : Certificate) :=
  {subset V <= P} /\ forall x : 'cV[R]_d, x \in V ->
  activeSets cert x = [set i : 'I_m | '[normalVector P i , x] == P.`b i ord0].

(* Condition T2 *)
Definition mapping_check (cert : Certificate) :=
  forall f : simplex_m, f \in facets cert ->
  f \subset activeSets cert (mapping cert f).

(* Condition T3 *)
Definition graph_check (cert : Certificate) :=
  forall f, f \in vertices (graph cert) -> #|successors (graph cert) f| <= d /\
  forall i : 'I_m, (i \in f) -> exists f', (f' \in successors (graph cert) f) /\ f:\i \subset f'.

(* Condition T4 *)
Definition inversibility_check (cert : Certificate) :=
  forall (i j : 'I_d), (i = j /\ '[\col_k (P.`A (specialSimplex cert i) k), (col j (witnesses cert))] > 0)%R
  \/ (i <> j /\ '[\col_k (P.`A (specialSimplex cert i) k), (col j (witnesses cert))] = 0)%R.

(* Condition T5 *)
Definition separability_check (cert : Certificate) :=
  forall f : simplex_m, mapping cert f = (specialVertex cert)
  -> f != (specialSimplex cert @: 'I_d)
  -> forall i : 'I_m, i \in f ->
  ('[(witnesses cert) *m (weights cert f) , normalVector P i] <= 0)%R.

(* Condition T6 *)
Definition geom_edge_pairwise_check (cert : Certificate) :=
  forall v : 'cV[R]_d, v \in vertices (geom_graph cert) -> forall w : 'cV[R]_d,
  w \in successors (geom_graph cert) v -> incomparable (activeSets cert v) (activeSets cert w).

(* Condition T7 *)
Definition connectivity_check (cert : Certificate) :=
  connected (geom_graph cert).

(* Condition T8 *)
Definition geom_edge_difference_pairwise_check (cert : Certificate) :=
  forall v : 'cV[R]_d, v \in vertices (geom_graph cert) -> forall w w' : 'cV[R]_d,
  w \in successors (geom_graph cert) v /\ w' \in successors (geom_graph cert) v -> w <> w' 
  -> incomparable (activeSets cert v :\: activeSets cert w) (activeSets cert v :\: activeSets cert w').

End HighLevelChecks.

Section CertificateLemmas.

Context (d : nat) (R : realFieldType).

Variable (P : 'hpoly[R]_d) (V : {fset 'cV[R]_d}).

Notation "'[ u , v ]" := (vdot u v).

Local Notation m := (m R d P).
Local Notation simplex_m := (simplex [finType of 'I_m]).
Local Notation Certificate := (Certificate R d P).
Local Notation active_constraints := (active_constraints d R P).

Variable (cert : Certificate).

Local Notation facetsAreDSimplices := (facetsAreDSimplices R d P cert).
Local Notation graphVerticesAreFacets := (graphVerticesAreFacets R d P cert).
Local Notation graphIsUndirected := (graphIsUndirected R d P cert).
Local Notation feasibility_check := (feasibility_check R d P V cert).
Local Notation graph_check := (graph_check R d P cert).
Local Notation full_dim_check := (full_dim_check R d P V cert).
Local Notation facets := (facets R d P cert).
Local Notation graph := (graph R d P cert).
Local Notation activeSets := (activeSets R d P cert).
Local Notation full_dim_point := (full_dim_point R d P cert).
Local Notation full_dim_dir := (full_dim_dir R d P cert).
Local Notation full_dim_inv := (full_dim_inv R d P cert).

Lemma vertices_card (f : simplex_m) :
  facetsAreDSimplices -> graphVerticesAreFacets -> 
  f \in vertices graph -> #|f| = d.
Proof.
  move=> Hfacets Hvert Hfvert.
  apply/eqP.
  apply: (Hfacets f).
  by rewrite -(Hvert f).
Qed.

Lemma facets_cardND1 (f : simplex_m) (i : 'I_m) :
  facetsAreDSimplices -> graphVerticesAreFacets -> f \in vertices graph -> 
  i \in f -> #|f :\ i| = d - 1.
Proof.
  move=> Hfacets Hvert Hfvert Hif.
  have Hfcard := (vertices_card f Hfacets Hvert Hfvert).
  have H := cardsD1 i f.
  have Hsub := congr1 (fun n : nat => n - 1) H.
  rewrite addnC in Hsub. rewrite Hif in Hsub. simpl in Hsub.
  rewrite addnK in Hsub. by rewrite Hfcard in Hsub.
Qed.

Lemma facets_regular : 
  facetsAreDSimplices -> facets != set0 -> isDRegular d facets.
Proof.
  move=> Hfacets Hemp. split=>//.
  move=> F HF. by have/eqP HFcard := (Hfacets F HF).
Qed.

Lemma facets_cert : 
  facetsAreDSimplices-> facetsOf (set_to_asc facets) = facets.
Proof.
  move=> Hfacets.
  have [Hnemp | Hemp] := boolP (facets != set0).
  - have Hreg := facets_regular Hfacets Hnemp.
    apply: facets_of_set. by exists d.
  - rewrite negbK in Hemp. move/eqP in Hemp.
    rewrite Hemp. rewrite set_to_asc_set0. 
    by rewrite facetsOf_set0.
Qed. 

Lemma incident_facets_cert_subset (r : simplex_m) : 
  facetsAreDSimplices -> {subset incident_facets (set_to_asc facets) r <= facets}.
Proof.
  move=> Hfacets.
  have HfacetsOf := facets_cert Hfacets.
  move=> s Hs. 
  have Hsub := incident_facets_subset (set_to_asc facets) r s Hs.
  by rewrite HfacetsOf in Hsub.
Qed.

Lemma dim_cert : 
  facetsAreDSimplices -> facets != set0 -> 
  dim (set_to_asc facets) = d.
Proof.
  move=> Hfacets Hemp.
  have Hreg := facets_regular Hfacets Hemp.
  exact: dim_regular_set d facets Hreg.
Qed.

Lemma ridges_card (r : simplex_m) :
  facetsAreDSimplices -> facets != set0 -> 
  r \in ridgesOf (set_to_asc facets) -> #|r| = d.-1.
Proof.
  move=> Hfacets Hemp Hr.
  move/in_ridgesOfP in Hr. case: Hr => [Hrf Hrdim].
  rewrite/sdim in Hrdim. 
  by rewrite (dim_cert Hfacets Hemp) in Hrdim.
Qed.

Lemma successors_subset (f : simplex_m) :
  graphVerticesAreFacets -> {subset successors graph f <= facets}.
Proof.
  move=> Hgraph x Hx.
  have/fsubsetP Hsub := sub_succ graph f.
  have Hxvert := Hsub x Hx.
  by rewrite (Hgraph x) in Hxvert.
Qed.

Lemma full_dim_cert :
  feasibility_check -> full_dim_check -> \pdim '[P] = d.+1.
Proof.
  move=> [HV _] [Hpoint [Hdir Hinv]].
  have HpointP : full_dim_point \in '[P].
    rewrite mem_mk_poly.
    exact: HV full_dim_point Hpoint.
  pose X := [seq (full_dim_point + col i full_dim_dir)%R | i <- enum 'I_d].
  have HXP : {in X, forall x : 'cV_d, x \in '[P]}.
    move=> x Hx.
    rewrite /X in Hx. move/mapP in Hx. move: Hx => [i Hi Hxi].
    rewrite Hxi. rewrite mem_mk_poly. by exact: HV (Hdir i).
  pose A := [affine <<[seq (x - full_dim_point)%R | x <- X]>> & full_dim_point].
  have Hnonemp : [affine0] `<` A. by exact: mk_affine_proper0.
  have HX : [seq (x - full_dim_point)%R | x <- X] = [seq col i full_dim_dir | i <- enum 'I_d].
    rewrite/X.
    rewrite -map_comp.
    apply: eq_map => i. 
    by rewrite /comp GRing.addrC GRing.addrA GRing.addNr GRing.add0r.  
  have Hfree : free [seq col i full_dim_dir | i <- enum 'I_d].
    apply/freeP=> w Hw i.
    have Hwi := congr1 (fun u => '[u, col (enum_val i) full_dim_inv]%R) Hw.
    rewrite vdot0l vdot_sumDl (bigD1 i) //= big1 ?addr0 in Hwi.
    rewrite (nth_map (enum_val i) 0%R) ?size_enum ?ltn_ord // in Hwi.
    rewrite vdotZl in Hwi.
    move/eqP in Hwi. rewrite GRing.mulf_eq0 in Hwi.
    move/orP: Hwi => [/eqP Ha | /eqP Hb].
    - by [].
    - have Hi := (Hinv (enum_val i) (enum_val i)).
      have Hnz : '[col (enum_val i) full_dim_dir, col (enum_val i) full_dim_inv]%R <> 0%R.
      case: Hi => [[_ Hnz] | [Hneq _]].
      + exact: Hnz.
      + by case: Hneq.
      rewrite -(enum_val_nth (enum_val i)) in Hb.
      by move: Hnz; rewrite Hb.
    rewrite size_enum_ord.
    change (val i < d).
    have Hi : val i < #|'I_d| := ltn_ord i.
    have Hcard : #|'I_d| = d. apply: card_ord.
    exact: (ltn_ord (cast_ord (card_ord d) i)).
    move=> j HjDi. have Hij := (Hinv (enum_val j) (enum_val i)).
    have Hneq : enum_val j <> enum_val i.
      move=> Heq.
      have Hijord : j = i := (can_inj enum_valK) j i Heq.
      move: HjDi.
      by rewrite Hijord eqxx.
    have Hzero : '[ col (enum_val j) full_dim_dir, col (enum_val i) full_dim_inv]%R = 0%R.
      case: Hij => [[Heq _] | [_ Hzero]].
      + by case: (Hneq Heq).
      + exact Hzero.
    rewrite vdotZl. 
    rewrite (nth_map (enum_val i) 0%R) ?size_enum ?ltn_ord //.
    rewrite -(enum_val_nth (enum_val i)).
    rewrite Hzero.
    by rewrite GRing.mulr0.
    rewrite size_enum_ord.
    change (val j < d).
    have Hj : val j < #|'I_d| := ltn_ord j.
    have Hcard : #|'I_d| = d. apply: card_ord.
    exact: (ltn_ord (cast_ord (card_ord d) j)).
  have Hadim : adim [affine <<[seq (x - full_dim_point)%R | x <- X]>> & full_dim_point] = d.+1.
    rewrite (adimN0_eq Hnonemp).
    congr(_.+1).
    rewrite dir_mk_affine.
    rewrite HX.
    move/eqP in Hfree. rewrite Hfree.
    by rewrite size_map size_enum_ord.
  apply/eqP; rewrite eqn_leq; apply/andP; split=>//.
  - apply: adim_leSn.
  - have Hdimsub :=  dim_sub_affine HpointP HXP.
    by rewrite Hadim in Hdimsub.
Qed.

Lemma activeSets_cert :
  feasibility_check -> forall x : 'cV[R]_d, x \in V -> activeSets x = active_constraints x.
Proof.
  move=>Hfeas x HxV.
  by rewrite (snd (Hfeas) x HxV).
Qed.

End CertificateLemmas.

Section RidgesHaveEvenIncidence.

Context (d : nat) (R : realFieldType).

Variable (P : 'hpoly[R]_d) (V : {fset 'cV[R]_d}).

Local Notation m := (m R d P).
Local Notation simplex_m := (simplex [finType of 'I_m]).
Local Notation Certificate := (Certificate R d P).
Local Notation facetsAreDSimplices := (facetsAreDSimplices R d P).
Local Notation graphVerticesAreFacets := (graphVerticesAreFacets R d P).
Local Notation graphIsUndirected := (graphIsUndirected R d P).
Local Notation graph_check := (graph_check R d P).
Local Notation ridgesHaveEvenIncidence := (ridgesHaveEvenIncidence m).
Local Notation facets := (facets R d P).
Local Notation graph := (graph R d P).

Variable (cert : Certificate).

Local Notation vertices_card := (vertices_card d R P cert).
Local Notation facets_cardND1 := (facets_cardND1 d R P cert).
Local Notation facets_regular := (facets_regular d R P cert).
Local Notation facets_cert := (facets_cert d R P cert).
Local Notation incident_facets_cert_subset := (incident_facets_cert_subset d R P cert).
Local Notation dim_cert := (dim_cert d R P cert).
Local Notation ridges_card := (ridges_card d R P cert).
Local Notation successors_subset := (successors_subset d R P cert).

Hypothesis Hdim : d >= 1.
Hypothesis Hfacets : facetsAreDSimplices cert.
Hypothesis Hvert   : graphVerticesAreFacets cert.
Hypothesis Hgraph  : graph_check cert.
Hypothesis Hundir : graphIsUndirected cert.

Definition graph_neighbors (f : simplex_m) (i : 'I_m) :=
  [set g in successors (graph cert) f | f :\ i \subset g].

Lemma in_graph_neighborsE (f : simplex_m) (i : 'I_m) (g : simplex_m) :
  g \in graph_neighbors f i = (g \in successors (graph cert) f) && (f :\ i \subset g).
Proof. by rewrite inE. Qed.

Lemma in_graph_neighborsP (f : simplex_m) (i : 'I_m) (g : simplex_m) :
  reflect (g \in successors (graph cert) f /\ f :\ i \subset g) (g \in graph_neighbors f i).
Proof.
  rewrite in_graph_neighborsE.
  apply: (iffP andP).
  - by [].
  - by [].
Qed.

Lemma in_graph_neighbors_subset (f : simplex_m) (i : 'I_m) :
  {subset graph_neighbors f i <= successors (graph cert) f}.
Proof. by move=> g /in_graph_neighborsP [gS _]. Qed.

Lemma graph_neighbors_disjoint (f : simplex_m) :
  f \in vertices (graph cert) -> forall i j : 'I_m, i != j -> [disjoint (graph_neighbors f i) & (graph_neighbors f j)]%B.
Proof.
  move=> Hf i j Hij.
  rewrite -(setI_eq0). apply/eqP.
  apply/setP => g.
  rewrite inE. 
  rewrite in_set0.
  apply/negP.
  move=> /andP [/in_graph_neighborsP [His Hig] /in_graph_neighborsP [Hjs Hjg]].
  have Hfg := simplex_subset [finType of 'I_m] f g i j Hij Hig Hjg.
  rewrite (Hvert f) in Hf. have Hfc := Hfacets f Hf.
  have/fsubsetP Hsub := sub_succ (graph cert) f. 
  have Hg := Hsub g His. rewrite (Hvert g) in Hg. have Hgc := Hfacets g Hg.
  move/eqP in Hgc. move/eqP in Hfc. 
  have Hcard : #|f| = #|g| by rewrite Hgc Hfc.
  move/(subset_cardP Hcard) in Hfg. move/setP in Hfg.
  rewrite Hfg in Hjs. have Habs := succxx (graph cert) g.
  by move/negP in Habs.
Qed.

Lemma graph_neighbors_empty (f : simplex_m) (i : 'I_m) :
  f \in vertices (graph cert) -> i \notin f -> graph_neighbors f i == set0.
Proof.
  move=> Hfvert Hif.
  apply/eqP. 
  apply/setP => g. 
  rewrite in_set0.
  apply/negP.
  move/in_graph_neighborsP => [Hgs Hfig].
  rewrite (setD1_notin [finType of 'I_m] f i Hif) in Hfig.
  rewrite (Hvert f) in Hfvert. have Hfc := Hfacets f Hfvert.
  have/fsubsetP Hsub := sub_succ (graph cert) f. 
  have Hg := Hsub g Hgs. rewrite (Hvert g) in Hg. have Hgc := Hfacets g Hg.
  move/eqP in Hgc. move/eqP in Hfc. 
  have Hcard : #|f| = #|g| by rewrite Hgc Hfc.
  move/(subset_cardP Hcard) in Hfig. move/setP in Hfig.
  rewrite Hfig in Hgs. have Habs := succxx (graph cert) g.
  by move/negP in Habs.
Qed.

Lemma graph_neighbors_non_empty (f : simplex_m) :
  f \in vertices (graph cert) -> forall i : 'I_m, i \in f -> graph_neighbors f i != set0.
Proof.
  move=> Hf i Hi.
  apply/set0Pn.
  case: (Hgraph f Hf) => _ /(_ i Hi) [g [Hgf Hsub]].
  exists g.
  exact/in_graph_neighborsP.
Qed.

Lemma bigcup_neighbors_subset (f : simplex_m) :
  \bigcup_(i : 'I_m) graph_neighbors f i \subset successors (graph cert) f.
Proof.
  apply/subsetP => g Hg.
  move/bigcupP: Hg => [i _ Hgi].
  exact: in_graph_neighbors_subset f i g Hgi.
Qed.

Lemma bigcup_neighbors_card (f : simplex_m) :
  f \in vertices (graph cert) -> #|\bigcup_(i : 'I_m) graph_neighbors f i| = \sum_(i < m) #|graph_neighbors f i|.
Proof.
  move=> Hfvert.
  have Hpart := @partition_disjoint_bigcup [finType of simplex_m] [finType of 'I_m] nat 0 addn_comoid
  (fun i : 'I_m => graph_neighbors f i) (fun _ : simplex_m => 1) (graph_neighbors_disjoint f 
  Hfvert). simpl in Hpart.
  rewrite sum1_card in Hpart. rewrite Hpart. apply: eq_bigr => i _.
  by rewrite sum1_card.
Qed.

Lemma bigcup_neighbors_card_geq (f : simplex_m) :
  f \in vertices (graph cert) -> #|\bigcup_(i : 'I_m) graph_neighbors f i| >= d.
Proof.
  move=> Hfvert.
  have Hffac := Hfvert.
  rewrite (Hvert f) in Hffac.
  have/eqP Hfcard := Hfacets f Hffac.
  apply: (leq_trans (n := #|f|)).
  - by rewrite Hfcard.
  - rewrite (bigcup_neighbors_card f Hfvert).
    rewrite -sum1_card.
    rewrite big_mkcond. 
    apply: leq_sum => i _.
    case Hif: (i \in f).
    + have Hifnonemp := graph_neighbors_non_empty f Hfvert i Hif.
      by rewrite card_gt0.
    + by [].
Qed.

Lemma successors_card_eq (f : simplex_m) :
  f \in vertices (graph cert) -> #|successors (graph cert) f| = \sum_(i < m) #|graph_neighbors f i|.
Proof.
  move=> Hfvert.
  have [Hd Hg] := Hgraph f Hfvert.
  have Hcard : #|successors (graph cert) f| = #|\bigcup_(i : 'I_m) graph_neighbors f i|.
    apply/eqP; rewrite eqn_leq; apply/andP; split=>//.
    - apply: (@leq_trans d _ _).
      + by [].
      + by apply: bigcup_neighbors_card_geq.
    - by exact: subset_leq_card (bigcup_neighbors_subset f).
  by rewrite (bigcup_neighbors_card f Hfvert) in Hcard.
Qed.

Lemma sum_simplex (f : simplex_m) :
  f \in vertices (graph cert) -> \sum_(i : 'I_m) #|graph_neighbors f i| = \sum_(i in f) #|graph_neighbors f i|.
Proof.
  move=> Hfvert.
  rewrite [RHS]big_mkcond.
  apply: eq_bigr => i0 _.
  case: (boolP (i0 \in f)) => Hi0f.
  - by [].
  - apply/eqP. rewrite cards_eq0. by apply:graph_neighbors_empty.
Qed.

Lemma bigcup_neighbors_eq (f : simplex_m) :
  f \in vertices (graph cert) -> \bigcup_(i : 'I_m) graph_neighbors f i =i successors (graph cert) f.
Proof.
  move=> Hfvert.
  have Hsub : \bigcup_(i < m) graph_neighbors f i \subset [set x | x \in successors (graph cert) f].
    apply/subsetP => x Hx.
    have/subsetP Hsub := bigcup_neighbors_subset f.
    have Hsubx := Hsub x Hx.
    by rewrite inE.
  have Hcard : #|\bigcup_(i < m) graph_neighbors f i| == #|[set x | x \in successors (graph cert) f]|.
    rewrite (bigcup_neighbors_card f Hfvert).
    rewrite -(successors_card_eq f Hfvert).
    by rewrite cardsE.
  have/eqP Heq : \bigcup_(i < m) graph_neighbors f i == [set x | x \in successors (graph cert) f].
    rewrite eqEcard.
    apply/andP; split =>//; move/eqP in Hcard; by rewrite Hcard.
  move=> x; rewrite Heq; by rewrite inE.
Qed.

Lemma graph_neighbors_card1 (f : simplex_m) :
  f \in vertices (graph cert) -> forall i : 'I_m, i \in f -> #|graph_neighbors f i| = 1.
Proof.
  move=> Hfvert i Hif.
  have Hfcard := (vertices_card f Hfacets Hvert Hfvert).
  have [Hd Hg] := Hgraph f Hfvert.
  have Hsum := sum_simplex f Hfvert.
  have Hcard : \sum_(i in f) #|graph_neighbors f i| <= d. 
    rewrite -Hsum. by rewrite -(successors_card_eq f Hfvert).
  apply/eqP; rewrite eqn_leq; apply/andP; split=>//.
  - case: (boolP (1 < #|graph_neighbors f i|)) => [Hgt | Hnotgt].
    + have Habs : d+1 <= \sum_(i in f) #|graph_neighbors f i|.
        rewrite (bigD1 i Hif) /=.
        rewrite -{1}(subnKC Hdim). rewrite addnC. rewrite addnA.
        change (2 + (d - 1) <= #|graph_neighbors f i| + \sum_(i0 < m | (i0 \in f) && (i0 != i)) #|graph_neighbors f i0|).
        apply: (@leq_add 2 (d-1) #|graph_neighbors f i| (\sum_(i0 < m | (i0 \in f) && (i0 != i)) #|graph_neighbors f i0|)).
        * by [].
        * have Hdiff := facets_cardND1 f i Hfacets Hvert Hfvert Hif.
          rewrite -Hdiff. rewrite -sum1_card.
          have Hsame : \sum_(i0 in f :\ i) 1 = \sum_(i0 in f | i0 != i) 1.
            apply: eq_bigl => i0. rewrite inE.
            have Hnotin : i0 \notin [set i] = (i0 != i).
              by rewrite inE.
            rewrite Hnotin. by rewrite andbC.
          rewrite Hsame.
          apply: leq_sum => i0 /andP [Hi0f _].
          - rewrite card_gt0. by apply: graph_neighbors_non_empty.
      have Hleq := leq_trans Habs Hcard.
      rewrite addn1 in Hleq. by rewrite ltnn in Hleq.
    + by rewrite -leqNgt in Hnotgt.
  - rewrite card_gt0. by apply: graph_neighbors_non_empty.
Qed.

Lemma in_successorsP (f : simplex_m) (g : simplex_m) :
  f \in vertices (graph cert) -> reflect (exists! i : 'I_m, i \in f /\ g \in graph_neighbors f i)
  (g \in successors (graph cert) f).
Proof.
  move=> Hf.
  rewrite -(bigcup_neighbors_eq f Hf g).
  apply: (iffP idP).
  - move/bigcupP => [i _ Hi].
    exists i. split.
    + case: (boolP (i \in f)) => Hif.
      * by [].
      * have/eqP Hemp := graph_neighbors_empty f i Hf Hif.
        rewrite Hemp in Hi. by rewrite in_set0 in Hi.
    + move=> j [Hjf Hgfj].
      case: (boolP (i \in f)) => Hif.
      * case: (boolP (i == j)) => [/eqP Hij | Hij].
        - by [].
        - by rewrite (disjointFr (graph_neighbors_disjoint f Hf i j Hij) Hi) in Hgfj.
      * have/eqP Hemp := (graph_neighbors_empty f i Hf Hif).
        rewrite Hemp in Hi. by rewrite in_set0 in Hi.
  - move=>[i [[_ Hg] _]].
    apply/bigcupP; by exists i.
Qed.

Lemma in_successors (f : simplex_m) (g : simplex_m) :
  f \in vertices (graph cert) -> g \in successors (graph cert) f -> exists! i : 'I_m, i \in f /\ f :\ i \subset g.
Proof.
  move=> Hf /in_successorsP Hg.
  have Hgf := Hg Hf. move: Hgf=> [i [[Hif /in_graph_neighborsP [Hgs Hgsub]] Hu]].
  exists i. split=>//.
  move=> j [Hjf Hfsub].
  have Huj := Hu j.
  apply: Huj.
  split=>//.
  by apply/in_graph_neighborsP.
Qed.

Lemma successors_cardD (f : simplex_m) :
  f \in vertices (graph cert) -> #|successors (graph cert) f| = d.
Proof.
  move=> Hfvert.
  have Hfcard := (vertices_card f Hfacets Hvert Hfvert).
  rewrite (successors_card_eq f Hfvert).
  rewrite (sum_simplex f Hfvert).
  rewrite -[RHS]Hfcard.
  rewrite -sum1_card.
  apply: eq_bigr.
  exact: graph_neighbors_card1 f Hfvert.
Qed.
  
Lemma successors_unique (f : simplex_m) :
  f \in vertices (graph cert) -> forall i, (i \in f) -> exists! f',
  (f' \in successors (graph cert) f) /\ (f :\ i \subset f').
Proof.
  move=> Hfvert i Hif.
  have/eqP Hcard1 := graph_neighbors_card1 f Hfvert i Hif.
  move/cards1P: Hcard1 => [g Hg].
  exists g. split.
  - have Hgin : g \in [set g]. by rewrite in_set1.
    rewrite -Hg in Hgin. by move/in_graph_neighborsP in Hgin.
  - move=> h /in_graph_neighborsP Hh.
    rewrite Hg in Hh. rewrite in_set1 in Hh. by move/eqP in Hh.
Qed.

Definition isInClosedNeighborhood (f g : simplex_m) :=
  (f == g) || (g \in (successors (graph cert) f)).

Lemma isInClosedNeighborhoodP (f g : simplex_m) :
  reflect (f = g \/ g \in (successors (graph cert) f)) (isInClosedNeighborhood f g).
Proof.
  apply:(iffP orP).
  - move => Hor.
    case: Hor.
    - move/eqP => Hfg. by left.
    - move=> Hgs. by right.
  - move => Hor.
    case: Hor.
    - move/eqP => Hfg. by left.
    - move=> Hgs. by right.
Qed.

Lemma isInClosedNeighborhood_neq (f g : simplex_m) :
  f != g -> reflect (g \in (successors (graph cert) f)) (isInClosedNeighborhood f g).
Proof.
  move=> Hfg.
  apply: (iffP idP).
  - move/isInClosedNeighborhoodP => Hcn.
    case: Hcn => [Heq | Hsucc].
    + move: Hfg. by rewrite Heq eq_refl.
    + by [].
  - move=> Hsucc.
    apply/isInClosedNeighborhoodP.
    by right.
Qed.

Lemma closed_neighborhood_reflexive (f : simplex_m) : 
  isInClosedNeighborhood f f.
Proof.
  apply/isInClosedNeighborhoodP. by left.
Qed.

Lemma closed_neighbordhood_symmetrical (f g : simplex_m) :
  isInClosedNeighborhood f g -> isInClosedNeighborhood g f. 
Proof.
  move/isInClosedNeighborhoodP => Hfg.
  apply/isInClosedNeighborhoodP.
  case: Hfg.
  - move=> Heq. by left.
  - move=> Hsuc. right. by rewrite Hundir.
Qed.

Lemma no_chain_of_length3 (r : simplex_m) :
  r \in ridgesOf (set_to_asc (facets cert)) -> forall f g h, 
  f \in incident_facets (set_to_asc (facets cert)) r 
  -> g \in incident_facets (set_to_asc (facets cert)) r
  -> h \in incident_facets (set_to_asc (facets cert)) r
  -> isInClosedNeighborhood f g 
  -> isInClosedNeighborhood g h 
  -> (f = g \/ g = h \/ f = h).
Proof.
  move=> Hr f g h Hfr Hgr Hhr Hfg Hgh.
  have HfacetsOf := facets_cert Hfacets.
  have Hincfac := incident_facets_cert_subset r Hfacets.
  have Hemp : facets cert != set0.
    rewrite -HfacetsOf. apply/set0Pn.
    have Hnonemp := incident_facets_subset (set_to_asc (facets cert)) r f Hfr.
    by exists f.
  have Hdimasc := dim_cert Hfacets Hemp.
  have Hrdim := ridges_card r Hfacets Hemp Hr.
  have Hrcard : #|g| = #|r|.+1.
    have/eqP Hgdim := Hfacets g (Hincfac g Hgr).
    rewrite Hrdim Hgdim. by rewrite prednK //.
  move/in_incident_facetsP in Hgr. case: Hgr => [Hgfac Hgsub].
  move/in_incident_facetsP in Hfr. case: Hfr => [Hffac Hfsub].
  move/in_incident_facetsP in Hhr. case: Hhr => [Hhfac Hhsub].
  have Hexists := (subset_cardD1_exists [finType of 'I_m] r g Hgsub Hrcard).
  case: Hexists => [i [Hig Hrgi]].
  case: (eqVneq f g) => [Hfgeq | Hfgneq].
  - by left.
  - case: (eqVneq g h) => [Hgheq | Hghneq].
    + by right; left.
    + move/(isInClosedNeighborhood_neq g h Hghneq) in Hgh.
      rewrite eq_sym in Hfgneq.
      have Hgf := closed_neighbordhood_symmetrical f g Hfg. 
      move/(isInClosedNeighborhood_neq g f Hfgneq) in Hgf.
      have Hfin : f \in graph_neighbors g i.
        apply/in_graph_neighborsP. split=>//. by rewrite -Hrgi.
      have Hhin : h \in graph_neighbors g i.
        apply/in_graph_neighborsP. split=>//. by rewrite -Hrgi.
      have Hgvert : g \in vertices (graph cert).
        rewrite HfacetsOf in Hgfac. by rewrite -(Hvert g) in Hgfac.
      have/eqP Hcard1 := graph_neighbors_card1 g Hgvert i Hig.
      move/cards1P in Hcard1. case: Hcard1 => [x Hx].
      rewrite Hx in Hfin Hhin. rewrite in_set1 in Hfin. rewrite in_set1 in Hhin.
      move/eqP in Hhin. rewrite -Hhin in Hfin. 
      by right; right; move/eqP in Hfin.
Qed.

Lemma isInClosedNeigh_is_eqrel (r : simplex_m) :
  r \in ridgesOf (set_to_asc (facets cert)) ->
  {in incident_facets (set_to_asc (facets cert)) r & &, equivalence_rel isInClosedNeighborhood}.
Proof.
  move=> Hr.
  rewrite/equivalence_rel. 
  move=> g f h HxInInc HyInInc HzInInc.
  split.
  - apply: closed_neighborhood_reflexive.
  - move=> HgRf. have HfRg := (closed_neighbordhood_symmetrical g f HgRf).
    apply/idP/idP.
    + move=> HgRh.
      have HfEgEh : (f = g \/ g = h \/ f = h).
        by apply: (no_chain_of_length3 r Hr f g h).
      case: HfEgEh.
      * move=> Hfg. by rewrite Hfg.
      * move=> HgEhEf. case: HgEhEf.
        - move=> Hgh. by rewrite -Hgh.
        - move=> Hfh. rewrite Hfh. by apply: closed_neighborhood_reflexive.
    + move=> HfRh. 
      have HfEgEh : (g = f \/ f = h \/ g = h).
        by apply: (no_chain_of_length3 r Hr g f h).
      case: HfEgEh.
      * move=> Hgf. by rewrite Hgf.
      * move=> HgEhEf. case: HgEhEf.
        - move=> Hfh. by rewrite -Hfh.
        - move=> Hgh. rewrite Hgh. by apply: closed_neighborhood_reflexive.
Qed.

Definition facets_class (r : simplex_m) (x : simplex_m) :=
  [set y in incident_facets (set_to_asc (facets cert)) r | isInClosedNeighborhood x y].

Lemma in_facets_classE (r : simplex_m) (x y : simplex_m) :
  (y \in facets_class r x) = (y \in incident_facets (set_to_asc (facets cert)) r) && isInClosedNeighborhood x y.
Proof. by rewrite inE. Qed.

Lemma in_facets_classP (r : simplex_m) (x y : simplex_m) :
  reflect (y \in incident_facets (set_to_asc (facets cert)) r /\ isInClosedNeighborhood x y)
  (y \in facets_class r x).
Proof. rewrite in_facets_classE. by apply: (iffP andP). Qed.

Lemma in_facets_class_reflexive (r : simplex_m) (x : simplex_m) :
  x \in incident_facets (set_to_asc (facets cert)) r -> x \in facets_class r x.
Proof.
  move=> Hx.
  apply/in_facets_classP. split=> //.
  by apply: closed_neighborhood_reflexive.
Qed.

Definition facetsPartition (r : simplex_m) := 
  equivalence_partition isInClosedNeighborhood (incident_facets (set_to_asc (facets cert)) r).

Lemma in_facetsPartitionP (r : simplex_m) (A : {set simplex_m}) :
  r \in ridgesOf (set_to_asc (facets cert)) -> 
  reflect (exists x, x \in incident_facets (set_to_asc (facets cert)) r /\ A = facets_class r x)
  (A \in facetsPartition r).
Proof.
  move=> Hr.
  apply: (iffP idP).
  - move=> HA. 
    rewrite /facetsPartition in HA.
    rewrite /equivalence_partition in HA.
    move/imsetP: HA => [x Hx ->].
    by exists x.
  - move=> [x [Hx HA]].
    rewrite /facetsPartition.
    rewrite /equivalence_partition.
    apply/imsetP.
    by exists x.
Qed. 

Lemma facetsPartition_partition (r : simplex_m) :
  r \in ridgesOf (set_to_asc (facets cert)) -> 
  partition (facetsPartition r) (incident_facets (set_to_asc (facets cert)) r).
Proof.
    move=> Hr.
    rewrite/facetsPartition. apply/equivalence_partitionP. 
    by apply isInClosedNeigh_is_eqrel.
Qed.

Lemma classes_card (r : simplex_m) :  
  r \in ridgesOf (set_to_asc (facets cert)) -> 
  {in (facetsPartition r), forall A : {set simplex_m}, #|A| = 2}.
Proof.
  move=> Hr A /in_facetsPartitionP HAIn.
  move: (HAIn Hr) => [x [/in_incident_facetsP [Hxf Hxr] HA]].
  have Hx : x \in incident_facets (set_to_asc (facets cert)) r.
    by apply/in_incident_facetsP.
  have Hemp : facets cert != set0.
    rewrite -(facets_cert Hfacets).
    apply/set0Pn.
    by exists x.
  have Hrcard := ridges_card r Hfacets Hemp Hr.
  have/eqP Hxcard : #|x| == d.
    apply: (Hfacets x).
    by rewrite -(facets_cert Hfacets).
  have Heqrel := isInClosedNeigh_is_eqrel r Hr.
  apply/eqP; rewrite eqn_leq; apply/andP; split.
  - have [Hle | Hgt] := leqP #|A| 2.
    + by [].
    + move/card_gt2P in Hgt. move: Hgt => [f [g [h [[HfA HgA HhA] [Hfg Hgh Hhf]]]]].
      rewrite HA in HfA HgA HhA. 
      move/in_facets_classP: HfA => [Hfi HxRf].
      move/in_facets_classP: HgA => [Hgi HxRg].
      move/in_facets_classP: HhA => [Hhi HxRh].
      rewrite (snd (Heqrel x f g Hx Hfi Hgi) HxRf) in HxRg.
      rewrite (snd (Heqrel x h f Hx Hhi Hfi) HxRh) in HxRf.
      case: (no_chain_of_length3 r Hr h f g Hhi Hfi Hgi HxRf HxRg).
      * move=> HhEf. by rewrite HhEf eq_refl in Hhf.
      * move=> Hor. case: Hor.
        - move=> HfEg. by rewrite HfEg eq_refl in Hfg.
        - rewrite eq_sym in Hgh. move=> HhEg. by rewrite HhEg eq_refl in Hgh.
  - have HxA := in_facets_class_reflexive r x Hx.
    rewrite -HA in HxA.
    have Hcard : #|x| = #|r|.+1.
      rewrite Hrcard Hxcard. by rewrite prednK.
    have Hexists := subset_cardD1_exists [finType of 'I_m] r x Hxr Hcard.
    move: Hexists=> [i [Hix Hri]].
    rewrite (facets_cert Hfacets) -(Hvert x) in Hxf.
    have [g [[Hgs Hgr] Hgu]] := (successors_unique x Hxf i Hix).
    have Hxng : x != g.
      case Hxg: (x == g).
      move/eqP in Hxg. rewrite -Hxg in Hgs.
      by move: (succxx (graph cert) x); rewrite Hgs.
      by [].
    have HgA : g \in A.
      rewrite HA. apply/in_facets_classP. split.
      + apply/in_incident_facetsP. split.
        * rewrite (facets_cert Hfacets).
          by exact: successors_subset x Hvert g Hgs.
          by rewrite -Hri in Hgr.
          by move/(isInClosedNeighborhood_neq x g Hxng) in Hgs.
    apply/card_gt1P. by exists x; exists g.
Qed.

Lemma ridges_have_even_incidence :
  ridgesHaveEvenIncidence (set_to_asc (facets cert)).
Proof.
  move=> r Hr.
  have [k Hk] : exists k, #|incident_facets(set_to_asc (facets cert)) r| = k*2.
    exists #|facetsPartition r|. by exact: (@card_uniform_partition _ 2 (facetsPartition r) (incident_facets(set_to_asc (facets cert)) r)) (classes_card r Hr) (facetsPartition_partition r Hr).
  by rewrite/even Hk muln2 odd_double. 
Qed.

End RidgesHaveEvenIncidence.

Section ConesArePointed.

Context (d : nat) (R : realFieldType).

Variable (P : 'hpoly[R]_d) (V : {fset 'cV[R]_d}).

Local Notation m := (m R d P).
Local Notation simplex_m := (simplex [finType of 'I_m]).
Local Notation Certificate := (Certificate R d P).
Local Notation facetsAreDSimplices := (facetsAreDSimplices R d P).
Local Notation full_dim_check := (full_dim_check R d P V).
Local Notation mappingHasImageInPoints := (mappingHasImageInPoints R d P V).
Local Notation feasibility_check := (feasibility_check R d P V).
Local Notation mapping_check := (mapping_check R d P).
Local Notation conesArePointed := (conesArePointed m d R).
Local Notation facets := (facets R d P).
Local Notation mapping := (mapping R d P).
Local Notation normalVector := (normalVector d R).
Local Notation coneOf := (coneOf m d R (normalVector P)).
Local Notation coneOfS := (coneOfS m d R (normalVector P)).
Local Notation active_constraints := (active_constraints d R P).
Local Notation normalCone := (normalCone d R P).
Local Notation normal_cones_are_pointed := (normal_cones_are_pointed d R P).

Variable (cert : Certificate).

Local Notation facets_cert := (facets_cert d R P cert).
Local Notation activeSets_cert := (activeSets_cert d R P V cert).
Local Notation full_dim_cert := (full_dim_cert d R P V cert).

Hypothesis Hfeas : feasibility_check cert.
Hypothesis Hfulldim : full_dim_check cert.
Hypothesis Hfacets : facetsAreDSimplices cert.
Hypothesis Hmappoint : mappingHasImageInPoints cert.
Hypothesis Hmapcheck: mapping_check cert.

Lemma cones_are_pointed :
  conesArePointed (normalVector P) (set_to_asc (facets cert)).
Proof.
  move=> f Hf.
  rewrite (facets_cert Hfacets) in Hf.
  apply: (@pointedS R d (coneOf f) (normalCone (mapping cert f))).
  apply: coneOfS.
  rewrite -(activeSets_cert Hfeas (mapping cert f) (Hmappoint f Hf)).
  exact: Hmapcheck f Hf.
  by apply: normal_cones_are_pointed (full_dim_cert Hfeas Hfulldim) (mapping cert f) ((fst Hfeas) (mapping cert f) (Hmappoint f Hf)).
Qed.

End ConesArePointed.

Section SpecialPoint.

Context (d : nat) (R : realFieldType).

Variable (P : 'hpoly[R]_d) (V : {fset 'cV[R]_d}).

Local Notation m := (m R d P).
Local Notation simplex_m := (simplex [finType of 'I_m]).
Local Notation Certificate := (Certificate R d P).
Local Notation facets := (facets R d P).
Local Notation normalVector := (normalVector d R).
Local Notation existsSpecialPoint := (existsSpecialPoint m d R).
Local Notation mappingHasImageInPoints := (mappingHasImageInPoints R d P V).
Local Notation specialSimplexInSpecialCone := (specialSimplexInSpecialCone R d P).
Local Notation weightsAreStrictlyPositiveVectors := (weightsAreStrictlyPositiveVectors R d P).
Local Notation mapping_check := (mapping_check R d P).
Local Notation inversibility_check := (inversibility_check R d P).
Local Notation separability_check := (separability_check R d P).


Variable (cert : Certificate).

Hypothesis Hmappoint : mappingHasImageInPoints cert.
Hypothesis HspecSimp : specialSimplexInSpecialCone cert.
Hypothesis Hweights : weightsAreStrictlyPositiveVectors cert.
Hypothesis Hmapcheck : mapping_check cert.
Hypothesis Hinvert : inversibility_check cert.
Hypothesis Hsep : separability_check cert.

Lemma exists_special_point :
  existsSpecialPoint (normalVector P) (set_to_asc (facets cert)).
Admitted.

End SpecialPoint.





