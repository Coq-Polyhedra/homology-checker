From mathcomp Require Import finmap all_ssreflect all_algebra.
From Polyhedra Require Import polyhedron row_submx poly_base affine.
From DepotThese Require Import high_graph.

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

Definition inc (K : asc) (tau : simplex) :=
    [set F : simplex | [&& isFacet F, F \in (simplices K) & tau \subset F]].

Definition allRidgesHaveEvenIncidence (K : asc) :=
    forall tau : simplex, tau \in (simplices K) -> isRidge tau -> 
    even #|inc K tau|.

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
    (z \in P) && [forallf F in face_set P, (\pdim F < d) ==> ~~(z \in F)].

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

Section RidgesEvenIncidence.

Context (m d : nat).

Local Notation m_graph := (graph [choiceType of (simplex m)]).

Definition isFacetsGraph (K : simplicialComplex m) (g : m_graph) :=
    forall sig, (sig \in vertices g) <-> ((sig \in (simplices m (set_to_asc m K))) && isFacet m d sig).

Definition undirected (g : m_graph) :=
    forall x y, (y \in successors g x) <-> (x \in successors g y).

Definition adjacencyProperty (g : m_graph) :=
    forall sig, (sig \in vertices g) -> forall i, (i \in sig) -> 
    exists! rho, (rho \in successors g sig) /\ (sig:\i \subset rho). 

Definition isInClosedNeigh (g : m_graph) (x y : simplex m) :=
    (y == x) || (y \in (successors g x)).

Lemma isInClosedNeigh_is_reflexive (g : m_graph) (x : simplex m) : isInClosedNeigh g x x.
Proof.
    rewrite/isInClosedNeigh. apply/orP. left. trivial.
Qed.

Lemma isInClosedNeigh_is_symmetrical (g : m_graph) (x y : simplex m) :
    (undirected g) -> (isInClosedNeigh g x y) -> (isInClosedNeigh g y x).
Proof.
    intros Hundir HxRRy.
    rewrite/isInClosedNeigh. rewrite/isInClosedNeigh in HxRRy. 
    rewrite eq_sym in HxRRy. rewrite/undirected in Hundir. 
    have Hundirxy := Hundir x y. move/orP in HxRRy. rewrite Hundirxy in HxRRy. 
    move/orP in HxRRy. exact HxRRy.
Qed.

Definition equivalence_rel_on {T : finType} (R : rel T) (A : {set T}) :=
    equivalence_rel (fun x y => (~~(x \in A) && ~~(y \in A)) || ((x \in A) && 
    (y \in A) && (R x y))).

Check proper.

Lemma ridge_is_facet_minus_vertex (tau sig : simplex m) : (tau \subset sig) ->
(#|tau| = d) -> (#|sig| = d.+1) -> (exists i, (i \in sig) /\ (tau = sig :\ i)).
Proof.
    intros. have H2 : tau \proper sig. 
        rewrite/proper. apply/andP. split.
            exact H. destruct (sig \subset tau) eqn:H2.
                simpl. have Habsurd : #|sig| <= #|tau|. 
                    apply subset_leq_card. apply H2.
                rewrite H0 in Habsurd. rewrite H1 in Habsurd. 
                rewrite ltnn in Habsurd. exact Habsurd.
            trivial.
    move/properP in H2. destruct H2. destruct H3. exists x. split.
        exact H3.
        have Hsubset : tau \subset sig:\x.
            rewrite subsetD1. apply/andP. split.
                exact H2.
                exact H4.
        apply/setP. have Hcard : #|tau| = #|sig :\ x|.
            rewrite (@cardsD1 _ x _) in H1. rewrite H3 in H1. simpl in H1.
            rewrite add1n in H1. move/eqP in H1. rewrite eqSS in H1. move/eqP in H1.
            rewrite H1. exact H0.
        apply/subset_cardP.
            exact Hcard.
            exact Hsubset.
Qed.

Lemma no_chain_of_length_3 (g : m_graph) (K : simplicialComplex m)
(tau : simplex m) : (isFacetsGraph K g) -> (undirected g) 
-> (adjacencyProperty g) -> isRidge m d tau -> forall sig1 sig2 sig3, (sig1 \in inc m d (set_to_asc m K) tau) &&
(sig2 \in inc m d (set_to_asc m K) tau) && (sig3 \in inc m d (set_to_asc m K) tau) && (isInClosedNeigh g sig1 sig2) &&
(isInClosedNeigh g sig2 sig3) -> ((sig1 == sig2) || (sig2 == sig3) || (sig1 == sig3)).
Proof.
    intros. apply/orP.
    destruct (sig1 == sig3) eqn:H5.
        right. trivial.
        left. apply/orP. destruct (sig2 == sig3) eqn:H6.
            right. trivial.
            left. move/andP in H3. destruct H3. move/andP in H3. destruct H3.
            move/andP in H3. destruct H3. move/andP in H3. destruct H3.
            rewrite/isInClosedNeigh in H7. rewrite/isInClosedNeigh in H4.
            destruct (sig1 == sig2) eqn:H11.
                trivial.
                rewrite eq_sym in H11. rewrite H11 in H7. simpl in H7.
                rewrite eq_sym in H6. rewrite H6 in H4. simpl in H4.
                rewrite/inc in H9. rewrite inE in H9. move/andP in H9.
                destruct H9. move/andP in H10. destruct H10. 
                have H14 : exists i, (i \in sig2) /\ (tau = sig2:\i).
                    rewrite/isRidge in H2. rewrite/dim in H2. 
                    rewrite/isFacet in H9. rewrite/dim in H9.
                    apply ridge_is_facet_minus_vertex.
                        exact H12.
                        move/eqP in H2. exact H2.
                        move/eqP in H9. exact H9.
                destruct H14. destruct H13.
                rewrite/inc in H8. rewrite inE in H8. move/andP in H8.
                destruct H8. move/andP in H15. destruct H15.
                rewrite/inc in H3. rewrite inE in H3. move/andP in H3.
                destruct H3. move/andP in H17. destruct H17.
                rewrite H14 in H16. rewrite H14 in H18.
                unfold adjacencyProperty in H1. have H19 := H1 sig2.
                have H20 : (forall i : ordinal_finType m, i \in sig2 ->
                exists ! rho : [choiceType of simplex m], rho \in successors g sig2 /\ 
                sig2 :\ i \subset rho).
                    apply H19.
                        rewrite/isFacetsGraph in H. have H21 := H sig2.
                        apply H21. apply/andP. split.
                            exact H10.
                            exact H9.
                have H21 := H20 x. 
                have H22 : (exists ! rho : [choiceType of simplex m], rho \in 
                successors g sig2 /\ sig2 :\ x \subset rho).
                    apply H21. exact H13.
                destruct H22. unfold unique in H22. destruct H22.
                have Hsig1 := H23 sig1.
                have Habsurd1 : x0 = sig1.
                    apply Hsig1. split.
                        rewrite/undirected in H0. have Hswitchsig1sig2 := H0 sig2 sig1.
                        apply Hswitchsig1sig2. 
                            exact H7. 
                            exact H18.
                have Hsig3 := H23 sig3.
                have Habsurd2 : x0 = sig3.
                    apply Hsig3. split.
                        exact H4.
                        exact H16.
                rewrite Habsurd1 in Habsurd2. move/eqP in Habsurd2.
                rewrite Habsurd2 in H5. rewrite <- H5. trivial.
Qed.                  

Lemma isInClosedNeigh_is_eqrel (g : m_graph) (K : simplicialComplex m) 
(tau : simplex m) : (isFacetsGraph K g) -> (undirected g) -> (adjacencyProperty g) 
-> isRidge m d tau -> {in inc m d (set_to_asc m K) tau & &, equivalence_rel (isInClosedNeigh g)}.
Proof.
    intros Hfacets Hundir Hadj Hridge.
    rewrite/equivalence_rel. intros x y z HxInInc HyInInc HzInInc.
    split.
    - apply: isInClosedNeigh_is_reflexive. 
    - intro HxRy. apply/idP/idP.
        - intro HxRz. have HxEyEz : (y == x) || (x == z) || (y == z).
            - apply: (@no_chain_of_length_3 g K tau).
                - exact Hfacets.
                - exact Hundir.
                - exact Hadj.
                - exact Hridge.
                - apply/andP. split.
                    - apply/andP. split.
                        - apply/andP. split.
                            - apply/andP. split.
                                - exact HyInInc.
                                - exact HxInInc.
                            - exact HzInInc.
                        - apply isInClosedNeigh_is_symmetrical.
                            - exact Hundir.
                            - exact HxRy.
                    - exact HxRz.
          move/orP in HxEyEz. case: HxEyEz => H.
            - move/orP in H. case: H => HxEy.
                - move/eqP in HxEy. rewrite HxEy. exact HxRz.
                - move/eqP in HxEy. rewrite <- HxEy. rewrite isInClosedNeigh_is_symmetrical.
                    - trivial.
                    - exact Hundir.
                    - exact HxRy.
                - move/eqP in H. rewrite H. apply: isInClosedNeigh_is_reflexive.
        - intro HyRz. have HxEyEz : (x == y) || (y == z) || (x == z).
            - apply: (@no_chain_of_length_3 g K tau).
                - exact Hfacets.
                - exact Hundir.
                - exact Hadj.
                - exact Hridge.
                - apply/andP. split.
                    - apply/andP. split.
                        - apply/andP. split.
                            - apply/andP. split.
                                - exact HxInInc.
                                - exact HyInInc.
                            - exact HzInInc.
                        - apply isInClosedNeigh_is_symmetrical.
                            - exact Hundir.
                            - apply: isInClosedNeigh_is_symmetrical.
                                - exact Hundir.
                                - exact HxRy.
                    - exact HyRz.
          move/orP in HxEyEz. case: HxEyEz => H.
            - move/orP in H. case: H => HyEx.
                - move/eqP in HyEx. rewrite HyEx. exact HyRz.
                - move/eqP in HyEx. rewrite <- HyEx. exact HxRy.
                - move/eqP in H. rewrite H. apply: isInClosedNeigh_is_reflexive.
Qed.

Definition facetsPartition (g : m_graph) (K : simplicialComplex m) 
(tau : simplex m) := equivalence_partition (isInClosedNeigh g) (inc m d (set_to_asc m K) tau).

Lemma facetsPartition_is_partition (g : m_graph) (K : simplicialComplex m) 
(tau : simplex m) : (isFacetsGraph K g) -> (undirected g) -> (adjacencyProperty g) 
-> isRidge m d tau -> partition (facetsPartition g K tau) (inc m d (set_to_asc m K) tau).
Proof.
    intros Hfacets Hundir Hadj Hridge.
    rewrite/facetsPartition. apply: equivalence_partitionP. apply isInClosedNeigh_is_eqrel.
    exact Hfacets. exact Hundir. exact Hadj. exact Hridge.
Qed.

Lemma equiv_classes_are_pairs (g : m_graph) (K : simplicialComplex m) 
(tau : simplex m) : (isFacetsGraph K g) -> (undirected g) -> (adjacencyProperty g) 
-> isRidge m d tau -> {in (facetsPartition g K tau), forall A : {set simplex m}, #|A| = 2}.
Proof.
    intros Hfacets Hundir Hadj Hridge.
    intro A. intro AInPart.
    have Hminor : #|A| >= 2.
        - rewrite/facetsPartition in AInPart. rewrite/equivalence_partition in AInPart.
          move/imsetP in AInPart. case: AInPart => x HxInInc HA. rewrite/inc in HxInInc.
          rewrite inE in HxInInc. move/andP in HxInInc. case: HxInInc => HxFacet Hinter.
          move/andP in Hinter. case: Hinter => HxInK HtauInx.
          have Htaux : exists i, (i \in x) /\ (tau = x :\ i).
            - apply ridge_is_facet_minus_vertex. 
                - exact HtauInx.
                - rewrite/isRidge in Hridge. rewrite/dim in Hridge. move/eqP in Hridge.
                  exact Hridge.
                - rewrite/isFacet in HxFacet. rewrite/dim in HxFacet. move/eqP in HxFacet.
                  exact HxFacet.
          case: Htaux => i Htaux. case: Htaux => HiInx Htaux.
          rewrite/adjacencyProperty in Hadj. have Hadjx := Hadj x.
          have Hadjxfi : forall i : ordinal_finType m, i \in x -> exists ! rho : 
          [choiceType of simplex m], rho \in successors g x /\ x :\ i \subset rho.
            - apply: Hadjx. rewrite/isFacetsGraph in Hfacets. have Hfacetsx := Hfacets x.
              apply Hfacetsx. apply/andP. split. exact HxInK. exact HxFacet.
          have Hadjxi := Hadjxfi i. have Hrho : exists ! rho : [choiceType of simplex m],
          rho \in successors g x /\ x :\ i \subset rho.
            - apply Hadjxi. exact HiInx.
          case: Hrho => rho HrhoUnique. rewrite/unique in HrhoUnique.
          case: HrhoUnique => HrhoE HrhoU.
          have HrhoInA : rho \in A.
            - rewrite HA. rewrite inE. apply/andP. split.
                - rewrite/inc. rewrite inE. apply/andP. split.
                    - case: HrhoE => HrhoSX HrhoTau. have Hsub_succ : successors g x `<=` vertices g.
                        - apply (@sub_succ _ g x).
                        rewrite/fsubset in Hsub_succ. rewrite/fsetI in Hsub_succ.
                        move/eqP in Hsub_succ. rewrite <- Hsub_succ in HrhoSX.
                        rewrite inE in HrhoSX. move/andP in HrhoSX.
                        case: HrhoSX => HrhoSX HrhoInV. rewrite/isFacetsGraph in Hfacets.
                        have Hfacetsrho := Hfacets rho. rewrite Hfacetsrho in HrhoInV.
                        move/andP in HrhoInV. case : HrhoInV => HrhoInS HrhoFac. exact HrhoFac.
                    - case: HrhoE => HrhoSX HrhoTau. have Hsub_succ : successors g x `<=` vertices g.
                        - apply (@sub_succ _ g x).
                        rewrite/fsubset in Hsub_succ. rewrite/fsetI in Hsub_succ.
                        move/eqP in Hsub_succ. rewrite <- Hsub_succ in HrhoSX.
                        rewrite inE in HrhoSX. move/andP in HrhoSX.
                        case: HrhoSX => HrhoSX HrhoInV. rewrite/isFacetsGraph in Hfacets.
                        have Hfacetsrho := Hfacets rho. rewrite Hfacetsrho in HrhoInV.
                        move/andP in HrhoInV. case : HrhoInV => HrhoInS HrhoFac. apply/andP. split.
                            - exact HrhoInS.
                            - rewrite <- Htaux in HrhoTau. exact HrhoTau.
                    - rewrite/isInClosedNeigh. apply/orP. right. case HrhoE => HrhoinS _.
                      exact HrhoinS.
          have HxInA : x \in A.
            - rewrite HA. rewrite inE. apply/andP. split.
                - rewrite/inc. rewrite inE. apply/andP. split.
                    - exact HxFacet.
                    - apply/andP. split.
                        - exact HxInK.
                        - rewrite Htaux. apply: subD1set.
                - apply: isInClosedNeigh_is_reflexive.
          have HxNErho : x != rho.
            - have HxNIs : x \notin successors g x.
                - apply: succxx.
              destruct (x == rho) eqn:HxErho.
                - move/eqP in HxErho. rewrite HxErho in HxNIs. case HrhoE => HrhoIns _.
                  rewrite HxErho in HrhoIns. rewrite HrhoIns in HxNIs. exact HxNIs.
                - trivial.
          apply/card_gt1P. exists x. exists rho. split.
            - exact HxInA.
            - exact HrhoInA.
            - exact HxNErho.
    have Hmajor : #|A| <= 2.
        - destruct (#|A| <= 2) eqn:HcardA.
            - trivial.
            - move/negbT in HcardA. rewrite <- ltnNge in HcardA.
          have Hxyz : exists x y z, [/\ x \in A, y \in A & z \in A] /\
          [/\ x != y, y != z & z != x].
            - apply: card_gt2P.
                - exact HcardA.
          case: Hxyz => x Hxyz. case: Hxyz => y Hxyz. case: Hxyz => z Hxyz.
          case: Hxyz => HIns HNEs. case: HIns => HxInA HyInA HzInA.
          rewrite/facetsPartition in AInPart. rewrite/equivalence_partition in AInPart. 
          move/imsetP in AInPart. case: AInPart => t tInInc HA.
          have HxEyEz : (x == y) || (y == z) || (x == z).
            - apply (@no_chain_of_length_3 g K tau).
                - exact Hfacets.
                - exact Hundir.
                - exact Hadj.
                - exact Hridge.
                - have HAP : forall w, (w \in A) -> (w \in inc m d (set_to_asc m K) tau) /\ (isInClosedNeigh g t w).
                    - intros w HwInA. rewrite HA in HwInA. rewrite inE in HwInA.
                      move/andP in HwInA. exact HwInA.
                  have HAPx := (HAP x) HxInA. have HAPy := (HAP y) HyInA. have HAPz := (HAP z) HzInA.
                  case: HAPx => HxInInc HtRx. case: HAPy => HyInInc HtRy. case: HAPz => HzInInc HtRz.
                  apply/andP. split.
                    - apply/andP. split.
                        - apply/andP. split.
                            - apply/andP. split.
                                - exact HxInInc.
                                - exact HyInInc.
                            - exact HzInInc.
                        - have HeqRel := isInClosedNeigh_is_eqrel g K tau Hfacets Hundir Hadj Hridge.
                          rewrite/equivalence_rel in HeqRel. 
                          have HeqReltxy := snd (HeqRel t x y tInInc HxInInc HyInInc) HtRx.
                          rewrite <- HeqReltxy. exact HtRy.
                    - have HeqRel := isInClosedNeigh_is_eqrel g K tau Hfacets Hundir Hadj Hridge.
                      rewrite/equivalence_rel in HeqRel. 
                      have HeqReltyz := snd (HeqRel t y z tInInc HyInInc HzInInc) HtRy.
                      rewrite <- HeqReltyz. exact HtRz.
          case: HNEs => HxNeY HyNEz HzNEx.
          move/orP in HxEyEz. case: HxEyEz => HxEyEz.
            - move/orP in HxEyEz. case: HxEyEz => HxEy.
                - move/eqP in HxEy. rewrite HxEy in HxNeY. rewrite eqxx in HxNeY.
                  simpl in HxNeY. exact HxNeY.
                - move/eqP in HxEy. rewrite HxEy in HyNEz. rewrite eqxx in HyNEz.
                  simpl in HyNEz. exact HyNEz.
            - move/eqP in HxEyEz. rewrite HxEyEz in HzNEx. rewrite eqxx in HzNEx.
              simpl in HzNEx. exact HzNEx.
    apply/eqP. rewrite eqn_leq. apply/andP. split.
        - exact Hmajor.
        - exact Hminor.
Qed.

Lemma ridges_have_even_incidence (K : simplicialComplex m) : 
(exists g : m_graph, (isFacetsGraph K g) /\ (undirected g) /\
(adjacencyProperty g)) -> allRidgesHaveEvenIncidence m d (set_to_asc m K).
Proof.
    intro Hg. case: Hg => g Hg. case: Hg => Hfacets Hg. case: Hg => Hundir Hadj.
    rewrite/allRidgesHaveEvenIncidence. intro tau.
    intros HtauInS Hridge.
    have HcardInc : exists k, #|inc m d (set_to_asc m K) tau| = k*2.
        - exists #|facetsPartition g K tau|.
            - apply (@card_uniform_partition _ 2 (facetsPartition g K tau) (inc m d (set_to_asc m K) tau)).
                - apply (equiv_classes_are_pairs g K tau Hfacets Hundir Hadj Hridge).
                - apply (facetsPartition_is_partition g K tau Hfacets Hundir Hadj Hridge).
    rewrite/even. case: HcardInc => k Hk. rewrite Hk. rewrite muln2. rewrite odd_double.
    trivial.
Qed.

End RidgesEvenIncidence.
