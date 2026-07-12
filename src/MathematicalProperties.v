From mathcomp Require Import finmap all_ssreflect all_algebra.
Import GRing.Theory Num.Theory Order.Theory.
From Polyhedra Require Import polyhedron row_submx poly_base affine barycenter inner_product vector_order lrel.
From Polyhedra Require Import hpolyhedron.
Import HPolyhedron. 
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
(* Attention : il faut l'existence d'un élément maximal. *)
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

Lemma simplices_of_dim_d_are_facets (K : simplicialComplex m) : isDRegular K -> 
forall sig : simplex m, isFacet m d sig -> sig \in simplices m (set_to_asc K) -> sig \in K.
Proof.
    intros HDreg sig HsigFac HsiginS. rewrite/set_to_asc in HsiginS.
    simpl in HsiginS. rewrite/unionPS in HsiginS. rewrite/map_cup in HsiginS.
    rewrite inE in HsiginS. move/existsP in HsiginS. case: HsiginS => x Hx.
    move/andP in Hx. case:Hx => HxInK HsigInX. rewrite/powerSet in HsigInX.
    rewrite inE in HsigInX. rewrite/isDRegular in HDreg. 
    have HxFac : isFacet m d x. exact: (HDreg x) HxInK. rewrite/isFacet in HxFac.
    rewrite/isFacet in HsigFac. rewrite/dim in HxFac. rewrite/dim in HsigFac.
    move/eqP in HxFac. rewrite -HxFac in HsigFac. have HsigEx : sig =i x.
    have Href : reflect (sig =i x) (sig \subset x). apply/subset_cardP.
    move/eqP in HsigFac. exact HsigFac. move/Href in HsigInX. exact HsigInX.
    move/setP in HsigEx. rewrite -HsigEx in HxInK. exact HxInK.
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

Section NormalCones.

Context (d : nat) (R : realFieldType).
Local Notation "'[ u , v ]" := (vdot u v).

Definition normalCone (hP : 'hpoly[R]_d) (x : 'cV[R]_d) :=
  let normal i := trmx (row i hP.`A) in
  let offset i := hP.`b i ord0 in
  cone [fset normal i | i : 'I_(hP.`c) & '[normal i , x] == offset i]%fset.

Lemma normalConeP (hP : 'hpoly[R]_d) (x c : 'cV[R]_d) :
    (x \in hP) -> reflect (x \in argmin '[hP] c) (c \in (normalCone hP x)).
Proof.
    intro HxInP. apply: (iffP idP).
    - intro HcInC. rewrite in_argmin. 
      apply/andP. split.
      - rewrite mem_mk_poly. exact HxInP.
      - rewrite poly_subset_mono. apply/poly_subsetP.
        move=> y Hy. rewrite in_hs. simpl. rewrite/normalCone in HcInC.
        move/in_coneP in HcInC. case: HcInC => w HwInPt Hcomb.
        rewrite combineE in Hcomb. rewrite Hcomb.
        rewrite vdot_sumDl. rewrite vdot_sumDl. 
        apply: ler_sum. intros i Huseless. destruct Huseless.
        rewrite vdotZl. rewrite vdotZl. case: i => ai Hai. simpl. 
        rewrite ler_pmul2l.
        move/fsubsetP in HwInPt.
        move/HwInPt in Hai. move/imfsetP in Hai. simpl in Hai.
        case: Hai => i Hi Hai. rewrite inE in Hi. move/eqP in Hi.
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
      have Hbound : polyhedron.bounded 'P(base_hpoly d R hP)%PH c.
      - rewrite -base_hpolyP. apply/boundedP. exists x. rewrite mem_mk_poly.
        exact HxInP. apply/poly_subsetP. rewrite in_argmin in HxInMin. move/andP in HxInMin.
        case:HxInMin => _ HPSubHs. move=> y Hy. rewrite -mem_polyE in Hy.
        rewrite in_hs. simpl. move/poly_subsetP in HPSubHs. have HyInHS := 
        (HPSubHs y) Hy. rewrite -mem_polyE in HyInHS. rewrite (snd (polyhedron.in_hs)) in 
        HyInHS. exact HyInHS.
      have Hdual := dual_opt_sol Hbound. case:Hdual => w HwSubBase HCombine.
      have HNonEmpt : ([ poly0 ] `<` 'P^=(base_hpoly d R hP; finsupp w))%PH.
      have HxInPEq : (x \in 'P^=(base_hpoly d R hP; finsupp w))%PH.
      - rewrite -mem_mk_poly in HxInP. rewrite base_hpolyP in HxInP.
        apply/(compl_slack_cond HwSubBase HxInP). 
        have HArgSub := argmin_opt_value Hbound. move/poly_subsetP in HArgSub.
        rewrite -HCombine in HArgSub. rewrite base_hpolyP in HxInMin.
        rewrite mem_polyE in HxInMin. have HxInComb := (HArgSub x HxInMin).
        rewrite -mem_polyE in HxInComb. rewrite (affE x) in HxInComb. exact HxInComb.
      apply/proper0P. exists x. exact HxInPEq.
      have HArgEq := (dual_sol_argmin HwSubBase HNonEmpt).
      rewrite base_hpolyP in HxInMin. rewrite HCombine in HArgEq.
      simpl in HArgEq. rewrite HArgEq in HxInMin. Locate "lrel". Locate "base_t". 
      pose p : lrel -> 'cV[R]_d := 
        fun e => let: BaseElt y := e in y.1.
      pose S0 : {fset 'cV[R]_d} :=
        [fset p e | e in finsupp w].
      pose w0_fun : {fsfun 'cV[R]_d ~> R} :=
        [fsfun a in S0 => \big[+%R/0%R]_(e <- enum_fset (finsupp w) 
        | p e == a) (val w e)].
      have Hw0con : conic w0_fun.
      - apply/conicP. intros x0 Hx0Inw0. rewrite /w0_fun in Hx0Inw0.
        have HfinSub : finsupp [fsfun a in S0 => (\sum_(e <- finsupp w | 
        p e == a) val w e)%R] `<=`S0.
        - intro useless. apply/finsupp_sub.
        have HfinSubb := HfinSub 0%R. move/fsubsetP in HfinSubb. 
        have Hx0InS0 := (HfinSubb x0 Hx0Inw0). rewrite/w0_fun. simpl. 
        rewrite fsfunE. rewrite Hx0InS0. rewrite big_seq_cond. 
        rewrite sumr_ge0. trivial. intros i Hi. move/andP in Hi.
        case: Hi => HiInFs _. have Hwconic := valP w. simpl in Hwconic.
        move/conicP in Hwconic. have HiInCon := (Hwconic i HiInFs). exact HiInCon.
      pose w0 : {conic 'cV[R]_d ~> R} := Sub w0_fun Hw0con. exists w0.
      rewrite /w0. simpl. rewrite /w0_fun. apply/fsubsetP. move=> x0 Hx0Inw0.
      apply/imfsetP. have HfinSub : finsupp [fsfun a in S0 => (\sum_(e <- finsupp w | 
      p e == a) val w e)%R] `<=`S0.
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
      rewrite HcComb. rewrite combineE. rewrite combineE.
      rewrite sum_lrel_fst_gen. simpl. Admitted.


End NormalCones.

Section PointedCones.

Context (d : nat) (R : realFieldType).
Local Notation "'[ u , v ]" := (vdot u v).
Local Notation "'[' 'hp' e  ']'" := [affine <[e]> ].
Local Notation "[ 'affine' I ]"    := (@Core.affine_of _ _ (Phant _) I%VS).
Local Notation "''[' P ]" := (@mk_poly2 _ _ P).
Local Notation "[< A , b >]" := (BaseElt (pair A b)).
Local Notation "A ^T" := (trmx A).

Arguments normalCone {d R}.
Local Notation "\pdim P" := (@adim R d (hull P)).

Definition isFullDimensional (hP : 'hpoly[R]_d) :=
    \pdim '[hP] = d.+1.

(*
Lemma pointedForCones (P : 'poly[R]_d) :
    (exists W : {fset 'cV[R]_d}, P = cone W) -> 
    ((pointed P) <-> (forall x : 'cV[R]_d, ((x \in P) && ((-x)%R \in P)) -> (x = 0%R))).
Proof.
    intro Hcone. split.
    - intro Hpointed.
*)

Lemma normal_cones_are_pointed (hP : 'hpoly[R]_d) :
    (isFullDimensional hP) -> (forall x : 'cV[R]_d, (x \in hP) -> pointed (normalCone hP x)).
Proof.
    intros HfullD x HxInP. destruct (pointed (normalCone hP x)) eqn:Hpointed.
        - trivial.
        - move/eqP in Hpointed. rewrite eqbF_neg in Hpointed.
          move/pointedPn in Hpointed. case: Hpointed => x0 Hpointed.
          case: Hpointed => d0 Hd0null Hd0InP.
          have Hmin : forall z : 'cV[R]_d, forall t : R, (z \in hP)
          -> ('[x0 + t*:d0, z] >= '[x0 + t*:d0, x])%R.
            - intros z t HzInP. have Hd0InPt := Hd0InP t.
              rewrite/normalCone in Hd0InPt. simpl in Hd0InPt.
              move/in_coneP in Hd0InPt. case: Hd0InPt => w HwInPt Hcomb.
              (* rewrite (combinewE HwInPt) in Hcomb. *)
              rewrite combineE in Hcomb. rewrite Hcomb.
              rewrite vdot_sumDl. rewrite vdot_sumDl. 
              apply: ler_sum. intros i Huseless. destruct Huseless.
              rewrite vdotZl. rewrite vdotZl. case: i => ai Hai. simpl. 
              rewrite ler_pmul2l.
              move/fsubsetP in HwInPt.
              move/HwInPt in Hai. move/imfsetP in Hai. simpl in Hai.
              case: Hai => i Hi Hai. rewrite inE in Hi. move/eqP in Hi.
              rewrite Hai. rewrite Hi.
              rewrite in_hpolyE in HzInP. rewrite/lev in HzInP.
              move/forallP in HzInP. have HzInPi := HzInP i.
              rewrite row_vdot. exact HzInPi.
              have Hwcon : conic w. exact (valP w).
              have Hwaipos : ai \in finsupp w = (0 < w ai)%R.
              apply: conic_finsuppE. exact Hwcon.
              rewrite Hwaipos in Hai. exact Hai.
          have Hnull : forall z, (z \in hP) -> '[d0, z - x] == 0%R.
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
              have HpInHP : ('[hP] `<=` [ hp [<d0, '[ d0, x]>] ]%:PH)%PH.
              - apply/poly_leP. move=> z HzInP. rewrite (polyhedron.in_hp.1.2).
                simpl. rewrite mem_mk_poly in HzInP. have Hnullz := (Hnull z) HzInP. rewrite vdotBr in Hnullz.
                rewrite subr_eq0 in Hnullz. exact Hnullz.
              have HdimHP : adim [hp [<d0, '[d0, x]>]] = d.
              - have HadimHP := (@adim_hp R d [<d0, '[d0, x]>]).
                simpl in HadimHP. rewrite -eqbF_neg in Hd0null.
                move/eqP in Hd0null. rewrite Hd0null in HadimHP. simpl in HadimHP.
                have Haff0 : ([ affine0 ] `<` [ hp [<d0, '[ d0, x]>] ])%PH.
                - apply/affine_proper0P. exists x. rewrite (snd in_hp).
                  apply/eqP. reflexivity.
                have HadimH := HadimHP Haff0. rewrite add0n in HadimH. exact HadimH.
              have HaffS : (adim (hull '[hP]) <= adim [hp [<d0, '[d0, x]>]])%N.
              - have HhullP := (hullP '[hP] [ hp [<d0, '[ d0, x]>] ]).
                rewrite HhullP in HpInHP. apply/adimS. exact HpInHP.
              rewrite HdimHP in HaffS. rewrite/isFullDimensional in HfullD.
              rewrite HfullD in HaffS. rewrite ltnn in HaffS. exact HaffS.
Qed.

Context (m : nat).
              
Definition activeSets (normals : 'I_m -> 'cV[R]_d) (b : 'cV[R]_m) (x : 'cV[R]_d) : pred 'I_m :=
    [pred i | '[normals i, x] == b i ord0].

Definition normals_mx (normals : 'I_m -> 'cV[R]_d) : 'M[R]_(m, d) :=
  (\matrix_i (fun (i : 'I_m) => trmx (normals i)) i).

Definition normalsToPoly (normals : 'I_m -> 'cV[R]_d) (b : 'cV[R]_m) :=
  hpoly_from_matrix (existT (fun k : nat => ('M[R]_(k, d) * 'cV[R]_k)%type)
  m (normals_mx normals, b)).
    
Definition facetsInActiveSets (normals : 'I_m -> 'cV[R]_d) (b : 'cV[R]_m) (K : simplicialComplex m) := 
    let P := normalsToPoly normals b in
    exists S : {fset 'cV[R]_d}, {subset S <= P} /\
    forall sig : simplex m, sig \in K -> exists x : 'cV[R]_d,
    (x \in S) && (sig \subset activeSets normals b x).

Lemma facets_are_pointed (normals : 'I_m -> 'cV[R]_d) (K : simplicialComplex m) :
    (isDRegular m d K) -> (exists b : 'cV[R]_m, (isFullDimensional (normalsToPoly normals b)) /\ facetsInActiveSets normals b K) -> 
    areFacetsPointed m d R normals (set_to_asc m K).
Proof.
    intros HDreg Hb. case: Hb => b Hb. case: Hb => Hfull Has. rewrite/areFacetsPointed. 
    intros sig HsigInS Hfacet.
    rewrite/coneOfSimplex. rewrite/facetsInActiveSets in Has. case: Has => S HS.
    case:HS => HS Has. have Hsig := Has sig.
    have HsigInK : sig \in K. apply/simplices_of_dim_d_are_facets. exact HDreg.
    exact Hfacet. exact HsigInS. have Hx := Hsig HsigInK. case: Hx => x Hx.
    move/andP in Hx. case: Hx => HxInS HsigX.
    have HconSub : (cone [fset normals i | i in 'I_m & i \in sig] `<=` 
    cone [fset normals i | i in 'I_m & i \in activeSets normals b x])%PH.
    - apply/poly_leP. move=> y Hy. move/in_coneP in Hy. case: Hy => w Hw Hcomb.
    have Hfin : finsupp w `<=` [fset normals i | i in 'I_m & i \in activeSets normals b x].
    - apply/fsubsetP. move=> z Hz. apply/imfsetP. move/fsubsetP in Hw.
        have Hwz := (Hw z) Hz. move/imfsetP in Hwz. case:Hwz => r Hr HrN. 
        exists r. simpl. simpl in Hr. rewrite inE in Hr. rewrite inE.
        move/subsetP in HsigX. exact ((HsigX r) Hr). exact HrN. apply/in_coneP.
        exists w. exact Hfin. exact Hcomb.
    have Himp := pointedS HconSub. simpl in Himp.
    have HpoinNorm : polyhedron.pointed (cone [fset normals i | i in [pred i | i \in activeSets normals b x]]).
    have HisNorm : cone [fset normals i | i in [pred i | i \in activeSets normals b x]] = 
    normalCone (normalsToPoly normals b) x.
    - rewrite/normalCone. simpl.
      have Hrew : [fset normals i | i in [pred i | i \in activeSets normals b x]] =
      [fset ((row i (normals_mx normals))^T)%R | i in [pred i | '[ (row i 
      (normals_mx normals))^T, x] == b i ord0]].
      - apply/fsetP => y. apply/imfsetP. simpl.
        case HyF: (y \in [fset ((row i (normals_mx normals))^T)%R | i in [pred i |
        '[ (row i (normals_mx normals))^T, x] == b i ord0]]).
        - move/imfsetP in HyF. simpl in HyF. case: HyF => i Hi. intro Hy.
          exists i. unfold normals_mx in Hi. move/eqP in Hi. 
          have Hmat : ((row i (\matrix_i0 (normals i0)^T))^T = normals i).
          - apply/colP. move=>j. rewrite rowK. rewrite trmxK. reflexivity.
          rewrite Hmat in Hi. rewrite/activeSets.
          change (i \in [pred i1 | '[ normals i1, x] == b i1 ord0]).
          change ('[ normals i, x] == b i ord0). apply/eqP. exact Hi.
          have Hmat : ((row i (\matrix_i0 (normals i0)^T))^T = normals i).
          - apply/colP. move=>j. rewrite rowK. rewrite trmxK. reflexivity.
          rewrite Hmat in Hy. exact Hy.
        - destruct [exists x0 : 'I_m, (x0 \in activeSets normals b x) && (y == normals x0)]
          eqn: Hdes.
          - move/existsP in Hdes. case:Hdes => i Hi. move/andP in Hi.
            case:Hi => HiAct HyNi. 
            have Habs : ((y \in [fset (row i (normals_mx normals))^T | i in 
            [pred i | '[ (row i (normals_mx normals))^T, x] == b i ord0]]) = true).
            - apply/imfsetP. exists i. simpl. apply/eqP. rewrite/normals_mx.
              have Hmat : ((row i (\matrix_i0 (normals i0)^T))^T = normals i).
              - apply/colP. move=>j. rewrite rowK. rewrite trmxK. reflexivity.
              rewrite Hmat. rewrite/activeSets in HiAct. move/eqP in HiAct. exact HiAct.
              have Hmat : ((row i (\matrix_i0 (normals i0)^T))^T = normals i).
              - apply/colP. move=>j. rewrite rowK. rewrite trmxK. reflexivity.
              rewrite Hmat. move/eqP in HyNi. exact HyNi.
            rewrite Habs in HyF. discriminate HyF.
            intro Habs. case:Habs => x0 Hx0Act HyNx0.
            have Habs2 : [exists x0, (x0 \in activeSets normals b x) && 
            (y == normals x0)] = true.
            - apply/existsP. exists x0. apply/andP. split.
              exact Hx0Act. apply/eqP. exact HyNx0.
              rewrite Hdes in Habs2. discriminate Habs2.
      congr cone. rewrite Hrew. apply/fsetP. intro.
      apply/idP/idP. intro Hx0.
      - apply/imfsetP. simpl. move/imfsetP in Hx0. case: Hx0 => i Hi1 Hi2.
        simpl in Hi1. exists i. change ('[ (row i (normals_mx normals))^T, x] == b i ord0).
        rewrite/in_mem in Hi1. simpl in Hi1. exact Hi1. exact Hi2.
      - intro Hx0. apply/imfsetP. simpl. move/imfsetP in Hx0. case: Hx0 => i Hi1 Hi2.
        simpl in Hi1. exists i. change ('[ (row i (normals_mx normals))^T, x] == b i ord0).
        rewrite/in_mem in Hi1. simpl in Hi1. exact Hi1. exact Hi2.
    rewrite HisNorm. apply/normal_cones_are_pointed. exact Hfull.
    exact: (HS x) HxInS. apply Himp. Set Printing All.
    have Hhorrible :
    is_true
    (@polyhedron.pointed R d
     (@cone R d
        (@Imfset.imfset imfset_key (ordinal_choiceType m)
           (matrix_choiceType (Num.RealField.choiceType R) d
              (Datatypes.S O))
           (fun i : ordinal m => normals i)
           (@mem_fin (Choice.eqType (ordinal_choiceType m))
              (simplPredType (ordinal m))
              (@subfinset_finpred (ordinal_choiceType m)
                 (@mem_fin
                    (Choice.eqType (ordinal_choiceType m))
                    (predPredType (ordinal m))
                    (@fin_finpred
                       (Choice.eqType (ordinal_choiceType m))
                       (pred_finpredType (ordinal_finType m))
                       (@PredOfSimpl.coerce 
                          (ordinal m)
                          (pred_of_argType (ordinal m)))))
                 (fun i : ordinal m =>
                  @in_mem (ordinal m) i
                    (@mem (ordinal m)
                       (predPredType (ordinal m))
                       (activeSets normals b x)))))
           (Phantom (mem_pred (ordinal m))
              (@mem (ordinal m) (simplPredType (ordinal m))
                 (@SimplPred (ordinal m)
                    (fun i : ordinal m =>
                     @in_mem (ordinal m) i
                       (@mem (ordinal m)
                          (predPredType (ordinal m))
                          (activeSets normals b x)))))))))
    =
    is_true
              (@polyhedron.pointed R d
                 (@cone R d
                    (@Imfset.imfset imfset_key
                       (ordinal_choiceType m)
                       (matrix_choiceType
                          (Num.RealField.choiceType R) d
                          (Datatypes.S O))
                       (fun
                          i : Choice.sort
                                (ordinal_choiceType m) =>
                        normals i)
                       (@mem_fin
                          (Choice.eqType
                             (ordinal_choiceType m))
                          (simplPredType (ordinal m))
                          (@fin_finpred
                             (Choice.eqType
                                (ordinal_choiceType m))
                             (simpl_pred_finpredType
                                (ordinal_finType m))
                             (@SimplFun 
                                (ordinal m) bool
                                (fun i : ordinal m =>
                                 @in_mem 
                                   (ordinal m) i
                                   (@mem 
                                      (ordinal m)
                                      (predPredType
                                       (ordinal m))
                                      (activeSets normals b
                                       x))))))
                       (Phantom (mem_pred (ordinal m))
                          (@mem (ordinal m)
                             (simplPredType (ordinal m))
                             (@SimplPred 
                                (ordinal m)
                                (fun i : ordinal m =>
                                 @in_mem 
                                   (ordinal m) i
                                   (@mem 
                                      (ordinal m)
                                      (predPredType
                                       (ordinal m))
                                      (activeSets normals b
                                       x))))))))).
    - simpl. congr (polyhedron.pointed). congr cone.
      apply/fsetP. intro.
      apply/idP/idP.
      - intro Hx0. apply/imfsetP. simpl. move/imfsetP in Hx0. case: Hx0 => i Hi1 Hi2.
        simpl in Hi1. exists i. change (i \in activeSets normals b x).
        rewrite/in_mem in Hi1. simpl in Hi1. exact Hi1. exact Hi2.
      - intro Hx0. apply/imfsetP. simpl. move/imfsetP in Hx0. case: Hx0 => i Hi1 Hi2.
        simpl in Hi1. exists i. change (i \in activeSets normals b x).
        rewrite/in_mem in Hi1. simpl in Hi1. exact Hi1. exact Hi2.
    rewrite Hhorrible. exact HpoinNorm.
Qed.

End PointedCones.

Section CoveringCriterion.

Context (d : nat) (R : realFieldType).

Arguments normalCone {d R}.

Theorem covering_criterion (P : 'poly[R]_d) (S : {fset 'cV[R]_d}) :
    {subset S <= P} -> ((vertex_set P) `<=` S <-> forall z : 'cV[R]_d, exists x : 'cV[R]_d, 
    (x \in S)/\ (z \in normalCone (hrepr P) x )).
Admitted.

End CoveringCriterion.

