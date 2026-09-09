From mathcomp Require Import finmap all_ssreflect all_algebra.
Import GRing.Theory Num.Theory Order.Theory.
From Polyhedra Require Import hpolyhedron row_submx inner_product polyhedron poly_base affine vector_order barycenter lrel.
From PolyhedraHirsch Require Import high_graph.
Import HPolyhedron.

Open Scope polyh_scope.

From Cert Require Import OddCoveringTheorem CoveringCriterion HighLevelCertificate VertexCriterion.

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
  move/properP: Hproper => [_ [x HxB HxA]].
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

Section RidgesHaveEvenIncidence.

Context (d : nat) (R : realFieldType).

Local Notation Certificate := (Certificate R d).

Variable (cert : Certificate).

Local Notation polytope := (polytope R d cert).
Local Notation m := polytope.`c.
Local Notation points := (points R d cert).
Local Notation simplex_m := (simplex [finType of 'I_m]).
Local Notation facetsAreDSimplices := (facetsAreDSimplices d R cert).
Local Notation graphVerticesAreFacets := (graphVerticesAreFacets d R cert).
Local Notation graphIsUndirected := (graphIsUndirected d R cert).
Local Notation graph_check := (graph_check d R cert).
Local Notation ridgesHaveEvenIncidence := (ridgesHaveEvenIncidence m).
Local Notation facets := (facets R d).
Local Notation graph := (graph R d).
Local Notation vertices_card := (vertices_card d R cert).
Local Notation facets_cardND1 := (facets_cardND1 d R cert).
Local Notation facets_regular := (facets_regular d R cert).
Local Notation facets_cert := (facets_cert d R cert).
Local Notation incident_facets_cert_subset := (incident_facets_cert_subset d R cert).
Local Notation dim_cert := (dim_cert d R cert).
Local Notation ridges_card := (ridges_card d R cert).
Local Notation successors_subset := (successors_subset d R cert).

Hypothesis Hdim : d >= 1.
Hypothesis Hfacets : facetsAreDSimplices.
Hypothesis Hvert   : graphVerticesAreFacets.
Hypothesis Hgraph  : graph_check.
Hypothesis Hundir : graphIsUndirected.

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

Local Notation Certificate := (Certificate R d).

Variable (cert : Certificate).

Local Notation polytope := (polytope R d cert).
Local Notation m := polytope.`c.
Local Notation points := (points R d cert).
Local Notation simplex_m := (simplex [finType of 'I_m]).
Local Notation facetsAreDSimplices := (facetsAreDSimplices d R cert).
Local Notation full_dim_check := (full_dim_check d R cert).
Local Notation mappingHasImageInPoints := (mappingHasImageInPoints d R cert).
Local Notation feasibility_check := (feasibility_check d R cert).
Local Notation mapping_check := (mapping_check d R cert).
Local Notation conesArePointed := (conesArePointed m d R).
Local Notation facets := (facets R d).
Local Notation mapping := (mapping R d).
Local Notation normalVector := (normalVector d R).
Local Notation coneOf := (coneOf m d R (normalVector polytope)).
Local Notation coneOfS := (coneOfS m d R (normalVector polytope)).
Local Notation active_constraints := (active_constraints d R polytope).
Local Notation normalCone := (normalCone d R polytope).
Local Notation normal_cones_are_pointed := (normal_cones_are_pointed d R polytope).
Local Notation facets_cert := (facets_cert d R cert).
Local Notation activeSets_cert := (activeSets_cert d R cert).
Local Notation full_dim_cert := (full_dim_cert d R cert).

Hypothesis Hfeas : feasibility_check.
Hypothesis Hfulldim : full_dim_check.
Hypothesis Hfacets : facetsAreDSimplices.
Hypothesis Hmappoint : mappingHasImageInPoints.
Hypothesis Hmapcheck: mapping_check.

Lemma cones_are_pointed :
  conesArePointed (normalVector polytope) (set_to_asc (facets cert)).
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

Local Notation Certificate := (Certificate R d).

Variable (cert : Certificate).

Local Notation polytope := (polytope R d cert).
Local Notation m := polytope.`c.
Local Notation points := (points R d cert).
Local Notation simplex_m := (simplex [finType of 'I_m]).
Local Notation facets := (facets R d).
Local Notation mapping := (mapping R d).
Local Notation activeSets := (activeSets R d).
Local Notation specialSimplex := (specialSimplex R d).
Local Notation specialVertex := (specialVertex R d).
Local Notation witnesses := (witnesses R d).
Local Notation weights := (weights R d).
Local Notation normalVector := (normalVector d R).
Local Notation existsSpecialPoint := (existsSpecialPoint m d R).
Local Notation mappingHasImageInPoints := (mappingHasImageInPoints d R).
Local Notation specialSimplexInSpecialCone := (specialSimplexInSpecialCone d R).
Local Notation weightsAreStrictlyPositiveVectors := (weightsAreStrictlyPositiveVectors d R).
Local Notation mapping_check := (mapping_check d R).
Local Notation inversibility_check := (inversibility_check d R).
Local Notation feasibility_check := (feasibility_check d R).
Local Notation separability_check := (separability_check d R).
Local Notation facetsAreDSimplices := (facetsAreDSimplices d R).
Local Notation coneOf := (coneOf m d R (normalVector polytope)).
Local Notation coneOfS := (coneOfS m d R (normalVector polytope)).
Local Notation normalsOfS := (normalsOfS m d R (normalVector polytope)).
Local Notation coneOf_subset := (coneOf_subset m d R (normalVector polytope)).
Local Notation normalsOf := ((normalsOf m d R (normalVector polytope))).
Local Notation normalCone := (normalCone d R polytope).
Local Notation in_normalConeP := (in_normalConeP d R polytope).
Local Notation isKGeneric := (isKGeneric m d R (normalVector polytope)).
Local Notation inversibility_cert := (inversibility_cert d R cert).
Local Notation activeSets_cert := (activeSets_cert d R cert).
Local Notation facets_cert := (facets_cert d R cert).

Hypothesis Hfacets : facetsAreDSimplices cert.
Hypothesis Hfeas : feasibility_check cert.
Hypothesis Hmappoint : mappingHasImageInPoints cert.
Hypothesis HspecSimp : specialSimplexInSpecialCone cert.
Hypothesis Hweights : weightsAreStrictlyPositiveVectors cert.
Hypothesis Hmapcheck : mapping_check cert.
Hypothesis Hinvert : inversibility_check cert.
Hypothesis Hsep : separability_check cert.

Definition zstar : 'cV[R]_d :=
  \sum_(i < d) (\col_k (polytope.`A (specialSimplex cert i) k))%R.

Lemma specVert_is_maximizer :
  (specialVertex cert) \in argmin '[polytope] zstar.
Proof.
  rewrite in_argmin.
  have HspecVertInV : specialVertex cert \in points.
    rewrite -(snd HspecSimp). by apply/Hmappoint; apply (fst HspecSimp).
  apply/andP. split=>//.
  rewrite -(snd HspecSimp).
  have HspecSimpInV : mapping cert ((specialSimplex cert) @: 'I_d) \in points.
    by rewrite (snd HspecSimp).
  rewrite mem_mk_poly. by apply: (fst Hfeas) (mapping cert ((specialSimplex cert) @: 'I_d)) HspecSimpInV.
  apply/poly_subset_hsP. move=> x Hx.
  simpl. rewrite vdot_sumDl. rewrite vdot_sumDl.
  apply: ler_sum=> i _.
  have Hact : ((specialSimplex cert) @: 'I_d) \subset activeSets cert (specialVertex cert).
    rewrite -(snd HspecSimp). apply/Hmapcheck. by apply: (fst HspecSimp).
  have HactSpecVert := (snd Hfeas) (specialVertex cert) HspecVertInV.
  rewrite HactSpecVert in Hact. move/subsetP in Hact.
  have HspecSimpli : specialSimplex cert i \in [set specialSimplex cert x | x : 'I_d].
    by apply/imsetP; exists i.
  have Hacti := Hact (specialSimplex cert i) HspecSimpli.
  rewrite inE in Hacti. move/eqP in Hacti.
  have Hrew : normalVector polytope (specialSimplex cert i) = (\col_k polytope.`A (specialSimplex cert i) k)%R.
    rewrite/normalVector. by apply/matrixP => k j; rewrite !mxE.
  rewrite -Hrew Hacti. rewrite mem_mk_poly in_hpolyE in Hx.
  move/forallP in Hx. have Hxi := Hx (specialSimplex cert i).
  rewrite/normalVector. by rewrite -row_vdot in Hxi.
Qed.

Lemma maximizer_is_unique :
  forall x, x \in argmin '[polytope] zstar -> x = (specialVertex cert).
Proof.
  move=> x Hx.
  have HspecVertInV : specialVertex cert \in points.
    rewrite -(snd HspecSimp). by apply/Hmappoint; apply (fst HspecSimp).
  have HsVInS := (fst Hfeas) (specialVertex cert) HspecVertInV.
  rewrite -mem_mk_poly in HsVInS.
  rewrite in_argmin in Hx. move/andP : Hx => [HxP /poly_subset_hsP Hhs].
  have Heq : ('[ zstar, x] = '[ zstar, specialVertex cert])%R.
  apply/eqP. rewrite eq_le. apply/andP; split=>//.
  - by have HhsSv := Hhs (specialVertex cert) HsVInS; simpl in HhsSv.
  - have HsV := specVert_is_maximizer.
    rewrite in_argmin in HsV. move/andP : HsV => [_ /poly_subset_hsP HhssV].
    by have Hhsx := HhssV x HxP; simpl in Hhsx.
  move/eqP in Heq. rewrite -subr_eq0 in Heq. move/eqP in Heq. rewrite -vdotBr in Heq.
  rewrite vdot_sumDl in Heq.
  have Hpos : forall i, (0 <= '[ \col_k polytope.`A (specialSimplex cert i) k, x - specialVertex cert])%R.
    move=>i. rewrite vdotBr subr_ge0.
    have Hact : ((specialSimplex cert) @: 'I_d) \subset activeSets cert (specialVertex cert).
    rewrite -(snd HspecSimp). apply/Hmapcheck. by apply: (fst HspecSimp).
    have HactSpecVert := (snd Hfeas) (specialVertex cert) HspecVertInV.
    rewrite HactSpecVert in Hact. move/subsetP in Hact.
    have HspecSimpli : specialSimplex cert i \in [set specialSimplex cert x | x : 'I_d].
      by apply/imsetP; exists i.
    have Hacti := Hact (specialSimplex cert i) HspecSimpli.
    rewrite inE in Hacti. move/eqP in Hacti.
    have Hrew : normalVector polytope (specialSimplex cert i) = (\col_k polytope.`A (specialSimplex cert i) k)%R.
    rewrite/normalVector. by apply/matrixP => k j; rewrite !mxE.
    rewrite -Hrew Hacti. rewrite mem_mk_poly in_hpolyE in HxP.
    move/forallP in HxP. have Hxi := HxP (specialSimplex cert i).
    rewrite/normalVector. by rewrite -row_vdot in Hxi.
  have HeqT : forall i : 'I_d, '[ \col_k polytope.`A (specialSimplex cert i) k, x - specialVertex cert]%R = 0%R.
    move=> i.
     have HeqTB := (@psumr_eq0P R [finType of 'I_d] predT (fun i =>
    ('[\col_k polytope.`A (specialSimplex cert i) k, x - specialVertex cert])%R)).
    apply: HeqTB. move=> j _. by apply: Hpos j.
    by change ((\sum_i '[\col_k polytope.`A (specialSimplex cert i) k, x - specialVertex cert])%R = 0%R).
    by [].
  have Horth : (x - specialVertex cert)%R \in (<<[seq (\col_k (polytope.`A (specialSimplex cert i) k))%R | i <- enum 'I_d]>>^OC)%VS.
    apply/orthv_spanP. move=>y /mapP [i HiId Hyi].
    rewrite Hyi. by apply: HeqT i.
  have Hdimfree : \dim <<[seq (\col_k polytope.`A (specialSimplex cert i) k)%R | i <- enum 'I_d]>> = d.
    have Hfree := inversibility_cert Hinvert.
    move/eqP in Hfree. by rewrite size_map size_enum_ord in Hfree.
  have Hdim : \dim (<<[seq (\col_k (polytope.`A (specialSimplex cert i) k))%R | i <- enum 'I_d]>>^OC)%VS = 0.
    rewrite dim_orthv. rewrite Hdimfree. apply: subnn. 
  move/eqP in Hdim. rewrite dimv_eq0 in Hdim. move/eqP in Hdim.
  rewrite Hdim in Horth. rewrite memv0 in Horth.
  rewrite subr_eq0 in Horth. by move/eqP in Horth.
Qed.

Lemma zstar_in_specialCone :
  zstar \in coneOf (specialSimplex cert @: 'I_d).
Proof.
  apply/in_coneOfP.
  pose w0 : {fsfun 'cV[R]_d ~> R} := [fsfun x in normalsOf [set specialSimplex cert i | i : 'I_d] => 1%R].
  have Hw0 : conic w0.
    apply/conicwP => y.
    rewrite fsfunE.
    case: ifP => _.
    - exact: ler01.
    - by [].
  pose w : {conic 'cV[R]_d ~> R} := @mkConicFun _ _ w0 Hw0.
  exists w.
  have Hwsub : (finsupp w `<=` normalsOf [set specialSimplex cert x | x : 'I_d])%fset.
    apply/fsubsetP => y Hy.
    apply/in_normalsOfP. rewrite mem_finsupp /w /w0 /= fsfunE in Hy.
    have HyN : y \in normalsOf [set specialSimplex cert i | i : 'I_d].
      move: Hy. case: ifP => HyN.
      + by move=> _.
      + by rewrite eqxx.
    by move/in_normalsOfP in HyN. 
  split=>//. rewrite (combinewE Hwsub).
  have Hnormal i : (\col_k polytope.`A (specialSimplex cert i) k)%R \in
  normalsOf [set specialSimplex cert x | x : 'I_d].
  apply/in_normalsOfP. exists (specialSimplex cert i). split=>//.
  - apply/imsetP. exists i. by []. by [].
  - rewrite/normalVector. by apply/matrixP => k j; rewrite !mxE.
  have Huniq := free_uniq (inversibility_cert Hinvert).
  pose nvec := fun i : 'I_d => (\col_k polytope.`A (specialSimplex cert i) k)%R.
  have Hnvec_inj : injective nvec.
    move=> i j Hij.
    have Hsize : size [seq (\col_k polytope.`A (specialSimplex cert i) k)%R | i <- enum 'I_d] = d.
      by rewrite size_map size_enum_ord.
    have Hisize : i < size [seq (\col_k polytope.`A (specialSimplex cert i) k)%R | i <- enum 'I_d].
      by rewrite Hsize.
    have Hjsize : j < size [seq (\col_k polytope.`A (specialSimplex cert i) k)%R | i <- enum 'I_d].
      by rewrite Hsize.
    apply: val_inj. apply/eqP.
    rewrite -(@nth_uniq _ 0%R [seq (\col_k polytope.`A (specialSimplex cert i) k)%R | i <- enum 'I_d] i j Hisize Hjsize Huniq).
    apply/eqP.
    have Henum (k : 'I_d) : val k < size (enum 'I_d). 
      rewrite size_enum_ord. by apply: ltn_ord.
    rewrite (@nth_map 'I_d i 'cV[R]_d 0%R  nvec (val i) (enum 'I_d) (Henum i)).
    rewrite (@nth_map 'I_d i 'cV[R]_d 0%R  nvec (val j) (enum 'I_d) (Henum j)).
    by rewrite !nth_ord_enum.
  pose phi : 'I_d -> normalsOf [set specialSimplex cert x | x : 'I_d] :=
    fun i => Sub (nvec i) (Hnormal i).
  have Hphi_inj : injective phi.
    move=> i j Hij. 
    apply: Hnvec_inj. have Hval := congr1 (fun x => val x) Hij.
    exact Hval.
  have Hphi_surj : forall y, exists i : 'I_d, phi i == y.
    move=> y. have Hy := valP y. move/in_normalsOfP in Hy.
    case: Hy => [i [Hi Hyi]]. move/imsetP: Hi => [j Hj Hij].
    exists j. apply/eqP. apply: val_inj. rewrite Hyi. rewrite/phi. simpl.
    rewrite/nvec. rewrite/normalVector. rewrite Hij. by apply/matrixP => k l; rewrite !mxE.
  pose psi := fun y => xchoose (Hphi_surj y).
  have Hphi_psi : forall y, phi (psi y) = y.
    move=> y. apply/eqP. change (phi (xchoose (Hphi_surj y)) == y).
    exact: xchooseP (Hphi_surj y).
  have Hpsi_phi : forall i, psi (phi i) = i.
    move=> i. apply: Hphi_inj. exact: Hphi_psi (phi i).
  have Hphi_bij : bijective phi.
    apply: (@Bijective _ _ phi psi).
    - exact: Hpsi_phi.
    - exact: Hphi_psi.
  have Hphi_bij_on : {on [pred i | predT i], bijective phi}.
    exact: onW_bij _ Hphi_bij.
  rewrite (reindex phi Hphi_bij_on). simpl.
  apply:eq_bigr=> i _.
  rewrite fsfunE. rewrite (Hnormal i). 
  by rewrite scale1r.
Qed.  

Lemma zstar_notin_other_cones :
  forall f, f \in facets cert -> f != (specialSimplex cert @: 'I_d) -> zstar \notin coneOf f.
Proof.
  move=> f Hffac Hfspec.
  case: (mapping cert f =P specialVertex cert).
  - move=> Hfmap.
    pose qf := (witnesses cert *m (weights cert f))%R.
    have Hcone : forall y, y \in coneOf f -> ('[y,qf] <= 0)%R.
      move=>y /in_coneOfP [w [Hfsw Hcomb]].
      rewrite (combinewE Hfsw) in Hcomb. rewrite Hcomb.
      rewrite vdot_sumDl. 
      have Hle : ((\sum_(i : normalsOf f) '[w (fsval i) *: fsval i, qf])%R <=
      (\sum_(i : normalsOf f) (0%R : R))%R)%R.
      apply: ler_sum => x _.
      rewrite vdotZl. apply: mulr_ge0_le0.
      apply:ge0_fconic.
      rewrite vdotC. have Hfsvalx := fsvalP x.
      move/in_normalsOfP: Hfsvalx => [i [Hif Hfv]].
      rewrite Hfv. by apply: Hsep.
      rewrite [(\sum_(i : normalsOf f) (0%R : R))%R]big1 in Hle.
      exact Hle. by move=> _ _.
    have Hzstar : ('[zstar, qf] > 0)%R.
      rewrite vdot_sumDl. 
      have Hmul : (witnesses cert *m (weights cert f))%R = (\sum_(i < d) ((weights cert f i ord0) *: col i (witnesses cert)))%R.
        apply/matrixP => i j. rewrite !mxE. rewrite summxE. apply eq_bigr => k _.
        rewrite !mxE. rewrite mulrC. have Hj : j = ord0. by apply/ord1.
        by rewrite Hj.
      have Hscal i : ('[ \col_k polytope.`A (specialSimplex cert i) k, qf] = weights cert f i ord0 * '[\col_k polytope.`A (specialSimplex cert i) k, col i (witnesses cert)])%R.
        rewrite/qf Hmul. rewrite vdot_sumDr. rewrite -vdotZr. rewrite (bigD1 i) //=.
        have Hnull : (\sum_(i0 < d | i0 != i) '[ \col_k polytope.`A (specialSimplex cert i) k, weights cert f i0 ord0 *:
        col i0 (witnesses cert)] = 0)%R.
        apply: big1 => j Hj. have Hsepji := (Hinvert i j).
        case Hsepji.
        + move=> [Habs _]. move/eqP in Habs. rewrite eq_sym in Habs. move/eqP in Habs. by move/eqP: Hj.
        + move=> [_ Hsc]. rewrite vdotZr. rewrite Hsc. by rewrite mulr0.
        rewrite Hnull. by rewrite GRing.addr0.
      have [/forallP Hwpos Hwnul] := Hweights f Hfmap Hfspec.
      have Hcoord : [exists i : 'I_d, weights cert f i ord0 != 0%R].
        rewrite -(negbK ([exists i : 'I_d, weights cert f i ord0 != 0%R])).
        rewrite negb_exists. 
        apply (@contra ([forall x, ~~ (weights cert f x ord0 != 0%R)]) (weights cert f == 0%R)).
        move/forallP => Hforall. apply/eqP. apply/matrixP => i j.
        have Hj : j = ord0. by apply/ord1. rewrite Hj.
        have Hi := Hforall i. rewrite negbK in Hi. rewrite mxE. by apply/eqP.
        by move/eqP in Hwnul.
      move/existsP: Hcoord => [i Hi].
      rewrite (bigD1 i). simpl.
      rewrite (Hscal i). 
      have Hpos : (\sum_(i0 < d | i0 != i) '[ \col_k polytope.`A (specialSimplex cert i0) k, qf] >= 0)%R.
        apply: sumr_ge0. move=> j Hij.
        rewrite (Hscal j). apply: mulr_ge0. have Hwposj := Hwpos j. by rewrite mxE in Hwposj.
        case: (Hinvert j j). 
        + move=> [_ Hsc].  by exact: ltW Hsc.
        + by move=> [Habs _].
      have Hspos : (weights cert f i ord0 * '[ \col_k polytope.`A (specialSimplex cert i) k, col i (witnesses cert)] > 0)%R.
      + apply:mulr_gt0. have Hwposi := Hwpos i. rewrite mxE in Hwposi.
        rewrite lt_neqAle. apply/andP. split=>//. by rewrite eq_sym.
      + case: (Hinvert i i).
        * by move=> [_ Hsc].
        + by move=> [Habs _].
      have Hres := (@ltr_le_add R 0%R (weights cert f i ord0 * '[ \col_k polytope.`A (specialSimplex cert i) k, col i (witnesses cert)])%R
      0%R (\sum_(i0 < d | i0 != i) '[ \col_k polytope.`A (specialSimplex cert i0) k, qf])%R) Hspos Hpos.
      by rewrite add0r in Hres. by [].
    case Hin: (zstar \in coneOf f).
    have Hconezstar := Hcone zstar Hin. rewrite ltNge in Hzstar. by move/negP in Hzstar. by []. 
  - move=> Hfmap.
    have Hsubset : coneOf f `<=` normalCone (mapping cert f).
      apply: coneOfS. 
      rewrite -(activeSets_cert Hfeas (mapping cert f) (Hmappoint f Hffac)).
      by exact: Hmapcheck f Hffac.
    case Hin: (zstar \in coneOf f).
    + move/poly_subsetP in Hsubset. 
      have Hsubsetzstar := Hsubset zstar Hin.
      rewrite -mem_polyE in Hsubsetzstar.
      have HmapfInP := (fst Hfeas) (mapping cert f) (Hmappoint f Hffac).
      move/(in_normalConeP (mapping cert f) zstar HmapfInP) in Hsubsetzstar.
      by have Habs := maximizer_is_unique (mapping cert f) Hsubsetzstar.
    + by [].
Qed.

Lemma zstar_is_dgeneric :
  isKGeneric (set_to_asc (facets cert)) (d.+1) zstar.
Proof.
  move=> f Hf Hfdim.
  case Hin : (zstar \in coneOf f).
  - move/in_set_to_ascP: Hf => [g [Hg Hfg]].
    have/poly_subsetP Hsub := coneOfS f g Hfg.
    have Hzsin := Hsub zstar Hin. rewrite -mem_polyE in Hzsin.
    have Hgs : g = specialSimplex cert @: 'I_d.
      case: (g =P (specialSimplex cert @: 'I_d)) => Hcase.
      + by [].
      + move/eqP in Hcase.
        have Habs := zstar_notin_other_cones g Hg Hcase.
        by rewrite Hzsin in Habs.
    rewrite Hgs in Hfg.
    have Hex : [exists i : 'I_d, normalVector polytope (specialSimplex cert i) \notin (normalsOf f)].
      rewrite -(negbK ([exists i : 'I_d, normalVector polytope (specialSimplex cert i) \notin (normalsOf f)])).
      rewrite negb_exists. 
      apply (@contra ([forall x, ~~ (normalVector polytope (specialSimplex cert x) \notin normalsOf f)]) (\pdim (coneOf f) == d.+1)).
      move/forallP => Hforall.
      have Heq : normalsOf f = normalsOf [set specialSimplex cert x | x : 'I_d].
        apply/fsetP => y. apply/idP/idP.
        - move=> Hy. have/fsubsetP Hsubs := normalsOfS f [set specialSimplex cert x | x : 'I_d] Hfg.
          exact: Hsubs y Hy.
        - move=> Hy. move/in_normalsOfP: Hy => [i [Hi Hyi]]. move/imsetP: Hi => [j Hjd Hij].
          rewrite Hij in Hyi. rewrite Hyi. have Hforallj := Hforall j. by rewrite negbK in Hforallj.
      rewrite/coneOf. rewrite Heq. rewrite eq_le. apply/andP; split=>//.
      + apply: adim_leSn.
      + pose X := [seq (\col_k polytope.`A (specialSimplex cert i) k)%R | i <- enum 'I_d].
        have Hdimfree : \dim <<X>> = d.
          have Hfree := inversibility_cert Hinvert.
          move/eqP in Hfree. by rewrite size_map size_enum_ord in Hfree.
        have Hseq : ([seq (x-0)%R | x <- X] = [seq x | x <- X])%VS.
            apply eq_map => x. by rewrite subr0.
        have Hdir : dir [affine <<[seq (x-0)%R | x <- X]>> & 0%R] = <<X>>%VS.
          rewrite dir_mk_affine. rewrite Hseq. by rewrite map_id.
        have Hadim : adim [affine <<[seq (x-0)%R | x <- X]>> & 0%R] = (\dim <<X>>).+1.
          rewrite -Hdir. apply: adimN0_eq. by apply: mk_affine_proper0.
        rewrite Hdimfree in Hadim. rewrite -Hadim.
        apply: dim_sub_affine.
        + apply: zero_coneOf.
        + move=> x Hx.
          move/mapP: Hx => [i Hi Hij].
          have Hx : x \in normalsOf [set specialSimplex cert x0 | x0 : 'I_d].
            apply/in_normalsOfP. exists (specialSimplex cert i). split=>//.
            apply/imsetP. exists i. by rewrite inE. by [].
            have Hrew : normalVector polytope (specialSimplex cert i) = (\col_k polytope.`A (specialSimplex cert i) k)%R.
            rewrite/normalVector. by apply/matrixP => k j; rewrite !mxE.
            by rewrite Hrew.
          by exact: coneOf_subset ([set specialSimplex cert x0 | x0 : 'I_d]) x Hx.
        case Hdimcone : (\pdim (coneOf f) == d.+1).
        + move/eqP in Hdimcone. rewrite Hdimcone in Hfdim. by rewrite ltnn in Hfdim.
        + by [].
    move/existsP: Hex => [k Hk]. 
    have Hforall : forall y, y \in coneOf f -> ('[y, col k (witnesses cert)] = 0)%R.
      move=> y Hy.
      move/in_coneOfP: Hy => [w [Hfin Hcomb]].
      rewrite combineE in Hcomb. rewrite Hcomb. rewrite vdot_sumDl.
      apply: big1 => i _. rewrite vdotZl. move/fsubsetP in Hfin. 
      have HvalP := Hfin (fsval i) (fsvalP i).
      have/fsubsetP Hsubset := normalsOfS f [set specialSimplex cert x | x : 'I_d] Hfg.
      have Hval := Hsubset (fsval i) HvalP.
      move/in_normalsOfP: Hval => [j [Hjf Hfsval]].
      move/imsetP: Hjf => [l Hl Hjl]. rewrite Hjl in Hfsval.
      have Hrew : normalVector polytope (specialSimplex cert l) = (\col_k polytope.`A (specialSimplex cert l) k)%R.
        rewrite/normalVector. by apply/matrixP => o p; rewrite !mxE.
      have/eqP Hdiff : l != k.
        case Heq: (l == k).
        + move/eqP in Heq. rewrite Heq in Hfsval. rewrite Hfsval in HvalP. 
          by rewrite HvalP in Hk.
        + by [].
      have Hnull : ('[fsval i, col k (witnesses cert)] = 0)%R.
        rewrite Hfsval. rewrite Hrew. case: (Hinvert l k).
        + move=> [Habs _]. move/eqP in Habs. move/eqP in Hdiff. by rewrite Habs in Hdiff.
        + by move=> [_ Hscal].
      rewrite Hnull. by rewrite mulr0.
    have Hzstar : ('[ zstar, col k (witnesses cert)] > 0)%R.
      have Hsimpl : ('[ zstar, col k (witnesses cert)] = '[\col_i (polytope.`A (specialSimplex cert k) i), (col k (witnesses cert))])%R.
        rewrite vdot_sumDl. rewrite (bigD1 k) //. simpl.
        have Hnull : (\sum_(i < d | i != k) '[ \col_k0 polytope.`A (specialSimplex cert i) k0, 
        col k (witnesses cert)] = 0)%R.
        apply: big1 => i Hi. move/eqP in Hi. case: (Hinvert i k).
        + move=> [Habs _]. move/eqP in Habs. move/eqP in Hi. by rewrite Habs in Hi.
        + by move=> [_ Hscal].
        rewrite Hnull. by rewrite addr0.
      have Hpos : ('[ \col_i polytope.`A (specialSimplex cert k) i, col k (witnesses cert)] > 0)%R.
        case: (Hinvert k k).
        + by move=> [_ Hscal].
        + move=> [Habs _]. move/eqP in Habs. by rewrite eqxx in Habs.
      by rewrite Hsimpl.
    have Hforallz := (Hforall zstar) Hin.
    rewrite Hforallz in Hzstar. by rewrite ltxx in Hzstar.
  - by [].
Qed.

Lemma exists_special_point :
  existsSpecialPoint (normalVector polytope) (set_to_asc (facets cert)).
Proof.
  exists zstar. split.
  - exact: zstar_is_dgeneric.
  - have Hsing : [set F in facetsOf (set_to_asc (facets cert)) | zstar \in coneOf F] = [set (specialSimplex cert @: 'I_d)].
      apply/setP => x. apply/idP/idP.
      + move=> Hx. rewrite inE in Hx. move/andP: Hx => [Hxf Hzx].
        case Heqx: (x == (specialSimplex cert @: 'I_d)).
        * by rewrite in_set1.
        * rewrite (facets_cert Hfacets) in Hxf.
          have Hneq : x != [set specialSimplex cert x | x : 'I_d]. by rewrite /negb Heqx.
          have Habs := zstar_notin_other_cones x Hxf Hneq. by rewrite Hzx in Habs.
      + move=> Hx. rewrite inE. apply/andP. split.
        rewrite in_set1 in Hx. move/eqP in Hx. rewrite Hx. rewrite (facets_cert Hfacets).
        exact: (fst HspecSimp). rewrite in_set1 in Hx. move/eqP in Hx. rewrite Hx.
        exact: zstar_in_specialCone.
    rewrite Hsing. rewrite cards1.
    by [].
Qed.

End SpecialPoint.

Section CertificateCompleteness.

Context (d : nat) (R : realFieldType).

Local Notation Certificate := (Certificate R d).

Variable (cert : Certificate). 

Local Notation polytope := (polytope R d cert).
Local Notation m := polytope.`c.
Local Notation points := (points R d cert).
Local Notation facetsAreDSimplices := (facetsAreDSimplices d R).
Local Notation mappingHasImageInPoints := (mappingHasImageInPoints d R).
Local Notation graphVerticesAreFacets := (graphVerticesAreFacets d R ).
Local Notation graphIsUndirected := (graphIsUndirected d R).
Local Notation specialSimplexInSpecialCone := (specialSimplexInSpecialCone d R).
Local Notation weightsAreStrictlyPositiveVectors := (weightsAreStrictlyPositiveVectors d R).
Local Notation full_dim_check := (full_dim_check d R).
Local Notation feasibility_check := (feasibility_check d R).
Local Notation mapping_check := (mapping_check d R).
Local Notation graph_check := (graph_check d R).
Local Notation inversibility_check := (inversibility_check d R).
Local Notation separability_check := (separability_check d R).
Local Notation normalVector := (normalVector d R).
Local Notation facets := (facets R d).
Local Notation mapping := (mapping R d).
Local Notation specialSimplex := (specialSimplex R d).
Local Notation odd_covering_theorem := (odd_covering_theorem m d R (normalVector polytope)).
Local Notation ridges_have_even_incidence := (ridges_have_even_incidence d R cert).
Local Notation cones_are_pointed := (cones_are_pointed d R cert).
Local Notation exists_special_point := (exists_special_point d R cert).
Local Notation dim_cert := (dim_cert d R).
Local Notation facets_cert := (facets_cert d R).
Local Notation cone_subset_cert := (cone_subset_cert d R).
Local Notation full_dim_point := (full_dim_point R d cert).

Hypothesis Hdim : d > 0.
Hypothesis Hnormals : forall i : 'I_m, (normalVector polytope i <> 0)%R.

Definition well_formedness_check_completeness :=
  facetsAreDSimplices cert /\ 
  mappingHasImageInPoints cert /\ 
  graphVerticesAreFacets cert /\ 
  graphIsUndirected cert /\ 
  specialSimplexInSpecialCone cert /\
  weightsAreStrictlyPositiveVectors cert.

Definition check_certificate_completeness :=
  well_formedness_check_completeness /\ 
  full_dim_check cert /\ 
  feasibility_check cert /\ 
  mapping_check cert /\ 
  graph_check cert /\ 
  inversibility_check cert /\ 
  separability_check cert.

Theorem certificate_completeness :
  check_certificate_completeness -> ((vertex_set '[polytope]) `<=` points)%fset /\ compact '[polytope].
Proof.
  move=> H. 
  move: H => [Hwell [Hfulldim [Hfeas [Hmapcheck [Hgraph [Hinvert Hsep]]]]]].
  move: Hwell => [Hfacets [Hmappoint [Hvert [Hundir [HspecSimp Hweights]]]]].
  have Hnonemp : facets cert != set0.
    apply/set0Pn. exists (specialSimplex cert @: 'I_d). exact: fst HspecSimp.
  have Hodd := odd_covering_theorem (set_to_asc (facets cert)) (set_to_asc_is_asc (facets cert)) 
  (dim_cert cert Hfacets Hnonemp) (Hnormals)
  (ridges_have_even_incidence Hdim Hfacets Hvert Hgraph Hundir) 
  (cones_are_pointed Hfeas Hfulldim Hfacets Hmappoint Hmapcheck) 
  (exists_special_point Hfacets Hfeas Hmappoint HspecSimp Hweights Hmapcheck Hinvert Hsep).
  split=>//.
  - apply: covering_criterion.
    + exact: (fst Hfeas).
    + move=> z. have Hoddz := Hodd z. move: Hoddz => [F [HF HzF]]. rewrite (facets_cert cert Hfacets) in HF. 
      exists (mapping cert F). split.
      * exact: Hmappoint F HF.
      * have/poly_subsetP Hsub := cone_subset_cert cert Hfeas Hmappoint Hmapcheck F HF.
        exact: Hsub z HzF.
  - apply/compactP. 
    + apply/proper0P. exists full_dim_point. rewrite mem_mk_poly. exact: (fst Hfulldim).
    + move=>c. have [F [HF HcF]] := Hodd c.
      rewrite facets_cert in HF.
      have/poly_subsetP Hsub := cone_subset_cert cert Hfeas Hmappoint Hmapcheck F HF.
      have HcN := Hsub c HcF. rewrite -mem_polyE in HcN. move/in_normalConeP in HcN.
      have Hopt := HcN ((fst Hfeas) (mapping cert F) (Hmappoint F HF)).
      rewrite bounded_argminN0. apply/proper0P. by exists (mapping cert F). by [].
Qed.

End CertificateCompleteness.

Section FlagCriterion.

Context (d : nat) (R : realFieldType).

Local Notation Certificate := (Certificate R d).

Variable (cert : Certificate).

Local Notation polytope := (polytope R d cert).
Local Notation m := polytope.`c.
Local Notation points := (points R d cert).
Local Notation flag_indices := (flag_indices R d cert).
Local Notation flag_vertices := (flag_vertices R d cert).
Local Notation normalVector := (normalVector d R).
Local Notation normalsOf := ((normalsOf m d R (normalVector polytope))).
Local Notation feasibility_check := (feasibility_check d R).
Local Notation flagIndicesAreInActiveSets := (flagIndicesAreInActiveSets d R).
Local Notation flagVerticesArePoints := (flagVerticesArePoints d R).
Local Notation flag_check := (flag_check d R).
Local Notation flag_indices_are_active := (flag_indices_are_active d R cert).
Local Notation flag_vertices_lt_are_active := (flag_vertices_lt_are_active d R cert).
Local Notation flag_vertices_diag_are_not_active := (flag_vertices_diag_are_not_active d R cert).

Hypothesis Hdim : d >= 1.
Hypothesis Hfeas : feasibility_check cert.
Hypothesis Hflagact : flagIndicesAreInActiveSets cert.
Hypothesis Hflagvert : flagVerticesArePoints cert.
Hypothesis Hflagcheck : flag_check cert.

Lemma flag_is_free :
  forall v, v \in points -> free ([tuple normalVector polytope (flag_indices v i) | i < d]).
Proof.
  move=> v Hv.
  apply/freeP => w Hw.
  have Hdot := congr1 (fun x => '[x, v]%R) Hw. rewrite (vdot0l v) in Hdot.
  rewrite vdot_sumDl in Hdot.
  have Hkd (k : 'I_d) : k < size (enum 'I_d).
    rewrite size_enum_ord. exact: ltn_ord k.
  have Hnth : forall i : 'I_d, ([seq normalVector polytope (flag_indices v i0)
  | i0 <- enum 'I_d]`_i)%R = normalVector polytope (flag_indices v i).
    move=> j. rewrite (@nth_map 'I_d j 'cV[R]_d 0%R (fun k => normalVector polytope (flag_indices v k)) j (enum 'I_d) (Hkd j)).
    by rewrite nth_ord_enum.
  have Hrew x : (\sum_i '[ w i *: [seq normalVector polytope (flag_indices v i0) |
  i0 <- enum 'I_d]`_i%R, x])%R = (\sum_i '[ w i *:  normalVector polytope (flag_indices v i), x])%R.
    apply:eq_bigr=> k _. by rewrite (Hnth k).
  rewrite (Hrew v) in Hdot.
  have HvdotZl x : (\sum_i '[ w i *: normalVector polytope (flag_indices v i), x])%R = (\sum_i
      w i * '[normalVector polytope (flag_indices v i), x])%R.
    apply:eq_bigr=> j _. by rewrite vdotZl.
  rewrite (HvdotZl v) in Hdot. 
  have Hactive : (\sum_i w i * '[ normalVector polytope (flag_indices v i), v])%R =
  (\sum_i w i * (polytope.`b (flag_indices v i) 0))%R.
    apply:eq_bigr => j _. by rewrite (flag_indices_are_active Hfeas Hflagact v Hv j).
  rewrite Hactive in Hdot.
  have HR : forall k : nat, forall i : 'I_d, i >= d-1-k -> w i = 0%R.
    induction k. 
    move=> i Hi. rewrite subn0 in Hi.
    have Hkdi := Hkd i. rewrite size_enum_ord in Hkdi.
    have Hid : val i = d.-1.
      rewrite subn1 in Hi.
      have Hile : val i <= d.-1.
      rewrite -ltnS. by rewrite (ltn_predK Hkdi).
      apply/eqP. rewrite eqn_leq. apply/andP. by split.
    have Hdotwd := congr1 (fun x => '[x, (flag_vertices v i)]%R) Hw. 
    rewrite vdot0l in Hdotwd. rewrite vdot_sumDl in Hdotwd. 
    rewrite (Hrew (flag_vertices v i)) in Hdotwd.
    rewrite (HvdotZl (flag_vertices v i)) in Hdotwd.
    have Hdiff : ((\sum_i0 w i0 * '[ normalVector polytope (flag_indices v i0),
    flag_vertices v i])%R - \sum_i w i * polytope.`b 
    (flag_indices v i) 0)%R = 0%R. by rewrite Hdotwd Hdot subrr.
    rewrite -sumrN -big_split /= in Hdiff. 
    rewrite (bigD1 i) in Hdiff.
    simpl in Hdiff.
    have Hsumnull : (\sum_(i0 < d | i0 != i)
    (w i0 * '[ normalVector polytope (flag_indices v i0), flag_vertices v i] -
    w i0 * polytope.`b (flag_indices v i0) 0))%R = 0%R.
      apply: big1 => j Hj. rewrite -mulrBr.
      have Hji : j < i.
    have Hjle : j <= i. rewrite /= Hid.
    have Hjd := (ltn_ord j). have Hd : d = d.-1.+1. by rewrite (prednK Hdim).
    have Hvjd : (j : nat) < d := ltn_ord j. apply: ltnSE. by rewrite -Hd.
    rewrite ltn_neqAle. apply/andP. split=>//.
    rewrite (flag_vertices_lt_are_active Hflagvert Hfeas Hflagcheck v Hv i j
    Hji). rewrite subrr. by rewrite mulr0.
    rewrite Hsumnull in Hdiff. rewrite addr0 in Hdiff.
    rewrite -mulrBr in Hdiff.
    have Hnotnull : ('[ normalVector polytope (flag_indices v i), 
    flag_vertices v i] - polytope.`b (flag_indices v i) 0)%R != 0%R.
    have Hgt := flag_vertices_diag_are_not_active Hflagvert Hfeas Hflagcheck v Hv i.
    rewrite -subr_gt0 in Hgt. have Hgte := gt_eqF Hgt.
    rewrite/negb. by rewrite Hgte. move/eqP in Hdiff.
    rewrite mulf_eq0 in Hdiff. move/orP: Hdiff => [Hw0 | HA0].
    by move/eqP in Hw0.
    move/eqP in HA0. rewrite HA0 in Hnotnull. by rewrite eqxx in Hnotnull.
    by [].
    move=> i Hi.
    case Hk : (k < d-1).
    have Hpos : d-1-k>0. by rewrite subn_gt0.
    case Hie : (val i != d-1-k.+1).
    have Hlt : d - 1 - k.+1 < val i.
    rewrite ltn_neqAle. apply/andP. split=>//. by rewrite eq_sym.
    rewrite subnS in Hlt. 
    have Hle : d-1-k <= val i.
    by rewrite (prednK Hpos) in Hlt.
    apply: IHk i Hle.
    move/eqP in Hie. 
    rewrite (bigID (fun i => d - 1 - k <= val i)) in Hdot. simpl in Hdot.
    have Hnullb : (\sum_(i < d | (d - 1 - k <= i)%N) w i * polytope.`b (flag_indices v i) 0)%R = 0%R.
      apply:big1=>j Hj. rewrite (IHk j Hj). by rewrite mul0r.
    rewrite Hnullb in Hdot. rewrite add0r in Hdot.
    rewrite (bigID (fun i => d - 1 - k <= val i)) in Hw. simpl in Hw.
    have Hnulla :   (\sum_(i < d | (d - 1 - k <= i)%N) w i *:
    [seq normalVector polytope (flag_indices v i0) | i0 <- enum 'I_d]`_i)%R = 0%R.
      apply:big1=>j Hj. rewrite (IHk j Hj). by rewrite scale0r.
    rewrite Hnulla in Hw. rewrite add0r in Hw.
    have Hdotwk := congr1 (fun x => '[x, (flag_vertices v i)]%R) Hw. 
    rewrite vdot0l in Hdotwk. rewrite vdot_sumDl in Hdotwk. 
    have Hrewind x : (\sum_(i | ~~ (d - 1 - k <= val i)%N) '[ w i *: [seq normalVector polytope (flag_indices v i0) |
    i0 <- enum 'I_d]`_i%R, x])%R = (\sum_(i | ~~ (d - 1 - k <= val i)%N) '[ w i *:  normalVector polytope (flag_indices v i), x])%R.
    apply:eq_bigr=> l _. by rewrite (Hnth l).
    have HvdotZlind x : (\sum_(i | ~~ (d - 1 - k <= val i)%N) '[ w i *: normalVector polytope (flag_indices v i), x])%R = (\sum_(i | ~~ (d - 1 - k <= val i)%N)
      w i * '[normalVector polytope (flag_indices v i), x])%R.
    apply:eq_bigr=> j _. by rewrite vdotZl.
    rewrite (Hrewind (flag_vertices v i)) in Hdotwk.
    rewrite (HvdotZlind (flag_vertices v i)) in Hdotwk.
    have Hdiff : ((\sum_(i0 | ~~ (d - 1 - k <= val i0)%N) w i0 * '[ normalVector polytope (flag_indices v i0),
    flag_vertices v i])%R - \sum_(i | ~~ (d - 1 - k <= val i)%N) w i * polytope.`b 
    (flag_indices v i) 0)%R = 0%R. by rewrite Hdotwk Hdot subrr.
    rewrite -sumrN -big_split /= in Hdiff. 
    rewrite (bigD1 i) in Hdiff.
    simpl in Hdiff.
    have Hsumnull : (\sum_(i0 < d | ~~ (d - 1 - k <= i0)%N && (i0 != i))
    (w i0 * '[ normalVector polytope (flag_indices v i0), flag_vertices v i] -
    w i0 * polytope.`b (flag_indices v i0) 0))%R = 0%R.
      apply: big1 => j Hj. move/andP: Hj => [Hdk Hji]. rewrite -mulrBr.
      have Hjli : j < i.
    have Hjle : j <= i. rewrite /= Hie.
    rewrite -ltnNge in Hdk. rewrite subnS.
    by rewrite -ltnS (prednK Hpos).
    rewrite ltn_neqAle. apply/andP. by split.
    rewrite (flag_vertices_lt_are_active Hflagvert Hfeas Hflagcheck v Hv i j
    Hjli). rewrite subrr. by rewrite mulr0.
    rewrite Hsumnull in Hdiff. rewrite addr0 in Hdiff.
    rewrite -mulrBr in Hdiff.
    have Hnotnull : ('[ normalVector polytope (flag_indices v i), 
    flag_vertices v i] - polytope.`b (flag_indices v i) 0)%R != 0%R.
    have Hgt := flag_vertices_diag_are_not_active Hflagvert Hfeas Hflagcheck v Hv i.
    rewrite -subr_gt0 in Hgt. have Hgte := gt_eqF Hgt.
    rewrite/negb. by rewrite Hgte. move/eqP in Hdiff.
    rewrite mulf_eq0 in Hdiff. move/orP: Hdiff => [Hw0 | HA0].
    by move/eqP in Hw0.
    move/eqP in HA0. rewrite HA0 in Hnotnull. by rewrite eqxx in Hnotnull.
    rewrite Hie. rewrite -ltnNge. rewrite subnS. by rewrite (prednK Hpos).
    have Heq : d - 1 - k.+1 = d - 1 - k.
      have Hk' : k >= d-1. by rewrite leqNgt Hk.
      rewrite -subn_eq0 in Hk'. move/eqP in Hk'. rewrite Hk'.
      apply/eqP. rewrite subn_eq0. move/eqP in Hk'. rewrite subn_eq0 in Hk'.
      by apply:leqW.
    rewrite Heq in Hi. exact: IHk i Hi.
  move=> i. have Hend := HR (d-1) i. rewrite subnn in Hend.
  exact: Hend (leq0n i).
Qed.

Lemma flag_is_full_dim :
  forall v, v \in points -> (\dim << normalsOf [set flag_indices v i | i : 'I_d] >> = d)%VS.
Proof.
  move=> v Hv.
  have Hfree := flag_is_free v Hv.
  have Hd : (\dim <<[tuple normalVector polytope (flag_indices v i) | i < d]>> = d)%VS.
    rewrite/free in Hfree. move/eqP in Hfree. rewrite Hfree. exact: size_tuple.
  have Heqspan : (<<[tuple normalVector polytope (flag_indices v i) | i < d]>> =
  <<normalsOf [set flag_indices v i | i : 'I_d]>>)%VS.
    apply: eq_span=> x.
    apply/idP/idP.
    - move=> Hx. apply/in_normalsOfP. move/mapP:Hx => [i Hi Hxi].
      exists (flag_indices v i). split=>//.
      apply/imsetP. exists i. by []. by [].
    - move=> Hx. move/in_normalsOfP: Hx => [i [Hi Hxi]]. 
      apply/mapP. move/imsetP: Hi => [j Hj Hij]. exists j.
      apply/mapP. exists j. by []. by [].
      by rewrite Hij in Hxi.
  by rewrite Heqspan in Hd.
Qed.

End FlagCriterion.

Section CertificateCorrectness.

Context (d : nat) (R : realFieldType).

Local Notation Certificate := (Certificate R d).

Variable (cert : Certificate). 

Local Notation polytope := (polytope R d cert).
Local Notation m := polytope.`c.
Local Notation points := (points R d cert).
Local Notation facetsAreDSimplices := (facetsAreDSimplices d R).
Local Notation mappingHasImageInPoints := (mappingHasImageInPoints d R).
Local Notation graphVerticesAreFacets := (graphVerticesAreFacets d R ).
Local Notation graphIsUndirected := (graphIsUndirected d R).
Local Notation specialSimplexInSpecialCone := (specialSimplexInSpecialCone d R).
Local Notation weightsAreStrictlyPositiveVectors := (weightsAreStrictlyPositiveVectors d R).
Local Notation full_dim_check := (full_dim_check d R).
Local Notation feasibility_check := (feasibility_check d R).
Local Notation mapping_check := (mapping_check d R).
Local Notation graph_check := (graph_check d R).
Local Notation inversibility_check := (inversibility_check d R).
Local Notation separability_check := (separability_check d R).
Local Notation normalVector := (normalVector d R).
Local Notation facets := (facets R d).
Local Notation mapping := (mapping R d).
Local Notation specialSimplex := (specialSimplex R d).
Local Notation flag_indices := (flag_indices R d cert).
Local Notation odd_covering_theorem := (odd_covering_theorem m d R (normalVector polytope)).
Local Notation ridges_have_even_incidence := (ridges_have_even_incidence d R cert).
Local Notation cones_are_pointed := (cones_are_pointed d R cert).
Local Notation exists_special_point := (exists_special_point d R cert).
Local Notation dim_cert := (dim_cert d R).
Local Notation facets_cert := (facets_cert d R).
Local Notation cone_subset_cert := (cone_subset_cert d R).
Local Notation full_dim_point := (full_dim_point R d cert).
Local Notation flagIndicesAreInActiveSets := (flagIndicesAreInActiveSets d R).
Local Notation flagVerticesArePoints := (flagVerticesArePoints d R).
Local Notation flag_check := (flag_check d R).
Local Notation certificate_completeness := (certificate_completeness d R).
Local Notation check_certificate_completeness := (check_certificate_completeness d R).
Local Notation flag_indices_are_active := (flag_indices_are_active d R).
Local Notation flag_is_full_dim := (flag_is_full_dim d R cert).

Hypothesis Hdim : d > 0.
Hypothesis Hnormals : forall i : 'I_m, (normalVector polytope i <> 0)%R.

Definition well_formedness_check :=
  facetsAreDSimplices cert /\ 
  mappingHasImageInPoints cert /\ 
  graphVerticesAreFacets cert /\ 
  graphIsUndirected cert /\ 
  specialSimplexInSpecialCone cert /\
  weightsAreStrictlyPositiveVectors cert /\
  flagIndicesAreInActiveSets cert /\
  flagVerticesArePoints cert.

Definition check_certificate :=
  well_formedness_check /\ 
  full_dim_check cert /\ 
  feasibility_check cert /\ 
  mapping_check cert /\ 
  graph_check cert /\ 
  inversibility_check cert /\ 
  separability_check cert /\
  flag_check cert.

Theorem certificate_correctness :
  check_certificate -> ((vertex_set '[polytope]) = points)%fset.
Proof.
  move=> H. 
  move: H => [Hwell [Hfulldim [Hfeas [Hmapcheck [Hgraph [Hinvert [Hsep Hflagcheck]]]]]]].
  move: Hwell => [Hfacets [Hmappoint [Hvert [Hundir [HspecSimp [Hweights [Hflagact Hflagvert]]]]]]].
  have Hcheck : check_certificate_completeness cert. split=>//.
  apply/eqP. rewrite eqEfsubset. apply/andP. split.
  - by exact: (fst (certificate_completeness cert Hdim Hnormals Hcheck)).
  - apply/fsubsetP. move=> v Hv.
    apply: vertex_criterion.
    by exact: (snd (certificate_completeness cert Hdim Hnormals Hcheck)).
    by exact: (fst Hfeas) v Hv.
    exists [set flag_indices v i | i : 'I_d]. split.
    apply/subsetP => x Hx. apply/in_active_constraintsP.
    move/imsetP: Hx => [i Hi Hxi]. rewrite Hxi.
    by exact: (flag_indices_are_active cert Hfeas Hflagact v Hv i).
    by exact: flag_is_full_dim.
Qed.

End CertificateCorrectness.
