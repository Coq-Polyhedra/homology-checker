From mathcomp Require Import finmap all_ssreflect all_algebra.
Import GRing.Theory Num.Theory Order.Theory.
From Polyhedra Require Import hpolyhedron row_submx inner_product polyhedron poly_base affine vector_order barycenter lrel.
From DepotThese Require Import high_graph.
Import HPolyhedron.

Open Scope polyh_scope.

From Cert Require Import OddCoveringTheorem NormalCones HighLevelCertificate.

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

Section RidgesHaveEvenIncidence.

Context (d : nat) (R : realFieldType).

Variable (P : 'hpoly[R]_d) (V : {fset 'cV[R]_d}).

Local Notation m := (m R d P).
Local Notation simplex_m := (simplex [finType of 'I_m]).
Local Notation Certificate := (Certificate R d P).
Local Notation facetsAreDSimplices := (facetsAreDSimplices d R P).
Local Notation graphVerticesAreFacets := (graphVerticesAreFacets d R P).
Local Notation graphIsUndirected := (graphIsUndirected d R P).
Local Notation graph_check := (graph_check d R P).
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
Local Notation facetsAreDSimplices := (facetsAreDSimplices d R P).
Local Notation full_dim_check := (full_dim_check d R P V).
Local Notation mappingHasImageInPoints := (mappingHasImageInPoints d R P V).
Local Notation feasibility_check := (feasibility_check d R P V).
Local Notation mapping_check := (mapping_check d R P).
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
Local Notation mappingHasImageInPoints := (mappingHasImageInPoints d R P V).
Local Notation specialSimplexInSpecialCone := (specialSimplexInSpecialCone d R P).
Local Notation weightsAreStrictlyPositiveVectors := (weightsAreStrictlyPositiveVectors d R P).
Local Notation mapping_check := (mapping_check d R P).
Local Notation inversibility_check := (inversibility_check d R P).
Local Notation separability_check := (separability_check d R P).

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