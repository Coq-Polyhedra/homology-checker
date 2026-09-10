From mathcomp Require Import finmap all_ssreflect all_algebra.
Import GRing.Theory Num.Theory Order.Theory.
From Polyhedra Require Import hpolyhedron row_submx inner_product polyhedron poly_base affine vector_order barycenter lrel.
From PolyhedraHirsch Require Import high_graph.
From Cert Require Import GraphDistance.
Import HPolyhedron.
Open Scope polyh_scope.
From Cert Require Import OddCoveringTheorem CoveringCriterion.

Section Certificate.

Context (R : realFieldType) (d : nat).

Notation simplex_of m := (simplex [finType of 'I_m]).
Notation simplex_graph m := (graph [choiceType of (simplex_of m)]).
Notation vertex_graph := (graph [choiceType of ('cV[R]_d)]).

Record Certificate := {
    polytope : 'hpoly[R]_d;
    points : {fset 'cV[R]_d};
    full_dim_point : 'cV[R]_d;
    full_dim_dir : 'M[R]_(d,d);
    full_dim_inv : 'M[R]_(d,d);
    activeSets : 'cV[R]_d -> {set 'I_(polytope.`c)};
    facets : {set simplex_of (polytope.`c)};
    mapping : simplex_of (polytope.`c) -> 'cV[R]_d;
    graph : simplex_graph (polytope.`c);
    specialVertex : 'cV[R]_d;
    specialSimplex : 'I_d -> 'I_(polytope.`c);
    witnesses : 'M[R]_(d,d);
    weights : simplex_of (polytope.`c) -> 'cV[R]_d;
    flag_indices : 'cV[R]_d -> 'I_d -> 'I_(polytope.`c);
    flag_vertices : 'cV[R]_d -> 'I_d -> 'cV[R]_d;
    geom_graph : vertex_graph
}.

(* The distance certificate: a source point and the distance of every point
   from it *)
Record DistanceCertificate := {
    source : 'cV[R]_d;
    distance : 'cV[R]_d -> nat
}.

End Certificate.

Section HighLevelChecks.

Context (d : nat) (R : realFieldType).

Notation "'[ u , v ]" := (vdot u v).
Notation "x <=m y" := (lev x y).

Local Notation simplex_of m := (simplex [finType of 'I_m]).
Local Notation Certificate := (Certificate R d).

Definition incomparable {T : finType} (A B : {set T}) :=
  ~~ (A \subset B) && ~~ (B \subset A).

Definition normalVector (polytope : 'hpoly[R]_d) (i : 'I_(polytope.`c)) :=
    trmx (row i polytope.`A).

Variable (cert : Certificate).

Local Notation polytope := (polytope R d cert).
Local Notation points := (points R d cert).
Local Notation full_dim_point := (full_dim_point R d cert).
Local Notation full_dim_dir := (full_dim_dir R d cert).
Local Notation full_dim_inv := (full_dim_inv R d cert).
Local Notation activeSets := (activeSets R d cert).
Local Notation facets := (facets R d cert).
Local Notation mapping := (mapping R d cert).
Local Notation graph := (graph R d cert).
Local Notation specialVertex := (specialVertex R d cert).
Local Notation specialSimplex := (specialSimplex R d cert).
Local Notation witnesses := (witnesses R d cert).
Local Notation weights := (weights R d cert).
Local Notation flag_indices := (flag_indices R d cert).
Local Notation flag_vertices := (flag_vertices R d cert).
Local Notation geom_graph := (geom_graph R d cert).
Local Notation m := (polytope.`c).

Variable (dc : DistanceCertificate R d).

Local Notation source := (source R d dc).
Local Notation distance := (distance R d dc).

(* Well-formedness condition on facets *)
Definition facetsAreDSimplices :=
  forall f : simplex_of m, f \in facets -> #|f| == d.

(* Well-formedness condition on mapping *)
Definition mappingHasImageInPoints :=
  forall f : simplex_of m, f \in facets -> mapping f \in points.

(* Well-formedness condition on graph *)
Definition graphVerticesAreFacets :=
  vertices graph =i facets.

Definition graphIsUndirected :=
  forall x y, y \in successors graph x <-> x \in successors graph y.

(* Well-formedness condition on the special simplex *)
Definition specialSimplexInSpecialCone :=
  specialSimplex @: 'I_d \in facets /\
  mapping (specialSimplex @: 'I_d) = specialVertex.

(* Well-formedness condition on the weights *)
Definition weightsAreStrictlyPositiveVectors :=
  forall f : simplex_of m, mapping f = specialVertex
  -> f != specialSimplex @: 'I_d -> (0 <=m (weights f)) /\ (weights f <> 0%R).

(* Well-formedness condition on flag indices *)
Definition flagIndicesAreInActiveSets :=
  forall v : 'cV[R]_d, v \in points -> forall i : 'I_d, flag_indices v i \in activeSets v.

(* Well-formedness condition on flag vertices *)
Definition flagVerticesArePoints :=
  forall v : 'cV[R]_d, v \in points -> forall i : 'I_d, flag_vertices v i \in points.
  
(* Well-formedness condition on the geometric graph *)
Definition geomGraphVerticesArePoints :=
  vertices geom_graph = points.

Definition geomGraphIsImageOfGraph :=
  forall v w : 'cV[R]_d, v \in vertices geom_graph -> w \in vertices geom_graph
  -> (w \in successors geom_graph v <-> exists fv fw : simplex_of m, fv \in vertices graph
  /\ fw \in successors graph fv /\ mapping fv = v /\ mapping fw = w).

(* Full dimension hypothesis *)
Definition full_dim_check :=
  full_dim_point \in polytope
  /\ (forall i : 'I_d, (full_dim_point + col i full_dim_dir)%R \in polytope)
  /\ forall (i j : 'I_d), (i = j /\ '[col i full_dim_dir, col j full_dim_inv] <> 0)%R
  \/ (i <> j /\ '[col i full_dim_dir, col j full_dim_inv] = 0)%R.

(* Condition T1 *)
Definition feasibility_check :=
  {subset points <= polytope} /\ forall x : 'cV[R]_d, x \in points ->
  activeSets x = [set i : 'I_m | '[normalVector polytope i , x] == polytope.`b i ord0].

(* Condition T2 *)
Definition mapping_check :=
  forall f : simplex_of m, f \in facets ->
  f \subset activeSets (mapping f).

(* Condition T3 *)
Definition graph_check :=
  forall f, f \in vertices graph -> #|successors graph f| <= d /\
  forall i : 'I_m, (i \in f) -> exists f', (f' \in successors graph f) /\ f:\i \subset f'.

(* Condition T4 *)
Definition inversibility_check :=
  forall (i j : 'I_d), (i = j /\ '[\col_k (polytope.`A (specialSimplex i) k), (col j witnesses)] > 0)%R
  \/ (i <> j /\ '[\col_k (polytope.`A (specialSimplex i) k), (col j witnesses)] = 0)%R.

(* Condition T5 *)
Definition separability_check :=
  forall f : simplex_of m, mapping f = specialVertex
  -> f != specialSimplex @: 'I_d
  -> forall i : 'I_m, i \in f ->
  ('[witnesses *m (weights f) , normalVector polytope i] <= 0)%R.

(* Condition T6 *)
Definition flag_check :=
  forall v, v \in points -> forall k : 'I_d, flag_indices v k \notin activeSets (flag_vertices v k)
  /\ forall j : 'I_d, j < k -> flag_indices v j \in activeSets (flag_vertices v k).

(* Condition T7 *)
Definition geom_edge_difference_pairwise_check :=
  forall v : 'cV[R]_d, v \in vertices geom_graph -> forall w w' : 'cV[R]_d,
  w \in successors geom_graph v /\ w' \in successors geom_graph v -> w <> w' 
  -> incomparable (activeSets v :\: activeSets w) (activeSets v :\: activeSets w').

(* Condition D1: the source is a vertex of the geometric graph, at distance 0 *)
Definition distance_source_check :=
  source_labelled geom_graph source distance.

(* Condition D2: along every edge the distance grows by at most one *)
Definition distance_edge_check :=
  edges_labelled geom_graph distance.

(* Condition D3: every other vertex has a neighbour one closer to the source *)
Definition distance_parent_check :=
  parents_labelled geom_graph source distance.

(* The certified eccentricity of the source: the largest distance *)
Definition eccentricity_check (D : nat) :=
  (forall v : 'cV[R]_d, v \in vertices geom_graph -> distance v <= D)
  /\ (exists v : 'cV[R]_d, v \in vertices geom_graph /\ distance v = D).

(* The distance certificate as a whole *)
Definition distance_check (D : nat) :=
  distance_source_check /\ distance_edge_check /\ distance_parent_check
  /\ eccentricity_check D.

End HighLevelChecks.

Section CertificateLemmas.

Context (d : nat) (R : realFieldType).

Notation "'[ u , v ]" := (vdot u v).

Local Notation Certificate := (Certificate R d).

Variable (cert : Certificate).

Local Notation polytope := (polytope R d cert).
Local Notation m := polytope.`c.
Local Notation points := (points R d cert).
Local Notation simplex_of m := (simplex [finType of 'I_m]).
Local Notation active_constraints := (active_constraints d R polytope).
Local Notation normalVector := (normalVector d R polytope).
Local Notation coneOf := (coneOf m d R (normalVector)).
Local Notation normalCone := (normalCone d R polytope).
Local Notation facetsAreDSimplices := (facetsAreDSimplices d R cert).
Local Notation graphVerticesAreFacets := (graphVerticesAreFacets d R cert).
Local Notation graphIsUndirected := (graphIsUndirected d R cert).
Local Notation mappingHasImageInPoints := (mappingHasImageInPoints d R cert).
Local Notation flagIndicesAreInActiveSets := (flagIndicesAreInActiveSets d R cert).
Local Notation flagVerticesArePoints := (flagVerticesArePoints d R cert).
Local Notation feasibility_check := (feasibility_check d R cert).
Local Notation inversibility_check := (inversibility_check d R cert).
Local Notation graph_check := (graph_check d R cert).
Local Notation full_dim_check := (full_dim_check d R cert).
Local Notation flag_check := (flag_check d R cert).
Local Notation mapping_check := (mapping_check d R cert).
Local Notation facets := (facets R d cert).
Local Notation graph := (graph R d cert).
Local Notation geom_graph := (geom_graph R d cert).
Local Notation specialSimplex := (specialSimplex R d cert).
Local Notation witnesses := (witnesses R d cert).
Local Notation activeSets := (activeSets R d cert).
Local Notation full_dim_point := (full_dim_point R d cert).
Local Notation full_dim_dir := (full_dim_dir R d cert).
Local Notation full_dim_inv := (full_dim_inv R d cert).
Local Notation mapping := (mapping R d cert).
Local Notation flag_indices := (flag_indices R d cert).
Local Notation flag_vertices := (flag_vertices R d cert).
Local Notation notin_active_constraintsP := (notin_active_constraintsP d R).

Lemma vertices_card (f : simplex_of m) :
  facetsAreDSimplices -> graphVerticesAreFacets -> 
  f \in vertices graph -> #|f| = d.
Proof.
  move=> Hfacets Hvert Hfvert.
  apply/eqP.
  apply: (Hfacets f).
  by rewrite -(Hvert f).
Qed.

Lemma facets_cardND1 (f : simplex_of m) (i : 'I_m) :
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

Lemma incident_facets_cert_subset (r : simplex_of m) : 
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

Lemma ridges_card (r : simplex_of m) :
  facetsAreDSimplices -> facets != set0 -> 
  r \in ridgesOf (set_to_asc facets) -> #|r| = d.-1.
Proof.
  move=> Hfacets Hemp Hr.
  move/in_ridgesOfP in Hr. case: Hr => [Hrf Hrdim].
  rewrite/sdim in Hrdim. 
  by rewrite (dim_cert Hfacets Hemp) in Hrdim.
Qed.

Lemma successors_subset (f : simplex_of m) :
  graphVerticesAreFacets -> {subset successors graph f <= facets}.
Proof.
  move=> Hgraph x Hx.
  have/fsubsetP Hsub := sub_succ graph f.
  have Hxvert := Hsub x Hx.
  by rewrite (Hgraph x) in Hxvert.
Qed.

Lemma full_dim_cert :
  feasibility_check -> full_dim_check -> \pdim '[polytope] = d.+1.
Proof.
  move=> _ [Hpoint [Hdir Hinv]].
  have HpointP : full_dim_point \in '[polytope].
    by rewrite mem_mk_poly.
  pose X := [seq (full_dim_point + col i full_dim_dir)%R | i <- enum 'I_d].
  have HXP : {in X, forall x : 'cV_d, x \in '[polytope]}.
    move=> x Hx.
    rewrite /X in Hx. move/mapP in Hx. move: Hx => [i Hi Hxi].
    rewrite Hxi. rewrite mem_mk_poly. by exact: Hdir i.
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
  feasibility_check -> forall x : 'cV[R]_d, x \in points -> activeSets x = active_constraints x.
Proof.
  move=>Hfeas x HxV.
  by rewrite (snd (Hfeas) x HxV).
Qed.

Lemma inversibility_cert :
  inversibility_check -> free [seq (\col_k (polytope.`A (specialSimplex i) k))%R | i <- enum 'I_d].
Proof.
  move=> Hinv.
  apply/freeP=> w Hw i.
    have Hwi := congr1 (fun u => '[u, col (enum_val i) witnesses]%R) Hw.
    rewrite vdot0l vdot_sumDl (bigD1 i) //= big1 ?addr0 in Hwi.
    rewrite (nth_map (enum_val i) 0%R) ?size_enum ?ltn_ord // in Hwi.
    rewrite vdotZl in Hwi.
    move/eqP in Hwi. rewrite GRing.mulf_eq0 in Hwi.
    move/orP: Hwi => [/eqP Ha | /eqP Hb].
    - by [].
    - have Hi := (Hinv (enum_val i) (enum_val i)).
      have Hnz : '[\col_k (polytope.`A (specialSimplex (enum_val i)) k), col (enum_val i) witnesses]%R <> 0%R.
      case: Hi => [[_ Hnz] | [Hneq _]].
      + apply/eqP. rewrite gt_eqF. by []. by [].
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
    have Hzero : '[\col_k (polytope.`A (specialSimplex (enum_val j)) k), col (enum_val i) witnesses]%R = 0%R.
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
Qed.

Lemma cone_subset_cert :
  feasibility_check -> mappingHasImageInPoints -> mapping_check -> forall f : simplex_of m, f \in facets -> (coneOf f) `<=` normalCone (mapping f).
Proof.
  move=> Hfeas Hmappoint Hmapcheck f Hf. 
  apply:coneOfS. 
  rewrite -(activeSets_cert Hfeas (mapping f) (Hmappoint f Hf)).
  exact: Hmapcheck f Hf.
Qed.

Lemma flag_indices_are_active :
  feasibility_check -> flagIndicesAreInActiveSets -> forall v : 'cV[R]_d, v \in points -> forall i : 'I_d, ('[normalVector 
  (flag_indices v i), v])%R = (polytope.`b (flag_indices v i) 0)%R.
Proof.
  move=> Hfeas Hflag v Hv i.
  have Hact := (Hflag v Hv i).
  rewrite (activeSets_cert Hfeas v Hv) in Hact.
  by move/in_active_constraintsP in Hact.
Qed. 

Lemma flag_vertices_lt_are_active :
  flagVerticesArePoints -> feasibility_check -> flag_check ->
  forall v, v \in points -> forall k : 'I_d, forall j : 'I_d, j < k ->
  ('[normalVector (flag_indices v j), flag_vertices v k])%R = (polytope.`b (flag_indices v j) 0)%R.
Proof.
  move=> Hflagvert Hfeas Hflagcheck v Hv k j Hjk.
  have Hact := (snd (Hflagcheck v Hv k) j Hjk).
  rewrite (activeSets_cert Hfeas (flag_vertices v k) (Hflagvert v Hv k)) in Hact.
  by move/in_active_constraintsP in Hact.
Qed.

Lemma flag_vertices_diag_are_not_active :
  flagVerticesArePoints -> feasibility_check -> flag_check ->
  forall v, v \in points -> forall k : 'I_d, (('[normalVector (flag_indices v k), 
  flag_vertices v k])%R > polytope.`b (flag_indices v k) 0)%R.
Proof.
  move=> Hflagvert Hfeas Hflagcheck v Hv k.
  have Hact := (fst (Hflagcheck v Hv k)).
  rewrite (activeSets_cert Hfeas (flag_vertices v k) (Hflagvert v Hv k)) in Hact.
  by move/(notin_active_constraintsP polytope (flag_vertices v k) (flag_indices v k) ((fst Hfeas) (flag_vertices v k) (Hflagvert v Hv k))) in Hact.
Qed.

(* Conditions D1-D3 make the distances exact: the eccentricity of the source
   in the geometric graph is the certified value. *)
Lemma eccentricity_cert (dc : DistanceCertificate R d) (D : nat) :
  (forall x y : 'cV[R]_d, edges geom_graph x y -> edges geom_graph y x) ->
  distance_source_check d R cert dc -> distance_edge_check d R cert dc ->
  distance_parent_check d R cert dc -> eccentricity_check d R cert dc D ->
  eccentricity_is geom_graph (source R d dc) D.
Proof.
move=> hsym h1 h2 h3 [hbound hattained].
exact: (eccentricity_of_labelling hsym h1 h2 h3 hbound hattained).
Qed.

End CertificateLemmas.

