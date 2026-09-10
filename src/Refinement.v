(* -------------------------------------------------------------------------- *)
(* Refinement: linking the executable checker (LowLevelChecker) to the        *)
(* abstract specification (HighLevelCertificate / CertificateCorrectness).    *)
(*                                                                            *)
(* Built on the generic bridges of RefinementBridges.v; this file interprets  *)
(* a low-level certificate as a high-level one ([interp_cert]) and proves     *)
(* that every check of [VtxContainment.check_certificate] implies its         *)
(* high-level counterpart, up to [vertex_containment] at the end; the         *)
(* [GraphEquality] checks are discharged separately, into the geometric-graph *)
(* conditions of the spec ([graph_equality_correct]).                         *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import Uint63 PArray ZArith Lia.
From Bignums Require Import BigZ BigN.
From mathcomp Require Import finmap all_ssreflect all_algebra.
From Polyhedra Require Import inner_product vector_order hpolyhedron.
From PolyhedraHirsch Require Import high_graph.
From Cert Require LowLevelChecker HighLevelCertificate CertificateCorrectness.
From Cert Require Import RefinementBridges GraphDistance.

Module L := LowLevelChecker.
Module H := HighLevelCertificate.
Module CC := CertificateCorrectness.
Import HPolyhedron.

Import GRing.Theory Num.Theory Order.Theory.

Local Notation int := PrimInt63.int.
#[local] Delimit Scope Z_scope with Z.
Local Open Scope array_scope.

(* high_graph opens fset_scope globally, which makes [+] mean [catf] on fmaps.
   Close it here: fset notations are used with an explicit [%fset]. *)
#[local] Close Scope fset_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(* The checker's well-formedness bundle, destructured once                    *)
(* -------------------------------------------------------------------------- *)

(* The shape of the &&-trees of [LowLevelChecker] is known here and in the
   five selector lemmas only; everything else goes through named fields. *)
Record wf_data (c : L.Certificate) : Prop := WfData {
  wf_ineq  : L.areInequalitiesWellFormed c;
  wf_pts   : L.arePointsWellFormed c;
  wf_act   : L.areActiveSetsWellFormed c;
  wf_graph : L.isGraphWellFormed c;
  wf_desc  : L.areDescriptionsWellFormed c;
  wf_map   : L.isMappingWellFormed c;
  wf_si    : L.isSimplexIndexWellFormed c;
  wf_ai    : L.isActiveInverseWellFormed c;
  wf_wit   : L.areWitnessesWellFormed c;
  wf_sp    : L.areScalarProductsWellFormed c;
  wf_wt    : L.areWeightsWellFormed c;
  wf_fd    : L.isFullDimWellFormed c;
  wf_asu   : L.areActiveSetsUnique c;
  wf_fu    : L.areFacetsUnique c }.

Lemma wfP (c : L.Certificate) : L.VtxContainment.well_formedness_check c -> wf_data c.
Proof.
rewrite /L.VtxContainment.well_formedness_check /L.areVerticesWellFormed /L.areFacetsWellFormed
        /L.isRootWellFormed.
move=> /andP[/andP[/andP[/andP[/andP[/andP[/andP[hineq /andP[hpts hact]] hg] /andP[hdesc hmapwf]]
  /andP[/andP[/andP[/andP[hsi hai] hw] hsp] hwt]] hfd] hasu] hfu].
by split.
Qed.

Lemma rootP (c : L.Certificate) : L.VtxContainment.root_check c ->
  [/\ L.scalarProducts_check c, L.inversibility_check c & L.separability_check c].
Proof. by rewrite /L.VtxContainment.root_check => /andP[/andP[h1 h2] h3]. Qed.

Lemma certP (c : L.Certificate) : L.VtxContainment.check_certificate c ->
  [/\ L.VtxContainment.well_formedness_check c, L.feasibility_check c, L.mapping_check c,
      L.graph_check c & L.VtxContainment.root_check c /\ L.full_dim_check c].
Proof.
rewrite /L.VtxContainment.check_certificate.
by move=> /andP[/andP[/andP[/andP[/andP[hwf h1] h2] h3] hr] hfd]; split.
Qed.

Lemma geqP (c : L.Certificate) : L.GraphEquality.check_certificate c ->
  [/\ L.isGeomGraphWellFormed c, L.areGeomEdgeSourcesWellFormed c
    & L.areGeomEdgeLocalTargetsWellFormed c] /\
  L.graph_image_check c /\ L.geom_edge_difference_pairwise_check c.
Proof.
rewrite /L.GraphEquality.check_certificate /L.GraphEquality.well_formedness_check.
by move=> /andP[/andP[/andP[/andP[hg hsrc] htgt] himg] hpair].
Qed.

Lemma veqP (c : L.Certificate) : L.VtxEquality.check_certificate c ->
  L.areFlagsWellFormed c /\ L.flag_check c.
Proof.
by rewrite /L.VtxEquality.check_certificate => /andP[hfw hchk].
Qed.

(* -------------------------------------------------------------------------- *)
(* The interpreted certificate                                                *)
(* -------------------------------------------------------------------------- *)

(* Tactic conventions below: the checker's definitions are [let]-heavy, so
   [cbv zeta] exposes their bodies and [cbv beta] reduces the resulting
   redexes -- never [simpl], which would unfold [nat_of_int] and bigZ terms.
   Facts spelled at a convertible-but-different type are obtained with
   [have h : T := t] or closed with [exact:], both of which go through
   conversion where [rewrite] would fail on universe instances. *)

Section Interp.

Context (R : realFieldType) (c : L.Certificate).

Local Open Scope ring_scope.

Local Notation m := (nat_of_int (L.nb_inequalities c)).
Local Notation d := (nat_of_int (L.dimension c)).
Local Notation nv := (balen (L.vertices c)).

Definition ineq_of (i : 'I_m) : L.Inequality := aget (L.inequalities c) i.
Definition normal_of (i : 'I_m) : 'cV[R]_d := vec_of_array R d (L.normal (ineq_of i)).
Definition bound_of (i : 'I_m) : R := bigZ2R R (L.bound (ineq_of i)).

(* Well-formedness of the inequalities, in bridge form. *)
Lemma ineqs_len : L.areInequalitiesWellFormed c -> alen (L.inequalities c) = m.
Proof.
rewrite /L.areInequalitiesWellFormed; cbv zeta => /andP[/andP[hnb _] _].
by move: hnb; rewrite eqb_natE /alen => /eqP ->.
Qed.

Lemma normal_len (hineq : L.areInequalitiesWellFormed c) (i : 'I_m) :
  alen (L.normal (ineq_of i)) = d.
Proof.
have hlen := ineqs_len hineq; move: hineq.
rewrite /L.areInequalitiesWellFormed; cbv zeta.
by move=> /andP[/andP[_ /(for_all_composeP _ _ hlen)/(_ i)/hasLengthP h] _].
Qed.

Lemma hasLength_alen T (a : array T) : L.hasLength (L.dimension c) a -> alen a = d.
Proof. by move/hasLengthP. Qed.

Lemma rows_len (a : array (array bigZ)) : alen a = d ->
  L.for_all (L.hasLength (L.dimension c)) a -> forall i : 'I_d, alen (aget a i) = d.
Proof. by move=> ha /(for_allP _ ha) h i; have := h i; cbv beta => /hasLength_alen. Qed.

(* Coq-Polyhedra's ['hpoly] is {x | A x >= b}, while the checker tests
   <a_i, x> <= b_i: the sign flip is absorbed here, once. *)
Definition hpoly_of : 'hpoly[R]_d :=
  HPoly (- \matrix_(i < m) (normal_of i)^T) (- \col_(i < m) bound_of i).

(* Never rewritten with, but this definitional equality is what lets every
   ['I_m] of this file typecheck against [H.m R d hpoly_of]. *)
Lemma hpoly_of_c : hpoly_of.`c = m.
Proof. by []. Qed.

(* Projections by conversion: no [simpl] on the unfolded record (it would go on
   to unfold [normal_of], [vec_of_array], [nat_of_int], ... and hang). *)
Lemma hpoly_of_A : hpoly_of.`A = - \matrix_(i < m) (normal_of i)^T.
Proof. by []. Qed.

Lemma hpoly_of_b : hpoly_of.`b = - \col_(i < m) bound_of i.
Proof. by []. Qed.

(* No [mxE] on [(row i A)^T j 0]: unification hangs on that composite even
   for a generic [A]. Structural lemmas instead. *)
Lemma row_hpoly_of (i : 'I_m) : (row i hpoly_of.`A)^T = - normal_of i.
Proof.
rewrite hpoly_of_A.
have -> : forall M : 'M[R]_(m, d), row i (- M) = - row i M by move=> M; rewrite linearN.
have -> : forall u : 'rV[R]_d, (- u)^T = - u^T by move=> u; rewrite linearN.
by rewrite rowK trmxK.
Qed.

Lemma normalVector_hpoly_of (i : 'I_m) : @H.normalVector d R hpoly_of i = - normal_of i.
Proof. exact: row_hpoly_of. Qed.

Lemma hpoly_of_bE (i : 'I_m) : hpoly_of.`b i 0 = - bound_of i.
Proof. by rewrite hpoly_of_b !mxE. Qed.

Lemma hpoly_of_bE0 (i : 'I_m) : hpoly_of.`b i ord0 = - bound_of i.
Proof. exact: hpoly_of_bE. Qed.

Lemma colA_row (r : 'I_m) : \col_k hpoly_of.`A r k = - normal_of r.
Proof. by apply/colP => k; rewrite hpoly_of_A !mxE. Qed.

Lemma in_hpoly_of (x : 'cV[R]_d) :
  reflect (forall i : 'I_m, '[normal_of i, x] <= bound_of i) (x \in hpoly_of).
Proof.
rewrite in_hpolyE /lev; apply: (iffP forallP) => h i; move: (h i);
  by rewrite -row_vdot row_hpoly_of vdotNl hpoly_of_bE ler_opp2.
Qed.

(* The remaining hypothesis of [CC.certificate_correctness]: nonzero normals. *)
Lemma normal_of_neq0 (hineq : L.areInequalitiesWellFormed c) (i : 'I_m) :
  @H.normalVector d R hpoly_of i <> 0.
Proof.
rewrite normalVector_hpoly_of => /eqP; rewrite oppr_eq0 => /eqP h0.
have hlen := ineqs_len hineq; have hnorm := normal_len hineq i.
move: hineq; rewrite /L.areInequalitiesWellFormed; cbv zeta.
move=> /andP[_ /(for_all_composeP _ _ hlen)/(_ i)]; cbv beta => /(existP _ hnorm)[j hj].
have hj0 : bigZ2R R (aget (L.normal (ineq_of i)) j) = 0.
  by have := congr1 (fun v : 'cV[R]_d => v j 0) h0; rewrite /normal_of vec_of_arrayE mxE.
by move: hj; cbv beta; rewrite ?nbE (bigZ_eqbE R) bigZ2R_0 hj0 eqxx.
Qed.

Definition vertex_of (v : 'I_nv) : L.Vertex := baget (L.vertices c) v.
Definition point_of_vertex (v : 'I_nv) : 'cV[R]_d := point_of R d (L.point (vertex_of v)).
Definition points_of : {fset 'cV[R]_d} := [fset point_of_vertex v | v : 'I_nv]%fset.
Definition activeSet_of (v : 'I_nv) : {set 'I_m} := set_of_array m (L.activeSet (vertex_of v)).

(* Well-formedness of the vertices, in bridge form. *)
Lemma point_num_len (v : 'I_nv) : L.arePointsWellFormed c ->
  alen (L.numerators (L.point (vertex_of v))) = d.
Proof.
by rewrite /L.arePointsWellFormed; cbv zeta => /andP[_ /bfor_all_compose_balenP/(_ v)/hasLengthP].
Qed.

Lemma point_den_neq0 (v : 'I_nv) : L.arePointsWellFormed c ->
  ~~ (L.commonDenominator (L.point (vertex_of v)) =? 0)%bigN.
Proof.
rewrite /L.arePointsWellFormed; cbv zeta => /andP[/bfor_all_compose_balenP/(_ v) h _].
by move: h; rewrite /Basics.compose /vertex_of; cbv beta.
Qed.

Lemma activeSet_sorted (v : 'I_nv) : L.areActiveSetsWellFormed c ->
  L.isStrictlySorted Uint63.ltb (L.activeSet (vertex_of v)).
Proof.
rewrite /L.areActiveSetsWellFormed; cbv zeta.
by move=> /andP[/bfor_all_compose_balenP/(_ v) h _].
Qed.

(* Active sets are indexed by vertex in the certificate but by point in the
   high-level spec; two vertices may share a point, hence the union. *)
Definition activeSets_of (x : 'cV[R]_d) : {set 'I_m} :=
  \bigcup_(v : 'I_nv | point_of_vertex v == x) activeSet_of v.

Lemma in_points_of x : reflect (exists v : 'I_nv, point_of_vertex v = x) (x \in points_of).
Proof.
rewrite /points_of; apply: (iffP idP) => [/imfsetP [v _ ->]|[v <-]]; first by exists v.
by apply/imfsetP; exists v.
Qed.

(* Facets: the certificate's descriptions, as sets of inequality indices.
   Vertex indices are dereferenced directly. *)
Local Notation nf := (balen (L.facets c)).

Definition facet_of (k : 'I_nf) : L.Facet := baget (L.facets c) k.
Definition desc_of (k : 'I_nf) : {set 'I_m} := set_of_array m (L.description (facet_of k)).
Definition facets_of : {set {set 'I_m}} := [set desc_of k | k : 'I_nf].
Definition point_at (i : int) : 'cV[R]_d := point_of R d (L.point (BigArray.get (L.vertices c) i)).

Lemma point_at_ord (x : int) (hx : (nat_of_int x < nv)%N) : point_at x = point_of_vertex (Ordinal hx).
Proof.
by rewrite /point_of_vertex /vertex_of /baget -[nat_of_ord (Ordinal hx)]/(nat_of_int x) nat_of_intK.
Qed.

(* The facet graph: the descriptions of adjacent facet indices are adjacent. *)
Definition nbrs (k : 'I_nf) : {set 'I_nf} := set_of_array nf (baget (L.graph c) k).
Definition gedge (f f' : {set 'I_m}) : bool :=
  [exists k : 'I_nf, [exists w : 'I_nf, [&& desc_of k == f, desc_of w == f' & w \in nbrs k]]].
Definition gvertices : {fset {set 'I_m}} := [fset desc_of k | k : 'I_nf]%fset.
Definition graph_of : graph [choiceType of {set 'I_m}] := mk_graph gvertices gedge.

Lemma vtx_graph_of : vertices graph_of = gvertices.
Proof. exact: vtx_mk_graph. Qed.

Lemma in_succ_of (k0 : 'I_nf) f' :
  (f' \in successors graph_of (desc_of k0))
  = [&& f' != desc_of k0, f' \in gvertices & gedge (desc_of k0) f'].
Proof.
rewrite succ_mk_graph; last by apply/imfsetP; exists k0.
by rewrite in_fsetD1 in_fset inE.
Qed.

(* The geometric graph: certified points are adjacent when some pair of vertex
   indices carrying them is adjacent in the certificate's geometric graph. *)
Definition geom_nbrs (v : 'I_nv) : {set 'I_nv} := set_of_array nv (baget (L.geom_graph c) v).
Definition pedge (x y : 'cV[R]_d) : bool :=
  [exists v : 'I_nv, [exists w : 'I_nv,
     [&& point_of_vertex v == x, point_of_vertex w == y & w \in geom_nbrs v]]].
Definition geom_graph_of : graph [choiceType of 'cV[R]_d] := mk_graph points_of pedge.

Lemma vtx_geom_graph_of : vertices geom_graph_of = points_of.
Proof. exact: vtx_mk_graph. Qed.

Lemma in_succ_geom (x y : 'cV[R]_d) : x \in points_of ->
  (y \in successors geom_graph_of x) = [&& y != x, y \in points_of & pedge x y].
Proof.
move=> hx; rewrite succ_mk_graph //.
by rewrite in_fsetD1 in_fset inE.
Qed.

(* The root: special simplex, special vertex and witnesses. Witnesses are
   negated, like the polytope's [A]: with [A = -normals] this is what makes the
   high-level T4/T5 inner products equal to the checker's <n_i, W_j>. *)
Local Notation root := (L.root c).
Local Notation kstar := (L.simplexIndex root).
Local Notation fstar := (BigArray.get (L.facets c) kstar).
Local Notation vstar := (L.mapping fstar).
Local Notation dstar := (L.description fstar).
Local Notation astar := (L.activeSet (BigArray.get (L.vertices c) vstar)).
Local Notation W := (L.witnesses root).
Local Notation SP := (L.scalarProducts root).
Local Notation AI := (L.activeInverse root).

Definition specialVertex_of : 'cV[R]_d := point_at vstar.

(* The high-level [mapping] is a function on sets: pick any facet index with
   that description (facets are unique in a well-formed certificate, and the
   checks hold for every index anyway). Off the facets the value must differ
   from [specialVertex_of] -- otherwise [H.weightsAreStrictlyPositiveVectors]
   would demand a nonzero weight there -- hence the [+ const_mx 1] shift, a
   genuine shift as soon as [0 < d]. *)
Definition mapping_of (f : {set 'I_m}) : 'cV[R]_d :=
  if [pick k : 'I_nf | desc_of k == f] is Some k then point_at (L.mapping (facet_of k))
  else specialVertex_of + const_mx 1.
Definition specialSimplex_of (hm : (0 < m)%N) (i : 'I_d) : 'I_m :=
  insubd (Ordinal hm) (nat_of_int (aget dstar i)).

(* The high-level flag data is a function on points: pick any vertex index
   carrying the point (certified points are unique in a well-formed
   certificate). Off the certified points the value is immaterial: no
   condition constrains it. A flag row stores local positions into the
   vertex's active set (first component) and witness vertex indices (second
   component). *)
Definition flag_indices_of (hm : (0 < m)%N) (x : 'cV[R]_d) (i : 'I_d) : 'I_m :=
  if [pick v : 'I_nv | point_of_vertex v == x] is Some v then
    insubd (Ordinal hm)
      (nat_of_int (PArray.get (L.activeSet (vertex_of v))
         (PArray.get (fst (L.flag (vertex_of v))) (int_of_nat i))))
  else Ordinal hm.

Definition flag_vertices_of (x : 'cV[R]_d) (i : 'I_d) : 'cV[R]_d :=
  if [pick v : 'I_nv | point_of_vertex v == x] is Some v then
    point_at (PArray.get (snd (L.flag (vertex_of v))) (int_of_nat i))
  else 0.
Definition witnesses_of : 'M[R]_(d, d) :=
  - \matrix_(i < d, j < d) bigZ2R R (aget (aget W j) i).

Lemma col_witnesses_of (j : 'I_d) : col j witnesses_of = - vec_of_array R d (aget W j).
Proof. by apply/colP => i; rewrite !mxE. Qed.

Lemma col_Wmat (j : 'I_d) :
  col j (\matrix_(i < d, j' < d) bigZ2R R (aget (aget W j') i)) = vec_of_array R d (aget W j).
Proof. by apply/colP => i; rewrite !mxE. Qed.

Local Notation Wt := (L.weights root).

(* Facets visited by the separability check: not the root facet, mapped to the
   special vertex; [rank k] is the checker's running counter when it visits k. *)
Definition qual (k : nat) : bool :=
  ~~ (int_of_nat k =? kstar)%uint63
  && (L.mapping (BigArray.get (L.facets c) (int_of_nat k)) =? vstar)%uint63.
Definition rank (k : nat) : nat := count qual (iota 0 k).

Lemma rankS k : rank k.+1 = (rank k + qual k)%N.
Proof. by rewrite /rank -addn1 iotaD count_cat /= add0n addn0. Qed.

Lemma rank_lt_nf (k : nat) : (k < nf)%N -> (rank k < nf)%N.
Proof. by move=> hk; apply: (leq_ltn_trans (count_size _ _)); rewrite size_iota. Qed.

(* Weights are defined exactly on the facets the checker visits (0 elsewhere),
   so T5's premises [mapping f = specialVertex] and [f != specialSimplex @: 'I_d]
   are not needed for T5 itself. *)
Definition weights_of (f : {set 'I_m}) : 'cV[R]_d :=
  if [pick k : 'I_nf | (desc_of k == f) && qual k] is Some k
  then sparse_of R d (PArray.get Wt (int_of_nat (rank k))) else 0.

(* The weight consumed at facet [k] exists and is well formed. *)
Lemma weight_rank_lt (k : 'I_nf) : L.areWeightsWellFormed c -> qual k -> (rank k < alen Wt)%N.
Proof.
move=> hwt hq.
move: hwt; rewrite /L.areWeightsWellFormed; cbv zeta => /andP[]; rewrite eqb_natE bcountiE.
rewrite -[nat_of_int (length Wt)]/(alen Wt) => /eqP -> _.
have hsplit : forall n, (k <= n)%N ->
    count qual (iota 0 n) = (count qual (iota 0 k) + count qual (iota k (n - k)))%N.
  by move=> n hkn; rewrite -{1}(subnKC hkn) iotaD count_cat add0n.
rewrite -[X in count X _]/qual /rank (hsplit _ (ltnW (ltn_ord k))).
rewrite -addn1 leq_add2l -has_count; apply/hasP; exists (val k) => //.
by rewrite mem_iota leqnn (subnKC (ltnW (ltn_ord k))) ltn_ord.
Qed.

Lemma weight_wf (k : 'I_nf) : L.areWeightsWellFormed c -> qual k ->
  L.isSparseVectorWellFormed (L.dimension c) (PArray.get Wt (int_of_nat (rank k))).
Proof.
move=> hwt hq; have hrank := weight_rank_lt hwt hq.
move: hwt; rewrite /L.areWeightsWellFormed; cbv zeta.
by move=> /andP[_ /for_all_alenP/(_ (Ordinal hrank))]; rewrite /aget.
Qed.

(* Sparse weights: indices in range, coordinates nonnegative, vector nonzero. *)
Lemma sparse_idx (hd : (0 < d)%N) (w : L.Weight) : L.isSparseVectorWellFormed (L.dimension c) w ->
  forall p : 'I_(alen w), (nat_of_int (aget w p).1 < d)%N.
Proof.
rewrite /L.isSparseVectorWellFormed => /andP[/andP[/for_all_alenP h _] _] p.
have := h p; case: (aget w p) => [a z] /= h2.
by have h3 := inRangeP hd h2; exact: h3.
Qed.

Lemma sparse_of_ge0 (w : L.Weight) :
  L.for_all (fun '(_, x) => (0 <=? x)%bigZ) w -> lev 0 (sparse_of R d w).
Proof.
move/for_all_alenP => h; apply/forallP => j; rewrite !mxE; apply: sumr_ge0 => p _.
by have := h p; case: (aget w p) => [a z] /=; rewrite ?nbE (bigZ_lebE R) bigZ2R_0.
Qed.

Lemma sparse_of_neq0 (w : L.Weight) : (0 < alen w)%N ->
  (forall p : 'I_(alen w), (nat_of_int (aget w p).1 < d)%N) ->
  L.for_all (fun '(_, x) => (0 <=? x)%bigZ) w -> L.for_all (fun '(_, x) => ~~ (0 =? x)%bigZ) w ->
  sparse_of R d w <> 0.
Proof.
move=> h0 hidx /for_all_alenP hge /for_all_alenP hne heq0.
pose p0 : 'I_(alen w) := Ordinal h0.
pose j0 : 'I_d := Ordinal (hidx p0).
have hterm : forall p : 'I_(alen w), 0 <= bigZ2R R (aget w p).2.
  by move=> p; have := hge p; case: (aget w p) => [a z] /=; rewrite ?nbE (bigZ_lebE R) bigZ2R_0.
have := congr1 (fun v : 'cV[R]_d => v j0 0) heq0; rewrite /sparse_of !mxE.
move/(psumr_eq0P (fun p _ => hterm p)) => /(_ p0 (eqxx _)).
move: (hne p0); case: (aget w p0) => [a z] /=; rewrite ?nbE (bigZ_eqbE R) bigZ2R_0 => hz hz0.
by rewrite hz0 eqxx in hz.
Qed.

(* Full-dimension data: a point [num / D] and [d] directions [dir_i / D] (the
   checker tests the points [(num + dir_i) / D]), with the certified inverse. *)
Local Notation fdpt := (L.fullDimPoint (L.full_dim c)).
Local Notation fddir := (L.fullDimDir (L.full_dim c)).
Local Notation fdinv := (L.fullDimInverse (L.full_dim c)).
Local Notation fdden := (bigZ2R R (BigZ.Pos (L.commonDenominator fdpt))).

Definition full_dim_point_of : 'cV[R]_d := point_of R d fdpt.
Definition full_dim_dir_of : 'M[R]_(d, d) :=
  \matrix_(k < d, i < d) (bigZ2R R (aget (aget fddir i) k) / fdden).
Definition full_dim_inv_of : 'M[R]_(d, d) :=
  \matrix_(k < d, j < d) bigZ2R R (aget (aget fdinv j) k).

Lemma col_full_dim_dir_of (i : 'I_d) :
  col i full_dim_dir_of = fdden^-1 *: vec_of_array R d (aget fddir i).
Proof. by apply/colP => k; rewrite !mxE mulrC. Qed.

Lemma col_full_dim_inv_of (j : 'I_d) : col j full_dim_inv_of = vec_of_array R d (aget fdinv j).
Proof. by apply/colP => k; rewrite !mxE. Qed.

(* [hm : 0 < m] inhabits 'I_m for [specialSimplex_of] (out-of-range entries,
   excluded by well-formedness, fall back to that inhabitant). *)
Definition interp_cert (hm : (0 < m)%N) : H.Certificate R d :=
  @H.Build_Certificate R d hpoly_of points_of
    full_dim_point_of full_dim_dir_of full_dim_inv_of
    activeSets_of facets_of mapping_of
    graph_of                       (* graph *)
    specialVertex_of (specialSimplex_of hm) witnesses_of weights_of
    (flag_indices_of hm)
    flag_vertices_of
    geom_graph_of.                 (* geom_graph *)

(* -------------------------------------------------------------------------- *)
(* Index well-formedness, in bridge form                                      *)
(* -------------------------------------------------------------------------- *)

(* A vertex index in range, as an ordinal; [0 < nv] is needed because
   [inRange 0 (nv - 1)] wraps around when there are no vertices. *)
Lemma mapping_ord (hnv : (0 < nv)%N) (k : 'I_nf) :
  L.isMappingWellFormed c -> (nat_of_int (L.mapping (facet_of k)) < nv)%N.
Proof.
rewrite /L.isMappingWellFormed; cbv zeta => /bfor_all_compose_balenP/(_ k) h.
by have h2 := inRangeP hnv h; exact: h2.
Qed.

Lemma desc_len (k : 'I_nf) : L.areDescriptionsWellFormed c -> alen (L.description (facet_of k)) = d.
Proof.
rewrite /L.areDescriptionsWellFormed; cbv zeta.
by move=> /andP[_ /bfor_all_compose_balenP/(_ k)/hasLengthP].
Qed.

Lemma desc_range (hm : (0 < m)%N) (k : 'I_nf) : L.areDescriptionsWellFormed c ->
  forall p : 'I_(alen (L.description (facet_of k))),
    (nat_of_int (aget (L.description (facet_of k)) p) < m)%N.
Proof.
rewrite /L.areDescriptionsWellFormed; cbv zeta => /andP[/andP[_ hB] _].
by have h2 := ballInRange_ordP (k := k) hm hB; exact: h2.
Qed.

Lemma desc_sorted (k : 'I_nf) : L.areDescriptionsWellFormed c ->
  L.isStrictlySorted Uint63.ltb (L.description (facet_of k)).
Proof.
rewrite /L.areDescriptionsWellFormed; cbv zeta.
by move=> /andP[/andP[/bfor_all_compose_balenP/(_ k) h _] _].
Qed.

Lemma kstar_ord (hnf : (0 < nf)%N) : L.isSimplexIndexWellFormed c -> (nat_of_int kstar < nf)%N.
Proof.
rewrite /L.isSimplexIndexWellFormed; cbv zeta => h.
by have h2 := inRangeP hnf h; exact: h2.
Qed.

Lemma facet_of_kstar (hk : (nat_of_int kstar < nf)%N) : facet_of (Ordinal hk) = fstar.
Proof. by rewrite /facet_of /baget -[nat_of_ord (Ordinal hk)]/(nat_of_int kstar) nat_of_intK. Qed.

(* The special simplex is the root facet's description. *)
Lemma specialSimplex_img (hm : (0 < m)%N) (hk : (nat_of_int kstar < nf)%N)
    (hdesc : L.areDescriptionsWellFormed c) :
  specialSimplex_of hm @: 'I_d = desc_of (Ordinal hk).
Proof.
have hlen : alen dstar = d by rewrite -(facet_of_kstar hk); exact: desc_len _ hdesc.
have hrange : forall p : 'I_(alen dstar), (nat_of_int (aget dstar p) < m)%N.
  by have := desc_range hm hdesc (k := Ordinal hk); rewrite (facet_of_kstar hk).
rewrite /desc_of (facet_of_kstar hk).
apply/setP => x; apply/idP/idP => [/imsetP[i _ ->]|/in_set_of_array[j hj]].
  have hi : (nat_of_int (aget dstar i) < m)%N := hrange (cast_ord (esym hlen) i).
  have -> : specialSimplex_of hm i = Ordinal hi.
    by apply/val_inj; rewrite /specialSimplex_of val_insubd hi.
  by apply/in_set_of_array; exists (cast_ord (esym hlen) i).
apply/imsetP; exists (cast_ord hlen j); first by rewrite ?in_setT.
have hj' : (nat_of_int (aget dstar (cast_ord hlen j)) < m)%N := hrange j.
by apply/val_inj; rewrite /specialSimplex_of val_insubd hj' /= -hj.
Qed.

Lemma graph_len : L.isGraphWellFormed c -> balen (L.graph c) = nf.
Proof.
rewrite /L.isGraphWellFormed; cbv zeta => /andP[/andP[/andP[hl _] _] _].
by rewrite eqb_balenE in hl; move/eqP: hl => hl; exact: hl.
Qed.

Lemma nbrs_ord (hg : L.isGraphWellFormed c) (k : 'I_nf) (j : 'I_(alen (baget (L.graph c) k))) :
  (nat_of_int (aget (baget (L.graph c) k) j) < nf)%N.
Proof.
have hlen := graph_len hg; have hnf : (0 < nf)%N := leq_ltn_trans (leq0n _) (ltn_ord k).
move: hg; rewrite /L.isGraphWellFormed; cbv zeta => /andP[/andP[/andP[_ hv] _] _].
have h2 := bvertex_matrixP hlen hnf hv; exact: (h2 k j).
Qed.

(* Every adjacency row has exactly [d] entries (first conjunct of [L.graph_check]):
   one neighbour per ridge of the facet. *)
Lemma row_len (hg : L.isGraphWellFormed c) (k : 'I_nf) :
  L.bfor_all (L.hasLength (L.dimension c)) (L.graph c) -> alen (baget (L.graph c) k) = d.
Proof.
by move=> /(bfor_allP _ (graph_len hg))/(_ k)/hasLengthP.
Qed.

Lemma nbrs_len (hg : L.isGraphWellFormed c) (k : 'I_nf) :
  L.bfor_all (L.hasLength (L.dimension c)) (L.graph c) -> (alen (baget (L.graph c) k) <= d)%N.
Proof. by move/(row_len hg k) => ->. Qed.

Lemma nbrs_irrefl (hg : L.isGraphWellFormed c) (k : 'I_nf) : k \notin nbrs k.
Proof.
have hlen := graph_len hg; move: hg.
rewrite /L.isGraphWellFormed; cbv zeta => /andP[/andP[_ hnl] _].
move: hnl => /(bhasNoLoopsP hlen)/(_ k).
rewrite /L.bhasLocallyNoLoop bagetE /L.mem; apply: contra.
rewrite /nbrs => /in_set_of_array[j hj].
apply/exist_alenP; exists j; cbv beta; rewrite eqb_natE hj.
by rewrite (int_of_natK_le (i := blength (L.facets c)) (ltnW (ltn_ord k))) eqxx.
Qed.

Lemma nbrs_sym (hg : L.isGraphWellFormed c) (k w : 'I_nf) : w \in nbrs k -> k \in nbrs w.
Proof.
have hlen := graph_len hg; move: hg.
rewrite /L.isGraphWellFormed; cbv zeta => /andP[_ hu].
move: hu => /(bisUndirectedP hlen)/(_ k).
rewrite /L.bisLocallyUndirected bagetE => /for_all_alenP hk /in_set_of_array[j hj].
have hw : baget (L.graph c) w = BigArray.get (L.graph c) (aget (baget (L.graph c) k) j).
  by rewrite /baget -hj nat_of_intK.
have := hk j; cbv beta; rewrite /L.mem => /exist_alenP[p hp].
rewrite /nbrs hw; apply/in_set_of_array; exists p.
move: hp; cbv beta; rewrite eqb_natE => /eqP <-.
exact: int_of_natK_le (ltnW (ltn_ord k)).
Qed.

Lemma activeSet_range (hm : (0 < m)%N) (v : 'I_nv) : L.areActiveSetsWellFormed c ->
  forall p : 'I_(alen (L.activeSet (vertex_of v))),
    (nat_of_int (aget (L.activeSet (vertex_of v)) p) < m)%N.
Proof.
rewrite /L.areActiveSetsWellFormed; cbv zeta => /andP[_ hB].
by have h2 := ballInRange_ordP (k := v) hm hB; exact: h2.
Qed.

(* The flag rows: [d] local active-set positions and [d] witness indices. *)
Lemma flagsP (v : 'I_nv) : L.areFlagsWellFormed c ->
  [/\ alen (fst (L.flag (vertex_of v))) = d,
      alen (snd (L.flag (vertex_of v))) = d,
      L.allInRange Uint63.leb 0%uint63
        (PArray.length (L.activeSet (vertex_of v)) - 1)%uint63
        (fst (L.flag (vertex_of v)))
    & L.allInRange Uint63.leb 0%uint63
        (BigArray.length (L.vertices c) - 1)%uint63
        (snd (L.flag (vertex_of v)))].
Proof.
rewrite /L.areFlagsWellFormed; cbv zeta => /bfor_all_balenP/(_ v); cbv beta.
case E : (L.flag (baget (L.vertices c) v)) => [ineq wit].
move=> /andP[/andP[/andP[/hasLengthP hl1 /hasLengthP hl2] hr1] hr2].
split; [exact: hl1 | exact: hl2 | exact: hr1 | exact: hr2].
Qed.

(* [allInRange] wraps on an empty active set, so the local positions are only
   meaningful when the active set is nonempty; the positivity is taken as a
   hypothesis where needed. *)
Lemma flag_ineq_range (v : 'I_nv) (i : 'I_d) :
  L.areFlagsWellFormed c -> (0 < alen (L.activeSet (vertex_of v)))%N ->
  (nat_of_int (PArray.get (fst (L.flag (vertex_of v))) (int_of_nat i))
   < alen (L.activeSet (vertex_of v)))%N.
Proof.
move=> hfw h0; have [hl1 _ hr1 _] := flagsP v hfw.
move: hr1; rewrite /L.allInRange => /for_all_alenP h.
have hi : (i < alen (fst (L.flag (vertex_of v))))%N by rewrite hl1; exact: ltn_ord.
have := h (Ordinal hi); cbv beta => hin.
by have h2 := inRangeP h0 hin; exact: h2.
Qed.

Lemma flag_wit_range (hnv : (0 < nv)%N) (v : 'I_nv) (i : 'I_d) :
  L.areFlagsWellFormed c ->
  (nat_of_int (PArray.get (snd (L.flag (vertex_of v))) (int_of_nat i)) < nv)%N.
Proof.
move=> hfw; have [_ hl2 _ hr2] := flagsP v hfw.
move: hr2; rewrite /L.allInRange => /for_all_alenP h.
have hi : (i < alen (snd (L.flag (vertex_of v))))%N by rewrite hl2; exact: ltn_ord.
have := h (Ordinal hi); cbv beta => hin.
by have h2 := inRangeP hnv hin; exact: h2.
Qed.

(* The same for the geometric graph, whose rows are indexed by vertices. *)
Lemma geom_graph_len : L.isGeomGraphWellFormed c -> balen (L.geom_graph c) = nv.
Proof.
rewrite /L.isGeomGraphWellFormed; cbv zeta => /andP[/andP[/andP[hl _] _] _].
by rewrite eqb_balenE in hl; move/eqP: hl => hl; exact: hl.
Qed.

Lemma geom_nbrs_ord (hg : L.isGeomGraphWellFormed c) (v : 'I_nv)
    (j : 'I_(alen (baget (L.geom_graph c) v))) :
  (nat_of_int (aget (baget (L.geom_graph c) v) j) < nv)%N.
Proof.
have hlen := geom_graph_len hg.
have hnv : (0 < nv)%N := leq_ltn_trans (leq0n _) (ltn_ord v).
move: hg; rewrite /L.isGeomGraphWellFormed; cbv zeta => /andP[/andP[/andP[_ hv] _] _].
have h2 := bvertex_matrixP hlen hnv hv; exact: (h2 v j).
Qed.

Lemma geom_nbrs_irrefl (hg : L.isGeomGraphWellFormed c) (v : 'I_nv) : v \notin geom_nbrs v.
Proof.
have hlen := geom_graph_len hg; move: hg.
rewrite /L.isGeomGraphWellFormed; cbv zeta => /andP[/andP[_ hs] _].
move: hs => /bisSimpleGraph_loops/(bhasNoLoopsP hlen)/(_ v).
rewrite /L.bhasLocallyNoLoop bagetE /L.mem; apply: contra; rewrite /geom_nbrs
  => /in_set_of_array[j hj].
apply/exist_alenP; exists j; cbv beta; rewrite eqb_natE hj.
by rewrite (int_of_natK_le (i := blength (L.vertices c)) (ltnW (ltn_ord v))) eqxx.
Qed.

Lemma geom_nbrs_sym (hg : L.isGeomGraphWellFormed c) (v w : 'I_nv) :
  w \in geom_nbrs v -> v \in geom_nbrs w.
Proof.
have hlen := geom_graph_len hg; move: hg.
rewrite /L.isGeomGraphWellFormed; cbv zeta => /andP[_ hu].
move: hu => /(bisUndirectedP hlen)/(_ v).
rewrite /L.bisLocallyUndirected bagetE => /for_all_alenP hk /in_set_of_array[j hj].
have hw : baget (L.geom_graph c) w
          = BigArray.get (L.geom_graph c) (aget (baget (L.geom_graph c) v) j).
  by rewrite /baget -hj nat_of_intK.
have := hk j; cbv beta; rewrite /L.mem => /exist_alenP[p hp].
rewrite /geom_nbrs hw; apply/in_set_of_array; exists p.
move: hp; cbv beta; rewrite eqb_natE => /eqP <-.
exact: int_of_natK_le (ltnW (ltn_ord v)).
Qed.

(* Adjacency of certified points is symmetric. *)
Lemma geom_edges_sym (hg : L.isGeomGraphWellFormed c) (x y : 'cV[R]_d) :
  edges geom_graph_of x y -> edges geom_graph_of y x.
Proof.
move=> he.
have hx : x \in points_of by have := edge_vtxl he; rewrite vtx_geom_graph_of.
have hy : y \in points_of by have := edge_vtxr he; rewrite vtx_geom_graph_of.
move: he; rewrite /geom_graph_of !edge_mk_graph // => /andP[hne hpe].
rewrite eq_sym hne /=.
move: hpe => /existsP[v1 /existsP[w1 /and3P[hp1 hpw hnb]]].
apply/existsP; exists w1; apply/existsP; exists v1.
by rewrite hpw hp1 (geom_nbrs_sym hg hnb).
Qed.


(* The source / local-target tables describing each geometric edge's preimage. *)
Lemma geom_src_len : L.areGeomEdgeSourcesWellFormed c -> balen (L.geom_edge_sources c) = nv.
Proof.
rewrite /L.areGeomEdgeSourcesWellFormed; cbv zeta => /andP[/andP[hl _] _].
by rewrite eqb_balenE in hl; move/eqP: hl => hl; exact: hl.
Qed.

Lemma geom_src_row_len (hs : L.areGeomEdgeSourcesWellFormed c) (v : 'I_nv) :
  alen (baget (L.geom_edge_sources c) v) = alen (baget (L.geom_graph c) v).
Proof.
have hlen := geom_src_len hs; move: hs.
rewrite /L.areGeomEdgeSourcesWellFormed; cbv zeta => /andP[/andP[_ hrow] _].
move: hrow => /(bfor_alliP _ hlen)/(_ v); cbv beta => /hasLengthP h.
by rewrite h.
Qed.

Lemma geom_src_range (hnf : (0 < nf)%N) (hs : L.areGeomEdgeSourcesWellFormed c) (v : 'I_nv)
    (j : 'I_(alen (baget (L.geom_edge_sources c) v))) :
  (nat_of_int (aget (baget (L.geom_edge_sources c) v) j) < nf)%N.
Proof.
have hlen := geom_src_len hs; move: hs.
rewrite /L.areGeomEdgeSourcesWellFormed; cbv zeta => /andP[_ hr].
move: hr => /(bfor_allP _ hlen)/(_ v); cbv beta; rewrite /L.allInRange => /for_all_alenP/(_ j) h.
by have h2 := inRangeP hnf h; exact: h2.
Qed.

Lemma geom_tgt_len :
  L.areGeomEdgeLocalTargetsWellFormed c -> balen (L.geom_edge_local_targets c) = nv.
Proof.
rewrite /L.areGeomEdgeLocalTargetsWellFormed; cbv zeta => /andP[/andP[hl _] _].
by rewrite eqb_balenE in hl; move/eqP: hl => hl; exact: hl.
Qed.

Lemma geom_tgt_row_len (ht : L.areGeomEdgeLocalTargetsWellFormed c) (v : 'I_nv) :
  alen (baget (L.geom_edge_local_targets c) v) = alen (baget (L.geom_graph c) v).
Proof.
have hlen := geom_tgt_len ht; move: ht.
rewrite /L.areGeomEdgeLocalTargetsWellFormed; cbv zeta => /andP[/andP[_ hrow] _].
move: hrow => /(bfor_alliP _ hlen)/(_ v); cbv beta => /hasLengthP h.
by rewrite h.
Qed.

Lemma geom_tgt_range (ht : L.areGeomEdgeLocalTargetsWellFormed c) (v : 'I_nv)
    (j : 'I_(alen (baget (L.geom_edge_local_targets c) v))) :
  (0 < alen (BigArray.get (L.graph c)
        (PArray.get (baget (L.geom_edge_sources c) v) (int_of_nat j))))%N ->
  (nat_of_int (aget (baget (L.geom_edge_local_targets c) v) j)
   < alen (BigArray.get (L.graph c)
        (PArray.get (baget (L.geom_edge_sources c) v) (int_of_nat j))))%N.
Proof.
move=> h0; have hlen := geom_tgt_len ht; move: ht.
rewrite /L.areGeomEdgeLocalTargetsWellFormed; cbv zeta => /andP[_ hr].
move: hr => /bfor_alli_matrix_balenP h.
have hh := h (cast_ord (esym hlen) v) j.
have hin : L.inRange Uint63.leb 0%uint63
    (length (BigArray.get (L.graph c)
       (PArray.get (baget (L.geom_edge_sources c) v) (int_of_nat j))) - 1)%uint63
    (aget (baget (L.geom_edge_local_targets c) v) j) := hh.
by have h2 := inRangeP h0 hin; exact: h2.
Qed.

(* -------------------------------------------------------------------------- *)
(* The feasibility check, per vertex                                          *)
(* -------------------------------------------------------------------------- *)

Lemma check_ineqsP (v : L.Vertex) :
  alen (L.inequalities c) = m ->
  (forall i : 'I_m, alen (L.normal (ineq_of i)) = d) ->
  alen (L.numerators (L.point v)) = d ->
  ~~ (L.commonDenominator (L.point v) =? 0)%bigN ->
  L.isStrictlySorted Uint63.ltb (L.activeSet v) ->
  reflect (forall i : 'I_m,
             if i \in set_of_array m (L.activeSet v)
             then '[normal_of i, point_of R d (L.point v)] = bound_of i
             else '[normal_of i, point_of R d (L.point v)] < bound_of i)
          (L.check_ineqs (L.inequalities c) (L.activeSet v) (L.point v)).
Proof.
move=> hlen hnorm hnum hden hsorted; rewrite /L.check_ineqs.
have hden' := bigN2R_gt0 R hden.
set den := bigZ2R R (BigZ.Pos (L.commonDenominator (L.point v))).
have hdot i : bigZ2R R (L.array_bigZ_dot (L.normal (ineq_of i)) (L.numerators (L.point v)))
              = '[normal_of i, vec_of_array R d (L.numerators (L.point v))]
  := array_bigZ_dotE R (hnorm i) hnum.
have hb i : bigZ2R R (L.bound (ineq_of i) * BigZ.Pos (L.commonDenominator (L.point v)))%bigZ
            = bound_of i * den
  := bigZ2R_mul R _ _.
have hpt i : '[normal_of i, point_of R d (L.point v)]
             = '[normal_of i, vec_of_array R d (L.numerators (L.point v))] / den
  := vdot_point_of _ _.
apply: (iffP (for_all_alt_alenP _ _ hlen (isStrictlySorted_mono hsorted))) => h i; move: (h i);
  cbv beta; case: (i \in _).
- by rewrite ?nbE (bigZ_eqbE R) hdot hb => hE; apply/eqP; rewrite hpt eq_divr_mulr.
- by rewrite ?nbE (bigZ_ltbE R) hdot hb hpt ltr_pdivr_mulr.
- by move/eqP; rewrite hpt eq_divr_mulr // ?nbE (bigZ_eqbE R) hdot hb.
- by rewrite hpt ltr_pdivr_mulr // ?nbE (bigZ_ltbE R) hdot hb.
Qed.

Lemma feasibility_checkP :
  reflect (forall v : 'I_nv,
             L.check_ineqs (L.inequalities c) (L.activeSet (vertex_of v)) (L.point (vertex_of v)))
          (L.feasibility_check c).
Proof.
rewrite /L.feasibility_check; cbv zeta.
by apply: (iffP (@bfor_all_balenP _ _ (L.vertices c))) => h v; have := h v; cbv beta.
Qed.

(* The per-vertex content of the feasibility check: the active set is exactly
   the set of tight inequalities. *)
Lemma vertex_active :
  L.areInequalitiesWellFormed c -> L.arePointsWellFormed c -> L.areActiveSetsWellFormed c ->
  L.feasibility_check c ->
  forall (v : 'I_nv) (i : 'I_m),
    if i \in activeSet_of v then '[normal_of i, point_of_vertex v] = bound_of i
    else '[normal_of i, point_of_vertex v] < bound_of i.
Proof.
move=> hineq hpts hact /feasibility_checkP hchk v.
apply/(check_ineqsP (ineqs_len hineq) (normal_len hineq) (point_num_len v hpts)
                    (point_den_neq0 v hpts) (activeSet_sorted v hact)).
exact: hchk v.
Qed.

Lemma activeSet_ofE :
  L.areInequalitiesWellFormed c -> L.arePointsWellFormed c -> L.areActiveSetsWellFormed c ->
  L.feasibility_check c -> forall v : 'I_nv,
  activeSet_of v = [set i : 'I_m | '[normal_of i, point_of_vertex v] == bound_of i].
Proof.
move=> hineq hpts hact hfeas v; apply/setP => i; rewrite inE; have := vertex_active hineq hpts hact hfeas v i.
by case: (i \in activeSet_of v) => [-> | /lt_eqF ->]; rewrite ?eqxx.
Qed.

(* -------------------------------------------------------------------------- *)
(* Uniqueness: facets, active sets, certified points                          *)
(* ([sorted_sets_inj], from the bridges, does the work for the first two.)    *)
(* -------------------------------------------------------------------------- *)

(* Facets are unique: the descriptions are [ltbArray]-increasing along the
   facet array, hence pairwise distinct as sets. *)
Lemma desc_of_inj (hm : (0 < m)%N) :
  L.areDescriptionsWellFormed c -> L.areFacetsUnique c -> injective desc_of.
Proof.
move=> hdesc huniq.
have h := bsorted_sets_inj (g := L.description) (s := L.facets c) (n := m) huniq
            (fun k => desc_sorted k hdesc) (fun k => desc_range hm hdesc (k := k)).
exact: h.
Qed.

Lemma facet_of_ord (i : int) (hi : (nat_of_int i < nf)%N) :
  facet_of (Ordinal hi) = BigArray.get (L.facets c) i.
Proof. by rewrite /facet_of /baget nat_of_intK. Qed.

Lemma mapping_of_desc (hm : (0 < m)%N) (k : 'I_nf) :
  L.areDescriptionsWellFormed c -> L.areFacetsUnique c ->
  mapping_of (desc_of k) = point_at (L.mapping (facet_of k)).
Proof.
move=> hdesc hfu; rewrite /mapping_of.
case: pickP => [k' /eqP /(desc_of_inj hm hdesc hfu) ->|/(_ k)] //.
by rewrite eqxx.
Qed.


Lemma activeSet_of_inj (hm : (0 < m)%N) :
  L.areActiveSetsWellFormed c -> L.areActiveSetsUnique c -> injective activeSet_of.
Proof.
move=> hact huniq.
have h := bsorted_sets_inj (g := L.activeSet) (s := L.vertices c) (n := m) huniq
            (fun v => activeSet_sorted v hact) (fun v => activeSet_range hm hact (v := v)).
exact: h.
Qed.

Lemma point_of_vertex_inj (hm : (0 < m)%N) :
  L.areInequalitiesWellFormed c -> L.arePointsWellFormed c -> L.areActiveSetsWellFormed c ->
  L.areActiveSetsUnique c -> L.feasibility_check c -> injective point_of_vertex.
Proof.
move=> hineq hpts hact hasu hfeas v1 v2 heq; apply: (activeSet_of_inj hm hact hasu).
by rewrite !(activeSet_ofE hineq hpts hact hfeas) heq.
Qed.

(* At a certified point, the high-level active set is the vertex's. *)
Lemma activeSets_of_vertex (hm : (0 < m)%N) :
  L.areInequalitiesWellFormed c -> L.arePointsWellFormed c -> L.areActiveSetsWellFormed c ->
  L.areActiveSetsUnique c -> L.feasibility_check c ->
  forall v : 'I_nv, activeSets_of (point_of_vertex v) = activeSet_of v.
Proof.
move=> hineq hpts hact hasu hfeas v; rewrite /activeSets_of.
rewrite (eq_bigl (pred1 v)) ?big_pred1_eq // => v' /=.
apply/idP/idP => [/eqP he|/eqP ->]; last exact: eqxx.
by apply/eqP; apply: (point_of_vertex_inj hm hineq hpts hact hasu hfeas); exact: he.
Qed.

(* -------------------------------------------------------------------------- *)
(* Active-set differences: the [L.diff] list read at the set level            *)
(* -------------------------------------------------------------------------- *)

(* Every index the diff produces is an index of [v]'s active set, hence < m. *)
Lemma diff_lt_m (hm : (0 < m)%N) (v w : 'I_nv) : L.areActiveSetsWellFormed c ->
  forall x, x \in map nat_of_int
      (L.diff Uint63.ltb (L.activeSet (vertex_of v)) (L.activeSet (vertex_of w))) ->
    (x < m)%N.
Proof.
move=> hact x hx.
have [[p [hp hpx]] _] := diff_arr_mem (activeSet_sorted v hact) (activeSet_sorted w hact) hx.
have h2 := activeSet_range hm hact (v := v) (Ordinal hp).
by rewrite -hpx; exact: h2.
Qed.

(* The diff list computes exactly the set difference of the active sets. *)
Lemma diff_seq_setE (hm : (0 < m)%N) (v w : 'I_nv) : L.areActiveSetsWellFormed c ->
  forall x : 'I_m,
    (nat_of_ord x \in map nat_of_int
       (L.diff Uint63.ltb (L.activeSet (vertex_of v)) (L.activeSet (vertex_of w))))
    = (x \in activeSet_of v :\: activeSet_of w).
Proof.
move=> hact x; apply/idP/idP => [hx|].
  have [hsrc hnotb] := diff_arr_mem (activeSet_sorted v hact) (activeSet_sorted w hact) hx.
  rewrite in_setD; apply/andP; split.
    apply/negP => /in_set_of_array[q hq].
    by have := hnotb q (ltn_ord q); rewrite hq.
  have [p [hp hpx]] := hsrc.
  by apply/in_set_of_array; exists (Ordinal hp); exact: hpx.
rewrite in_setD => /andP[hnb /in_set_of_array[p hp]].
have hda := @diff_arr_all (L.activeSet (vertex_of v)) (L.activeSet (vertex_of w)).
have [hin|[q [hq hqx]]] := hda _ (ltn_ord p).
  by rewrite -hp; exact: hin.
exfalso; move/negP: hnb; apply; apply/in_set_of_array; exists (Ordinal hq).
by rewrite /aget hqx; exact: hp.
Qed.

(* -------------------------------------------------------------------------- *)
(* The scalar-products check, in bridge form (used by T4 and T5)              *)
(* -------------------------------------------------------------------------- *)

(* The scalar-products table, read through the inverse active map at an index
   [x] of the special vertex's active set, is the inner product of the normal
   of inequality [x] with the witnesses. *)
Lemma sp_AI_entry (x : int) (j : 'I_d) :
  L.areInequalitiesWellFormed c -> L.isActiveInverseWellFormed c ->
  L.areWitnessesWellFormed c -> L.areScalarProductsWellFormed c ->
  L.scalarProducts_check c ->
  (exists q, (q < alen astar)%N /\ PArray.get astar (int_of_nat q) = x) ->
  (nat_of_int x < m)%N ->
  bigZ2R R (PArray.get (PArray.get SP (PArray.get AI x)) (int_of_nat j))
  = '[vec_of_array R d (L.normal (PArray.get (L.inequalities c) x)), vec_of_array R d (aget W j)].
Proof.
move=> hineq hai hw hsp hspc [q [hq hqx]] hxm.
(* the inverse active map sends x back to its position q *)
have hAI : PArray.get AI x = int_of_nat q.
  move: hai; rewrite /L.isActiveInverseWellFormed; cbv zeta.
  move=> /andP[_ /for_alli_alenP/(_ (Ordinal hq))]; cbv beta.
  by rewrite -[aget astar (Ordinal hq)]/(PArray.get astar (int_of_nat q)) hqx => /Uint63.eqb_correct.
(* the scalar-products table at (q, j) *)
have hSPlen : alen SP = alen astar.
  by move: hsp; rewrite /L.areScalarProductsWellFormed; cbv zeta => /andP[]; rewrite eqb_natE => /eqP.
have hq' : (q < alen SP)%N by rewrite hSPlen.
have hSProw : alen (aget SP (Ordinal hq')) = d.
  move: hsp; rewrite /L.areScalarProductsWellFormed; cbv zeta.
  by move=> /andP[_ /for_all_alenP/(_ (Ordinal hq'))/hasLengthP].
have hj : (j < alen (aget SP (Ordinal hq')))%N by rewrite hSProw.
have hspE : bigZ2R R (aget (aget SP (Ordinal hq')) (Ordinal hj))
  = bigZ2R R (L.array_bigZ_dot (L.normal (PArray.get (L.inequalities c) x)) (PArray.get W (int_of_nat j))).
  move: hspc; rewrite /L.scalarProducts_check; cbv zeta.
  move=> /for_alli_matrixP/(_ (Ordinal hq'))/(_ (Ordinal hj)); cbv beta.
  rewrite ?nbE (bigZ_eqbE R) -[int_of_nat (Ordinal hq')]/(int_of_nat q) -[int_of_nat (Ordinal hj)]/(int_of_nat j).
  by rewrite hqx => /eqP.
(* lengths for the dot product *)
have hlen := ineqs_len hineq.
have hna : alen (L.normal (PArray.get (L.inequalities c) x)) = d.
  move: hineq; rewrite /L.areInequalitiesWellFormed; cbv zeta.
  move=> /andP[/andP[_ /(for_all_composeP _ _ hlen)/(_ (Ordinal hxm)) hB] _]; move: hB.
  by rewrite /L.hasLength eqb_natE /aget -[nat_of_ord (Ordinal hxm)]/(nat_of_int x) nat_of_intK => /eqP.
have hWlen : alen W = d.
  by move: hw; rewrite /L.areWitnessesWellFormed; cbv zeta => /andP[]; rewrite eqb_natE => /eqP.
have hnw : alen (aget W j) = d.
  move: hw; rewrite /L.areWitnessesWellFormed; cbv zeta.
  by move=> /andP[_ /(for_allP _ hWlen)/(_ j)/hasLengthP].
rewrite hAI -[PArray.get (PArray.get SP (int_of_nat q)) (int_of_nat j)]/(aget (aget SP (Ordinal hq')) (Ordinal hj)).
by rewrite hspE (array_bigZ_dotE R hna hnw).
Qed.

(* Same, with an int column index. *)
Lemma sp_AI_entry_int (x a : int) :
  L.areInequalitiesWellFormed c -> L.isActiveInverseWellFormed c ->
  L.areWitnessesWellFormed c -> L.areScalarProductsWellFormed c ->
  L.scalarProducts_check c ->
  (exists q, (q < alen astar)%N /\ PArray.get astar (int_of_nat q) = x) ->
  (nat_of_int x < m)%N -> (nat_of_int a < d)%N ->
  bigZ2R R (PArray.get (PArray.get SP (PArray.get AI x)) a)
  = '[vec_of_array R d (L.normal (PArray.get (L.inequalities c) x)),
      vec_of_array R d (PArray.get W a)].
Proof.
move=> hineq hai hw hsp hspc hx hxm ha.
have := sp_AI_entry (Ordinal ha) hineq hai hw hsp hspc hx hxm.
by rewrite /aget -[nat_of_ord (Ordinal ha)]/(nat_of_int a) nat_of_intK.
Qed.

(* -------------------------------------------------------------------------- *)
(* T1: feasibility                                                            *)
(* -------------------------------------------------------------------------- *)

Theorem feasibility_check_correct (hm : (0 < m)%N) :
  L.areInequalitiesWellFormed c -> L.arePointsWellFormed c -> L.areActiveSetsWellFormed c ->
  L.feasibility_check c -> @H.feasibility_check d R (interp_cert hm).
Proof.
move=> hineq hpts hact hfeas; have hvert := vertex_active hineq hpts hact hfeas.
have hin : forall v (i : 'I_m), i \in activeSet_of v -> '[normal_of i, point_of_vertex v] = bound_of i.
  by move=> v i hi; have := hvert v i; rewrite hi.
have hout : forall v (i : 'I_m), i \notin activeSet_of v -> '[normal_of i, point_of_vertex v] < bound_of i.
  by move=> v i hi; have := hvert v i; rewrite (negbTE hi).
rewrite /H.feasibility_check /interp_cert /H.activeSets.
split=> [x /in_points_of [v <-]|x /in_points_of [v0 <-]].
  apply/in_hpoly_of => i; case hi: (i \in activeSet_of v).
    by rewrite (hin v i hi) lexx.
  exact: ltW (hout v i (negbT hi)).
have hT : forall v : 'I_nv, point_of_vertex v == point_of_vertex v0 ->
  activeSet_of v
  = [set i : 'I_m | '[@H.normalVector d R hpoly_of i, point_of_vertex v0] == hpoly_of.`b i ord0].
  move=> v /eqP <-; apply/setP => i; case hi: (i \in activeSet_of v).
    by rewrite inE normalVector_hpoly_of vdotNl hpoly_of_bE0 eqr_opp (hin v i hi) eqxx.
  by rewrite inE normalVector_hpoly_of vdotNl hpoly_of_bE0 eqr_opp (lt_eqF (hout v i (negbT hi))).
apply/setP => i; apply/bigcupP/idP => [[v hv hi]|hi].
  by rewrite -(hT v hv).
by exists v0; [rewrite eqxx | rewrite (hT v0 (eqxx _))].
Qed.

(* -------------------------------------------------------------------------- *)
(* T2: mapping                                                                *)
(* -------------------------------------------------------------------------- *)

Theorem mapping_check_correct (hm : (0 < m)%N) (hnv : (0 < nv)%N) :
  L.isMappingWellFormed c -> L.mapping_check c -> @H.mapping_check d R (interp_cert hm).
Proof.
move=> hmapwf; rewrite /L.mapping_check; cbv zeta => /bfor_all_balenP hchk.
rewrite /H.mapping_check /interp_cert /H.facets /H.mapping /H.activeSets.
move=> f /imsetP[k _ ->]; rewrite /mapping_of.
case: pickP => [k' /eqP <-|/(_ k)]; last by rewrite eqxx.
set v0 : 'I_nv := Ordinal (mapping_ord hnv k' hmapwf).
have hv0 : vertex_of v0 = BigArray.get (L.vertices c) (L.mapping (facet_of k')).
  by rewrite /vertex_of /baget -[nat_of_ord v0]/(nat_of_int (L.mapping (facet_of k'))) nat_of_intK.
apply: (subset_trans _ (bigcup_sup v0 _)); last by rewrite /point_of_vertex hv0.
by apply: subset_arr; have := hchk k'; cbv beta; rewrite -hv0.
Qed.

(* -------------------------------------------------------------------------- *)
(* T3: the facet graph                                                        *)
(* -------------------------------------------------------------------------- *)

Theorem graph_check_correct (hm : (0 < m)%N) :
  L.isGraphWellFormed c -> L.areDescriptionsWellFormed c -> L.areFacetsUnique c ->
  L.graph_check c -> @H.graph_check d R (interp_cert hm).
Proof.
move=> hg hdesc huniq; rewrite /L.graph_check; cbv zeta => /andP[hreg hridge].
have hinj := desc_of_inj hm hdesc huniq.
rewrite /H.graph_check /interp_cert /H.graph vtx_graph_of => f /imfsetP[k0 _ ->].
split.
- have hsub : successors graph_of (desc_of k0) \subset desc_of @: nbrs k0.
    apply/subsetP => f'; rewrite in_succ_of => /and3P[_ _ hE].
    move: hE => /existsP[k /existsP[w /and3P[/eqP hk /eqP hw hnb]]].
    by rewrite -hw; apply: imset_f; rewrite -(hinj _ _ hk).
  apply: (leq_trans (subset_leq_card hsub)); apply: (leq_trans (leq_imset_card desc_of (nbrs k0))).
  have h := leq_trans (card_set_of_array nf (baget (L.graph c) k0)) (nbrs_len hg k0 hreg).
  exact: h.
- move=> i /in_set_of_array[j hj].
  have hd := desc_len k0 hdesc; have hr := row_len hg k0 hreg.
  have hj' : (j < alen (baget (L.graph c) k0))%N by rewrite hr -hd.
  pose w_int := aget (baget (L.graph c) k0) (Ordinal hj').
  have hw : (nat_of_int w_int < nf)%N := nbrs_ord hg (Ordinal hj').
  pose w : 'I_nf := Ordinal hw.
  have hwn : w \in nbrs k0 by apply/in_set_of_array; exists (Ordinal hj').
  have hfw : facet_of w = BigArray.get (L.facets c) w_int by rewrite -(nat_of_intK w_int).
  have hri : L.isRidgeInFacet (L.description (facet_of k0)) (L.description (facet_of w))
               (aget (L.description (facet_of k0)) j).
    rewrite hfw; move: hridge => /(bfor_alliP _ (graph_len hg))/(_ k0); cbv beta zeta.
    by move=> /(for_alliP _ erefl)/(_ (Ordinal hj')); cbv beta zeta.
  exists (desc_of w); split.
    rewrite in_succ_of; apply/and3P; split; last first.
    + by apply/existsP; exists k0; apply/existsP; exists w; rewrite !eqxx hwn.
    + by apply/imfsetP; exists w.
    apply/eqP => /hinj hwk; move: hwn; rewrite hwk.
    by rewrite (negbTE (nbrs_irrefl hg k0)).
  have h := ridge_subset hj hri; exact: h.
Qed.

(* -------------------------------------------------------------------------- *)
(* T4: inversibility                                                          *)
(* -------------------------------------------------------------------------- *)

(* T4's instance: [x] is the [i]-th entry of the root facet's description. *)
Lemma sp_entry (hm : (0 < m)%N) (hnf : (0 < nf)%N) :
  L.areInequalitiesWellFormed c -> L.areDescriptionsWellFormed c ->
  L.isSimplexIndexWellFormed c -> L.isActiveInverseWellFormed c ->
  L.areWitnessesWellFormed c -> L.areScalarProductsWellFormed c ->
  L.mapping_check c -> L.scalarProducts_check c ->
  forall i j : 'I_d,
    bigZ2R R (PArray.get (PArray.get SP (PArray.get AI (PArray.get dstar (int_of_nat i))))
                         (int_of_nat j))
    = '[normal_of (specialSimplex_of hm i), vec_of_array R d (aget W j)].
Proof.
move=> hineq hdesc hsi hai hw hsp hmap hspc i j.
set k0 : 'I_nf := Ordinal (kstar_ord hnf hsi).
have hf0 : facet_of k0 = fstar := facet_of_kstar _.
have hdlen : alen dstar = d by rewrite -hf0; exact: desc_len.
have hdi : (i < alen dstar)%N by rewrite hdlen.
have hdi0 : (i < alen (L.description (facet_of k0)))%N by rewrite hf0.
have hrange : (nat_of_int (aget dstar i) < m)%N.
  have := desc_range hm (k := k0) hdesc (Ordinal hdi0).
  by rewrite -[aget (L.description (facet_of k0)) _]/(PArray.get (L.description (facet_of k0)) (int_of_nat i)) hf0.
have hval : nat_of_ord (specialSimplex_of hm i) = nat_of_int (aget dstar i).
  by rewrite /specialSimplex_of; exact: insubdK.
have hineq_sp : ineq_of (specialSimplex_of hm i) = PArray.get (L.inequalities c) (aget dstar i).
  by rewrite /ineq_of {1}/aget hval nat_of_intK.
have hsubset : L.subset Uint63.ltb dstar astar.
  move: hmap; rewrite /L.mapping_check; cbv zeta => /bfor_all_balenP/(_ k0).
  by cbv beta; rewrite -/(facet_of k0) hf0.
have [q [hq hqi]] := subset_arr_all hsubset hdi.
rewrite (sp_AI_entry j hineq hai hw hsp hspc (ex_intro _ q (conj hq hqi)) hrange).
by rewrite /normal_of hineq_sp.
Qed.

Theorem inversibility_check_correct (hm : (0 < m)%N) (hnf : (0 < nf)%N) :
  L.areInequalitiesWellFormed c -> L.areDescriptionsWellFormed c ->
  L.isSimplexIndexWellFormed c -> L.isActiveInverseWellFormed c ->
  L.areWitnessesWellFormed c -> L.areScalarProductsWellFormed c ->
  L.mapping_check c -> L.scalarProducts_check c -> L.inversibility_check c ->
  @H.inversibility_check d R (interp_cert hm).
Proof.
move=> hineq hdesc hsi hai hw hsp hmap hspc hinv.
have hE := sp_entry hm hnf hineq hdesc hsi hai hw hsp hmap hspc.
(* the root facet's description has length d *)
have hdlen : alen dstar = d.
  by rewrite -(facet_of_kstar (kstar_ord hnf hsi)); exact: desc_len.
rewrite /H.inversibility_check /interp_cert /H.specialSimplex /H.witnesses.
move=> i j; rewrite colA_row col_witnesses_of vdotNl vdotNr opprK.
(* No [done] on goals mentioning bigZ operations: it would try to reduce them. *)
have hii : nat_of_int (int_of_nat i) = i.
  by apply: (int_of_natK_le (i := L.dimension c)); exact: ltnW (ltn_ord i).
have hjj : nat_of_int (int_of_nat j) = j.
  by apply: (int_of_natK_le (i := L.dimension c)); exact: ltnW (ltn_ord j).
have hi' : (i < alen dstar)%N by rewrite hdlen.
move: hinv; rewrite /L.inversibility_check; cbv zeta => /for_alli_alenP/(_ (Ordinal hi')).
cbv beta; rewrite -[int_of_nat (Ordinal hi')]/(int_of_nat i).
move=> /ifor_all_range0P/(_ j); cbv beta; rewrite eqb_natE hii hjj.
(* Name the checker's table entry and get its value by typing (conversion),
   not by rewriting: the checker's [get@{Set}] and a [get] spelled in a tactic
   carry different universe instances and never unify. *)
set X := PArray.get (PArray.get SP (PArray.get AI (aget dstar (Ordinal hi')))) (int_of_nat j).
have hX : bigZ2R R X = '[normal_of (specialSimplex_of hm i), vec_of_array R d (aget W j)] := hE i j.
case: (altP (i =P j)) => [hij|hne].
  have -> : (i == j :> nat) by rewrite hij.
  rewrite ?nbE (bigZ_ltbE R) bigZ2R_0 hX => h; left; split=> //; exact: h.
rewrite val_eqE (negbTE hne) ?nbE (bigZ_eqbE R) bigZ2R_0 eq_sym hX => /eqP h; right; split; last exact: h.
exact/eqP.
Qed.

(* -------------------------------------------------------------------------- *)
(* Support for T5 and the weight positivity: the separability fold            *)
(* -------------------------------------------------------------------------- *)

(* The check performed on a visited facet [k], with the counter at [r]. *)
#[local] Definition wcheck (k : nat) (r : int) : bool :=
  L.for_all (fun i =>
      L.isSparseVectorPositive (PArray.get Wt r)
      && (L.sparse_array_bigZ_dot (PArray.get Wt r) (PArray.get SP (PArray.get AI i)) <=? 0)%bigZ)
    (L.description (BigArray.get (L.facets c) (int_of_nat k))).

(* One step of the separability fold, as produced by [ifoldE]. *)
#[local] Definition sstep5 (acc : bool * int) (k : nat) : bool * int :=
  if qual k then let '(res, idx) := acc in (res && wcheck k acc.2, (idx + 1)%uint63) else acc.

#[local] Definition INV5 (k : nat) (acc : bool * int) :=
  acc.2 = int_of_nat (rank k) /\
  (acc.1 -> forall k', (k' < k)%N -> qual k' -> wcheck k' (int_of_nat (rank k'))).

Lemma sstep5_inv k acc : (k < nf)%N -> INV5 k acc -> INV5 k.+1 (sstep5 acc k).
Proof.
move=> hk; case: acc => [b r]; rewrite /INV5 /sstep5 rankS /= => -[h2 h1]; case hq: (qual k) => /=; last first.
  rewrite addn0; split=> // hacc k'; rewrite ltnS leq_eqVlt => /orP[/eqP->|hk'] hq'.
    by rewrite hq' in hq.
  exact: h1.
rewrite addn1; split.
  rewrite h2; apply: (int_of_natS (M := BigArray.length (L.facets c))).
  by rewrite balenE; exact: rank_lt_nf.
move=> /andP[hacc hw] k'; rewrite ltnS leq_eqVlt => /orP[/eqP->|hk'] hq'; last exact: h1.
by rewrite -h2.
Qed.

Lemma foldl_sstep5_inv m k acc :
  (k + m <= nf)%N -> INV5 k acc -> INV5 (k + m) (foldl sstep5 acc (iota k m)).
Proof.
elim: m k acc => [|m ih] k acc hkm hinv; first by rewrite addn0.
rewrite -[iota k m.+1]/(k :: iota k.+1 m)
        -[foldl _ _ (_ :: _)]/(foldl sstep5 (sstep5 acc k) (iota k.+1 m)).
rewrite addnS -addSn; apply: ih; first by rewrite addSn -addnS.
by apply: sstep5_inv => //; rewrite (leq_trans _ hkm) // addnS ltnS leq_addr.
Qed.

Lemma separabilityP : L.separability_check c ->
  forall k : 'I_nf, qual k -> wcheck k (int_of_nat (rank k)).
Proof.
have -> : L.separability_check c = (foldl sstep5 (true, 0%uint63) (iota 0 nf)).1.
  by rewrite /L.separability_check; cbv zeta; rewrite bfoldiE; cbv beta.
have hinv0 : INV5 0 (true, 0%uint63).
  by split; [rewrite /rank /= int_of_nat0 | move=> _ k'; rewrite ltn0].
have := foldl_sstep5_inv (m := nf) (k := 0) (acc := (true, 0%uint63)) (leqnn _) hinv0.
by rewrite add0n => -[_ h1] hok k hq; exact: h1 hok k (ltn_ord k) hq.
Qed.

(* -------------------------------------------------------------------------- *)
(* T5: separability                                                           *)
(* -------------------------------------------------------------------------- *)

Theorem separability_check_correct (hm : (0 < m)%N) :
  L.areInequalitiesWellFormed c ->
  L.isActiveInverseWellFormed c -> L.areWitnessesWellFormed c ->
  L.areScalarProductsWellFormed c -> L.areWeightsWellFormed c ->
  L.mapping_check c -> L.scalarProducts_check c -> L.separability_check c ->
  @H.separability_check d R (interp_cert hm).
Proof.
move=> hineq hai hw hsp hwt hmap hspc hsep.
rewrite /H.separability_check /interp_cert /H.mapping /H.specialVertex
        /H.specialSimplex /H.witnesses /H.weights.
move=> f _ _ i hif.
rewrite /weights_of; case: pickP => [k /andP[/eqP hdk hq]|_]; last first.
  by rewrite mulmx0 vdot0l lexx.
set w := PArray.get Wt (int_of_nat (rank k)).
(* i is an entry of the description of k *)
move: hif; rewrite -hdk => /in_set_of_array [p hp].
set x := aget (L.description (facet_of k)) p.
have hxi : x = int_of_nat i by rewrite -hp nat_of_intK.
have hxm : (nat_of_int x < m)%N by rewrite /x hp.
(* the checker's inequality at x *)
have hle : bigZ2R R (L.sparse_array_bigZ_dot w (PArray.get SP (PArray.get AI x))) <= 0.
  have := separabilityP hsep hq; rewrite /wcheck => /for_all_alenP/(_ p); cbv beta.
  by move=> /andP[_]; rewrite ?nbE (bigZ_lebE R) bigZ2R_0.
(* x is an active index of the special vertex *)
have hmk : L.mapping (facet_of k) = vstar.
  by move: hq => /andP[_ hq']; exact: Uint63.eqb_correct.
have hsubset : L.subset Uint63.ltb (L.description (facet_of k)) astar.
  move: hmap; rewrite /L.mapping_check; cbv zeta => /bfor_all_balenP/(_ k); cbv beta.
  by rewrite -/(facet_of k) -[(facet_of k).2]/(L.mapping (facet_of k)) hmk.
have [q [hq' hqx]] := subset_arr_all hsubset (ltn_ord p).
(* dimension 0: nothing to prove *)
have [hd0|hd] := posnP d.
  rewrite /vdot big1 // => -[r hr] _.
  suff: (r < 0)%N by rewrite ltn0.
  by rewrite -hd0.
(* sparse indices are in range *)
have hwf : L.isSparseVectorWellFormed (L.dimension c) w := weight_wf hwt hq.
have hidx := sparse_idx hd hwf.
(* assemble *)
rewrite mulNmx vdotNl normalVector_hpoly_of vdotNr opprK vdot_mulmx.
rewrite (eq_bigr (fun j => sparse_of R d w j 0 * '[vec_of_array R d (aget W j), normal_of i]));
  last by move=> j _; rewrite col_Wmat.
rewrite sum_sparse_of.
rewrite (eq_bigr (fun p' => bigZ2R R (aget w p').2
                            * '[vec_of_array R d (aget W (Ordinal (hidx p'))), normal_of i]));
  last by move=> p' _; rewrite (big_ord_eq _ (hidx p')).
have hterm : forall p' : 'I_(alen w),
    bigZ2R R (PArray.get (PArray.get SP (PArray.get AI x)) (aget w p').1)
    = '[vec_of_array R d (aget W (Ordinal (hidx p'))), normal_of i].
  move=> p'.
  rewrite (sp_AI_entry_int hineq hai hw hsp hspc (ex_intro _ q (conj hq' hqx)) hxm (hidx p')) vdotC.
  have -> : aget W (Ordinal (hidx p')) = PArray.get W (aget w p').1.
    by rewrite {1}/aget -[nat_of_ord (Ordinal (hidx p'))]/(nat_of_int (aget w p').1) nat_of_intK.
  by rewrite /normal_of /ineq_of /aget -hxi.
move: hle; rewrite sparse_array_bigZ_dotE => hle.
have -> : \sum_(p' < alen w) bigZ2R R (aget w p').2
                              * '[vec_of_array R d (aget W (Ordinal (hidx p'))), normal_of i]
        = \sum_(p' < alen w) bigZ2R R (aget w p').2
                              * bigZ2R R (PArray.get (PArray.get SP (PArray.get AI x)) (aget w p').1).
  by apply: eq_bigr => p' _; rewrite hterm.
exact: hle.
Qed.

(* -------------------------------------------------------------------------- *)
(* High-level well-formedness (CertificateCorrectness.well_formedness_check)  *)
(* -------------------------------------------------------------------------- *)

Lemma facetsAreDSimplices_correct (hm : (0 < m)%N) : L.areDescriptionsWellFormed c ->
  @H.facetsAreDSimplices d R (interp_cert hm).
Proof.
move=> hdesc; rewrite /H.facetsAreDSimplices /interp_cert /H.facets => f /imsetP[k _ ->].
by rewrite /desc_of (card_set_of_array_sorted (desc_sorted k hdesc) (desc_range hm hdesc))
  (desc_len k hdesc) eqxx.
Qed.

Lemma graphVerticesAreFacets_correct (hm : (0 < m)%N) :
  @H.graphVerticesAreFacets d R (interp_cert hm).
Proof.
rewrite /H.graphVerticesAreFacets /interp_cert /H.graph /H.facets vtx_graph_of => f.
by apply/imfsetP/imsetP => -[k _ ->]; exists k; rewrite ?in_setT.
Qed.

Lemma mappingHasImageInPoints_correct (hm : (0 < m)%N) (hnv : (0 < nv)%N) : L.isMappingWellFormed c ->
  @H.mappingHasImageInPoints d R (interp_cert hm).
Proof.
move=> hmapwf; rewrite /H.mappingHasImageInPoints /interp_cert /H.facets /H.mapping.
move=> f /imsetP[k _ ->]; rewrite /mapping_of; case: pickP => [k' _|/(_ k)]; last by rewrite eqxx.
set v0 : 'I_nv := Ordinal (mapping_ord hnv k' hmapwf).
apply/in_points_of; exists v0.
by rewrite /point_of_vertex /vertex_of /baget -[nat_of_ord v0]/(nat_of_int (L.mapping (facet_of k'))) nat_of_intK.
Qed.

Lemma graphIsUndirected_correct (hm : (0 < m)%N) : L.isGraphWellFormed c ->
  @H.graphIsUndirected d R (interp_cert hm).
Proof.
move=> hg; rewrite /H.graphIsUndirected /interp_cert /H.graph.
suff hsym : forall x y, y \in successors graph_of x -> x \in successors graph_of y.
  by move=> x y; split; exact: hsym.
move=> x y hxy; have hx : x \in gvertices by rewrite -vtx_graph_of; exact: edge_vtxl hxy.
move: hxy; move/imfsetP: hx => [k0 _ ->]; rewrite in_succ_of.
move=> /and3P[hne _ /existsP[k /existsP[w /and3P[/eqP hk /eqP hw hnb]]]].
rewrite -hw in hne *; rewrite in_succ_of; apply/and3P; split.
- by rewrite eq_sym.
- by apply/imfsetP; exists k0.
- by apply/existsP; exists w; apply/existsP; exists k; rewrite hk !eqxx (nbrs_sym hg hnb).
Qed.

Lemma specialSimplexInSpecialCone_correct (hm : (0 < m)%N) (hnf : (0 < nf)%N) :
  L.isSimplexIndexWellFormed c -> L.areDescriptionsWellFormed c -> L.areFacetsUnique c ->
  @H.specialSimplexInSpecialCone d R (interp_cert hm).
Proof.
move=> hsi hdesc huniq; have hk := kstar_ord hnf hsi.
rewrite /H.specialSimplexInSpecialCone /interp_cert /H.specialSimplex /H.facets /H.mapping
  /H.specialVertex (specialSimplex_img hm hk hdesc); split.
  by apply/imsetP; exists (Ordinal hk); rewrite ?in_setT.
by rewrite (mapping_of_desc hm _ hdesc huniq) (facet_of_kstar hk).
Qed.

Lemma weightsAreStrictlyPositiveVectors_correct (hm : (0 < m)%N) (hnv : (0 < nv)%N)
    (hnf : (0 < nf)%N) (hd : (0 < d)%N) :
  L.areInequalitiesWellFormed c -> L.arePointsWellFormed c -> L.areActiveSetsWellFormed c ->
  L.areDescriptionsWellFormed c -> L.isMappingWellFormed c -> L.isSimplexIndexWellFormed c ->
  L.areWeightsWellFormed c -> L.areActiveSetsUnique c ->
  L.feasibility_check c -> L.separability_check c ->
  @H.weightsAreStrictlyPositiveVectors d R (interp_cert hm).
Proof.
move=> hineq hpts hact hdesc hmapwf hsi hwt hasu hfeas hsep; have hk := kstar_ord hnf hsi.
rewrite /H.weightsAreStrictlyPositiveVectors /interp_cert /H.mapping /H.specialVertex
  /H.specialSimplex /H.weights (specialSimplex_img hm hk hdesc) => f.
rewrite /mapping_of; case: pickP => [k /eqP hdk|_]; last first.
  (* not a facet: [mapping_of] returns [specialVertex_of + const_mx 1], which
     differs from [specialVertex_of] since [0 < d], so the premise is absurd *)
  move=> heq _; exfalso.
  have h1 : const_mx 1 = (0 : 'cV[R]_d) by apply: (addrI specialVertex_of); rewrite addr0.
  by have := congr1 (fun v : 'cV[R]_d => v (Ordinal hd) 0) h1; rewrite !mxE => /eqP; rewrite oner_eq0.
(* the facet is mapped to the special vertex, as an index *)
have hv2 : (nat_of_int vstar < nv)%N.
  by have := mapping_ord hnv (Ordinal hk) hmapwf; rewrite (facet_of_kstar hk).
rewrite /specialVertex_of (point_at_ord (mapping_ord hnv k hmapwf)) (point_at_ord hv2).
move/(point_of_vertex_inj hm hineq hpts hact hasu hfeas)/(congr1 val) => /= hmk0.
have hmk : L.mapping (facet_of k) = vstar := nat_of_int_inj hmk0.
rewrite -hdk => hne.
(* hence the checker visited it *)
have hq : qual k.
  rewrite /qual !eqb_natE (int_of_natK_le (ltnW (ltn_ord k))) hmk eqxx andbT.
  apply: contra hne => /eqP hkk.
  by apply/eqP; congr desc_of; apply/val_inj; rewrite /= hkk.
rewrite /weights_of; case: pickP => [k' /andP[/eqP hdk' hq']|/(_ k)]; last by rewrite eqxx hq.
set w := PArray.get Wt (int_of_nat (rank k')).
have hwf : L.isSparseVectorWellFormed (L.dimension c) w := weight_wf hwt hq'.
have hpos : L.isSparseVectorPositive w.
  have hd' : (0 < alen (L.description (facet_of k')))%N by rewrite (desc_len k' hdesc).
  have := separabilityP hsep hq'; rewrite /wcheck => /for_all_alenP/(_ (Ordinal hd')); cbv beta.
  by move=> /andP[h _]; exact: h.
move: hpos; rewrite /L.isSparseVectorPositive => /andP[hlen0 hge].
move: hlen0; rewrite ltb_natE nat_of_int0 -[nat_of_int (length w)]/(alen w) => hlen0.
move: (hwf); rewrite /L.isSparseVectorWellFormed => /andP[_ hne0].
split; first exact: sparse_of_ge0 hge.
exact: sparse_of_neq0 hlen0 (sparse_idx hd hwf) hge hne0.
Qed.

(* -------------------------------------------------------------------------- *)
(* Full dimension                                                             *)
(* -------------------------------------------------------------------------- *)

Theorem full_dim_check_correct (hm : (0 < m)%N) :
  L.areInequalitiesWellFormed c -> L.isFullDimWellFormed c -> L.full_dim_check c ->
  @H.full_dim_check d R (interp_cert hm).
Proof.
move=> hineq hfd; rewrite /L.full_dim_check => /andP[hfeas hinv].
have hlen := ineqs_len hineq; have hnorm := normal_len hineq.
move: hfd; rewrite /L.isFullDimWellFormed /L.isFullDimPointWellFormed /L.isFullDimDirWellFormed
  /L.isFullDimInverseWellFormed; cbv zeta.
move=> /andP[/andP[/andP[hden /hasLength_alen hnum] /andP[/hasLength_alen hdirl hdirs]]
  /andP[/hasLength_alen hinvl hinvs]].
have hdirs' := rows_len hdirl hdirs; have hinvs' := rows_len hinvl hinvs.
have hden' : 0 < fdden := bigN2R_gt0 R hden.
have hb i : bigZ2R R (L.bound (ineq_of i) * BigZ.Pos (L.commonDenominator fdpt))%bigZ
            = bound_of i * fdden := bigZ2R_mul R _ _.
rewrite /H.full_dim_check /interp_cert /H.full_dim_point /H.full_dim_dir /H.full_dim_inv.
move: hfeas; rewrite /L.full_dim_feasibility_check; cbv zeta => /andP[hf1 hf2]; split; last split.
- (* the point *)
  apply/in_hpoly_of => i; have := (for_allP _ hlen hf2) i; cbv beta.
  have hdot : bigZ2R R (L.array_bigZ_dot (L.normal (ineq_of i)) (L.numerators fdpt))
              = '[normal_of i, vec_of_array R d (L.numerators fdpt)] := array_bigZ_dotE R (hnorm i) hnum.
  rewrite ?nbE (bigZ_lebE R) hdot hb /full_dim_point_of vdot_point_of.
  by rewrite ler_pdivr_mulr.
- (* the point shifted along each direction *)
  move=> k; apply/in_hpoly_of => i.
  have := (for_allP _ hlen ((for_allP _ hdirl hf1) k)) i; cbv beta.
  have hdot : bigZ2R R (L.array_bigZ_add_dot (L.normal (ineq_of i)) (L.numerators fdpt) (aget fddir k))
              = '[normal_of i, vec_of_array R d (L.numerators fdpt) + vec_of_array R d (aget fddir k)]
    := array_bigZ_add_dotE R (hnorm i) hnum (hdirs' k).
  rewrite ?nbE (bigZ_lebE R) hdot hb col_full_dim_dir_of /full_dim_point_of /point_of -scalerDr vdotZr.
  by move=> h; rewrite mulrC ler_pdivr_mulr.
- (* the inverse *)
  have hdot i j : bigZ2R R (L.array_bigZ_dot (aget fddir i) (aget fdinv j))
                  = '[vec_of_array R d (aget fddir i), vec_of_array R d (aget fdinv j)]
    := array_bigZ_dotE R (hdirs' i) (hinvs' j).
  have hnz i j : ('[col i full_dim_dir_of, col j full_dim_inv_of] == 0)
                 = (L.array_bigZ_dot (aget fddir i) (aget fdinv j) =? 0)%bigZ.
    rewrite col_full_dim_dir_of col_full_dim_inv_of vdotZl -hdot mulf_eq0 invr_eq0 (gt_eqF hden') /=.
    by rewrite ?nbE (bigZ_eqbE R) bigZ2R_0.
  move=> i j; move/for_alli_matrixP: hinv => hinv.
  pose i' : 'I_(alen fdinv) := cast_ord (esym hinvl) i.
  pose j' : 'I_(alen (aget fdinv i')) := cast_ord (esym (hinvs' i)) j.
  have hi' : nat_of_int (int_of_nat i') = i := int_of_natK_le (ltnW (ltn_ord i')).
  have hj' : nat_of_int (int_of_nat j') = j := int_of_natK_le (ltnW (ltn_ord j')).
  have h : (if (int_of_nat i' =? int_of_nat j')%uint63
            then ~~ (L.array_bigZ_dot (aget fddir i) (aget fdinv j) =? 0)
            else (L.array_bigZ_dot (aget fddir i) (aget fdinv j) =? 0))%bigZ := hinv i' j'.
  rewrite eqb_natE hi' hj' -!hnz in h; move: h.
  case hij: (i == j :> nat).
  - move/eqP => hne; left; split; last exact: hne.
    by apply/val_inj/eqP.
  - move/eqP => h0; right; split; last exact: h0.
    by move=> heq; rewrite heq eqxx in hij.
Qed.

(* -------------------------------------------------------------------------- *)
(* [flagIndicesAreInActiveSets]: flag positions are active at their vertex    *)
(* -------------------------------------------------------------------------- *)

Lemma flagIndicesAreInActiveSets_correct (hm : (0 < m)%N) :
  L.areInequalitiesWellFormed c -> L.arePointsWellFormed c -> L.areActiveSetsWellFormed c ->
  L.areActiveSetsUnique c -> L.feasibility_check c -> L.areFlagsWellFormed c ->
  (forall v : 'I_nv, (0 < alen (L.activeSet (vertex_of v)))%N) ->
  @H.flagIndicesAreInActiveSets d R (interp_cert hm).
Proof.
move=> hineq hpts hact hasu hfeas hfw hact0.
rewrite /H.flagIndicesAreInActiveSets /interp_cert /H.flag_indices /H.activeSets /H.points.
move=> x /in_points_of [v0 hv0] i; rewrite -hv0.
rewrite (activeSets_of_vertex hm hineq hpts hact hasu hfeas v0) /flag_indices_of.
case: pickP => [v /eqP hv|/(_ v0)]; last by rewrite eqxx.
have hvv : v = v0 by apply: (point_of_vertex_inj hm hineq hpts hact hasu hfeas).
subst v.
have hp := flag_ineq_range (v := v0) i hfw (hact0 v0).
have hm' : (nat_of_int (aget (L.activeSet (vertex_of v0)) (Ordinal hp)) < m)%N.
  by apply: activeSet_range.
have hE : nat_of_int (aget (L.activeSet (vertex_of v0)) (Ordinal hp))
          = nat_of_int (PArray.get (L.activeSet (vertex_of v0))
              (PArray.get (fst (L.flag (vertex_of v0))) (int_of_nat i))).
  by rewrite /aget nat_of_intK.
apply/in_set_of_array; exists (Ordinal hp).
by rewrite val_insubd -hE hm'.
Qed.

(* -------------------------------------------------------------------------- *)
(* [flagVerticesArePoints]: flag witnesses are certified points               *)
(* -------------------------------------------------------------------------- *)

Lemma flagVerticesArePoints_correct (hm : (0 < m)%N) (hnv : (0 < nv)%N) :
  L.areFlagsWellFormed c ->
  @H.flagVerticesArePoints d R (interp_cert hm).
Proof.
move=> hfw.
rewrite /H.flagVerticesArePoints /interp_cert /H.flag_vertices /H.points.
move=> x hx i; move: hx => /in_points_of [v0 hv0]; rewrite -hv0.
rewrite /flag_vertices_of.
case: pickP => [v _|/(_ v0)]; last by rewrite eqxx.
rewrite (point_at_ord (flag_wit_range hnv v i hfw)).
by apply/in_points_of; eexists.
Qed.

(* -------------------------------------------------------------------------- *)
(* T6: the flag criterion                                                     *)
(* -------------------------------------------------------------------------- *)

(* Per vertex and flag position [k], the witness's active set misses the
   [k]-th flag inequality and contains all the earlier ones. *)
Lemma flag_check_correct (hm : (0 < m)%N) (hnv : (0 < nv)%N) :
  L.areInequalitiesWellFormed c -> L.arePointsWellFormed c -> L.areActiveSetsWellFormed c ->
  L.areActiveSetsUnique c -> L.feasibility_check c -> L.areFlagsWellFormed c ->
  (forall v : 'I_nv, (0 < alen (L.activeSet (vertex_of v)))%N) ->
  L.flag_check c ->
  @H.flag_check d R (interp_cert hm).
Proof.
move=> hineq hpts hact hasu hfeas hfw hact0 hchk.
have hAS := activeSets_of_vertex hm hineq hpts hact hasu hfeas.
rewrite /H.flag_check /interp_cert /H.flag_indices /H.flag_vertices /H.activeSets /H.points.
move=> x /in_points_of [v0 hv0] k; rewrite -hv0.
rewrite /flag_indices_of /flag_vertices_of.
case: pickP => [v /eqP hv|/(_ v0)]; last by rewrite eqxx.
have hvv : v = v0 by apply: (point_of_vertex_inj hm hineq hpts hact hasu hfeas).
subst v.
(* the witness vertex at position [k], as an ordinal *)
have hwr := flag_wit_range hnv v0 k hfw.
rewrite (point_at_ord hwr) hAS.
set word := Ordinal hwr.
(* the certified flag row at [v0] *)
move: hchk; rewrite /L.flag_check; cbv zeta => /bfor_all_balenP/(_ v0); cbv beta zeta.
case E : (L.flag (baget (L.vertices c) v0)) => [ineq wit] hrow.
have hE : L.flag (vertex_of v0) = (ineq, wit) := E.
have hl1 : alen ineq = d.
  by have [h _ _ _] := flagsP v0 hfw; move: h; rewrite hE => h; exact: h.
have hl2 : alen wit = d.
  by have [_ h _ _] := flagsP v0 hfw; move: h; rewrite hE => h; exact: h.
(* the flag row cell at position [k] *)
move: hrow => /(for_alliP _ hl2)/(_ k); cbv beta => /andP[hc1 hc2].
(* the witness read, on both spellings *)
have hwE : PArray.get (snd (L.flag (vertex_of v0))) (int_of_nat k)
           = PArray.get wit (int_of_nat k).
  by rewrite hE.
have hvwE : vertex_of word
            = BigArray.get (L.vertices c) (PArray.get wit (int_of_nat k)).
  by rewrite /vertex_of /baget
     -[nat_of_ord word]/(nat_of_int (PArray.get (snd (L.flag (vertex_of v0)))
                           (int_of_nat k))) hwE nat_of_intK.
(* the flag inequality at [k]: in range, hence a genuine active entry < m *)
have hpk := flag_ineq_range (v := v0) k hfw (hact0 v0).
have hgetE : nat_of_int (aget (L.activeSet (vertex_of v0)) (Ordinal hpk))
             = nat_of_int (PArray.get (L.activeSet (vertex_of v0))
                 (PArray.get ineq (int_of_nat k))).
  by rewrite /aget nat_of_intK hE.
have hmk : (nat_of_int (PArray.get (L.activeSet (vertex_of v0))
              (PArray.get ineq (int_of_nat k))) < m)%N.
  by rewrite -hgetE; apply: activeSet_range.
split.
- (* the [k]-th flag inequality is NOT active at the witness *)
  apply/negP => hin.
  move/negP: hc2; apply.
  rewrite -hvwE.
  move: hin => /in_set_of_array[q hq].
  apply: (mem_sorted_complete (activeSet_sorted word hact) (p := q)).
  + exact: ltn_ord.
  + by rewrite hq val_insubd hmk.
- (* the earlier flag inequalities ARE active at the witness *)
  move=> j hjk.
  have hkk : nat_of_int (int_of_nat k) = k.
    exact: (int_of_natK_le (i := L.dimension c) (ltnW (ltn_ord k))).
  move: hc1 => /for_all_range0P h.
  have := h (cast_ord (esym hkk) (Ordinal hjk)); cbv beta => hnm.
  (* the [j]-th flag inequality, in range and < m *)
  have hpj := flag_ineq_range (v := v0) j hfw (hact0 v0).
  have hgetEj : nat_of_int (aget (L.activeSet (vertex_of v0)) (Ordinal hpj))
                = nat_of_int (PArray.get (L.activeSet (vertex_of v0))
                    (PArray.get ineq (int_of_nat j))).
    by rewrite /aget nat_of_intK hE.
  have hmj : (nat_of_int (PArray.get (L.activeSet (vertex_of v0))
                (PArray.get ineq (int_of_nat j))) < m)%N.
    by rewrite -hgetEj; apply: activeSet_range.
  set X := insubd (Ordinal hm)
    (nat_of_int (PArray.get (L.activeSet (vertex_of v0))
       (PArray.get ineq (int_of_nat j)))).
  (* [X] is active at [v0] *)
  have hXv0 : X \in activeSet_of v0.
    apply/in_set_of_array; exists (Ordinal hpj).
    by rewrite hgetEj /X val_insubd hmj.
  (* [X] is not in the difference: the checker's membership test is negative *)
  have hsd := diff_sorted (activeSet_sorted v0 hact)
                          (activeSet_sorted word hact).
  have hnotD : X \notin activeSet_of v0 :\: activeSet_of word.
    rewrite -(diff_seq_setE hm v0 word hact X).
    rewrite /X val_insubd hmj.
    by move: hnm; rewrite -hvwE mem_intlistE //.
  by move: hnotD; rewrite in_setD hXv0 andbT => /negbNE.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assembly: the VtxEquality checker                                          *)
(* -------------------------------------------------------------------------- *)

(* The two flag well-formedness conditions and the flag criterion follow from
   the vertex-containment and vertex-equality checker bundles; the checker
   does not enforce the nonemptiness of the active sets, which is taken as a
   hypothesis. *)
Theorem vtx_equality_correct (hm : (0 < m)%N) (hnv : (0 < nv)%N) :
  L.VtxContainment.check_certificate c -> L.VtxEquality.check_certificate c ->
  (forall v : 'I_nv, (0 < alen (L.activeSet (vertex_of v)))%N) ->
  [/\ @H.flagIndicesAreInActiveSets d R (interp_cert hm),
      @H.flagVerticesArePoints d R (interp_cert hm) &
      @H.flag_check d R (interp_cert hm)].
Proof.
move=> /certP[/wfP hwf hfeas _ _ _] /veqP[hfw hchk] hact0.
split.
- have h := flagIndicesAreInActiveSets_correct (hm := hm) (wf_ineq hwf) (wf_pts hwf)
              (wf_act hwf) (wf_asu hwf) hfeas hfw hact0.
  exact: h.
- have h := flagVerticesArePoints_correct (hm := hm) hnv hfw.
  exact: h.
- have h := flag_check_correct (hm := hm) hnv (wf_ineq hwf) (wf_pts hwf) (wf_act hwf)
              (wf_asu hwf) hfeas hfw hact0 hchk.
  exact: h.
Qed.

(* -------------------------------------------------------------------------- *)
(* The geometric graph: high-level conditions (GraphEquality checker)         *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* [geomGraphVerticesArePoints]: the vertices are the certified points        *)
(* -------------------------------------------------------------------------- *)

Lemma geomGraphVerticesArePoints_correct (hm : (0 < m)%N) :
  @H.geomGraphVerticesArePoints d R (interp_cert hm).
Proof.
by rewrite /H.geomGraphVerticesArePoints /interp_cert /H.geom_graph vtx_geom_graph_of.
Qed.

(* -------------------------------------------------------------------------- *)
(* [geomGraphIsImageOfGraph], with the corrective premise [v <> w]            *)
(* -------------------------------------------------------------------------- *)

(* As stated upstream the iff is false whenever a facet edge collapses under
   [mapping] -- with [v = w] the common image point, the RHS holds but a simple
   graph has no loop.  Once the premise is added upstream, drop this and use
   [H.geomGraphIsImageOfGraph] directly. *)
Definition geomGraphIsImageOfGraph_ne (hm : (0 < m)%N) : Prop :=
    forall v w : 'cV[R]_d,
    v \in vertices (@H.geom_graph R d (interp_cert hm)) ->
    w \in vertices (@H.geom_graph R d (interp_cert hm)) ->
    v <> w ->
    (w \in successors (@H.geom_graph R d (interp_cert hm)) v <->
     exists fv fw : {set 'I_m},
       fv \in vertices (@H.graph R d (interp_cert hm))
       /\ fw \in successors (@H.graph R d (interp_cert hm)) fv
       /\ @H.mapping R d (interp_cert hm) fv = v
       /\ @H.mapping R d (interp_cert hm) fw = w).

Lemma geomGraphIsImageOfGraph_correct (hm : (0 < m)%N) (hnv : (0 < nv)%N)
    (hnf : (0 < nf)%N) (hd : (0 < d)%N) :
  L.isGraphWellFormed c -> L.areDescriptionsWellFormed c -> L.isMappingWellFormed c ->
  L.areFacetsUnique c ->
  L.bfor_all (L.hasLength (L.dimension c)) (L.graph c) ->
  L.isGeomGraphWellFormed c -> L.areGeomEdgeSourcesWellFormed c ->
  L.areGeomEdgeLocalTargetsWellFormed c -> L.graph_image_check c ->
  geomGraphIsImageOfGraph_ne hm.
Proof.
move=> hgf hdesc hmapwf hfu hreg hg hsrc htgt himg.
have hdinj := desc_of_inj hm hdesc hfu.
have hGE : @H.geom_graph R d (interp_cert hm) = geom_graph_of by [].
have hGR : @H.graph R d (interp_cert hm) = graph_of by [].
have hMA : @H.mapping R d (interp_cert hm) = mapping_of by [].
move: himg; rewrite /L.graph_image_check; cbv zeta => /andP[himg1 himg2].
move=> v w; rewrite hGE hGR hMA vtx_geom_graph_of vtx_graph_of => hv hw hvw; split.
- (* a geometric edge is the image of the facet edge its tables name *)
  rewrite in_succ_geom // => /and3P[_ _ /existsP[v1 /existsP[w1 /and3P[/eqP hp1 /eqP hpw hnb]]]].
  move: hnb => /in_set_of_array[j hj].
  pose SRC := PArray.get (baget (L.geom_edge_sources c) v1) (int_of_nat j).
  pose TJI := PArray.get (baget (L.geom_edge_local_targets c) v1) (int_of_nat j).
  have hjs : (j < alen (baget (L.geom_edge_sources c) v1))%N.
    by rewrite (geom_src_row_len hsrc); exact: ltn_ord.
  have hjt : (j < alen (baget (L.geom_edge_local_targets c) v1))%N.
    by rewrite (geom_tgt_row_len htgt); exact: ltn_ord.
  have hsF : (nat_of_int SRC < nf)%N := geom_src_range hnf hsrc (Ordinal hjs).
  have hrowE : baget (L.graph c) (Ordinal hsF) = BigArray.get (L.graph c) SRC.
    by rewrite /baget nat_of_intK.
  have h0 : (0 < alen (BigArray.get (L.graph c) SRC))%N.
    by rewrite -hrowE (row_len hgf _ hreg); exact: hd.
  have htF0 : (nat_of_int TJI < alen (BigArray.get (L.graph c) SRC))%N
    := geom_tgt_range (j := Ordinal hjt) htgt h0.
  have htji : (nat_of_int TJI < alen (baget (L.graph c) (Ordinal hsF)))%N.
    by rewrite hrowE; exact: htF0.
  have htE : aget (baget (L.graph c) (Ordinal hsF)) (Ordinal htji)
             = PArray.get (BigArray.get (L.graph c) SRC) TJI.
    exact: eq_trans
      (congr1 (fun a : array int => PArray.get a (int_of_nat (nat_of_int TJI))) hrowE)
      (congr1 (PArray.get (BigArray.get (L.graph c) SRC)) (nat_of_intK TJI)).
  have htF : (nat_of_int (PArray.get (BigArray.get (L.graph c) SRC) TJI) < nf)%N.
    by rewrite -htE; exact: (nbrs_ord hgf (Ordinal htji)).
  have hnbr : Ordinal htF \in nbrs (Ordinal hsF).
    by apply/in_set_of_array; exists (Ordinal htji); rewrite htE.
  move: himg2 => /bfor_alli_matrix_balenP hcell.
  have hij := hcell (cast_ord (esym (geom_graph_len hg)) v1) j.
  have hcE : (int_of_nat v1 =? L.mapping (BigArray.get (L.facets c) SRC))%uint63
             && (aget (baget (L.geom_graph c) v1) j
                 =? L.mapping (BigArray.get (L.facets c)
                      (PArray.get (BigArray.get (L.graph c) SRC) TJI)))%uint63 := hij.
  case/andP: hcE => hc1 hc2.
  move: hc1; rewrite eqb_natE (int_of_natK_le (ltnW (ltn_ord v1))) => /eqP hc1.
  move: hc2; rewrite eqb_natE hj => /eqP hc2.
  have hbv : (nat_of_int (L.mapping (BigArray.get (L.facets c) SRC)) < nv)%N.
    by rewrite -hc1; exact: ltn_ord.
  have hbw : (nat_of_int (L.mapping (BigArray.get (L.facets c)
                (PArray.get (BigArray.get (L.graph c) SRC) TJI))) < nv)%N.
    by rewrite -hc2; exact: ltn_ord.
  exists (desc_of (Ordinal hsF)), (desc_of (Ordinal htF)); split; [|split; [|split]].
  + by apply/imfsetP; exists (Ordinal hsF).
  + rewrite in_succ_of; apply/and3P; split.
    * apply/eqP => he.
      have hwk : Ordinal htF = Ordinal hsF by apply: hdinj.
      by move: (nbrs_irrefl hgf (Ordinal hsF)); rewrite -{1}hwk hnbr.
    * by apply/imfsetP; exists (Ordinal htF).
    * apply/existsP; exists (Ordinal hsF); apply/existsP; exists (Ordinal htF).
      by rewrite !eqxx hnbr.
  + rewrite (mapping_of_desc hm _ hdesc hfu) (facet_of_ord hsF) (point_at_ord hbv) -hp1.
    by congr point_of_vertex; apply: val_inj; rewrite /= -hc1.
  + rewrite (mapping_of_desc hm _ hdesc hfu) (facet_of_ord htF) (point_at_ord hbw) -hpw.
    by congr point_of_vertex; apply: val_inj; rewrite /= -hc2.
- (* a facet edge maps onto a geometric edge (or collapses, excluded by v <> w) *)
  case=> fv [fw [hfv [hfw [hmv hmw]]]].
  case/imfsetP: hfv hfw hmv => [k _ ->] hfw hmv.
  move: hfw; rewrite in_succ_of
    => /and3P[_ _ /existsP[k' /existsP[w' /and3P[/eqP hdk' /eqP hdw' hnb]]]].
  have hkk : k' = k by apply: hdinj.
  rewrite hkk in hnb; rewrite -hdw' in hmw.
  have hb1 := mapping_ord hnv k hmapwf.
  have hb2 := mapping_ord hnv w' hmapwf.
  move: hmv; rewrite (mapping_of_desc hm _ hdesc hfu) (point_at_ord hb1) => hpv.
  move: hmw; rewrite (mapping_of_desc hm _ hdesc hfu) (point_at_ord hb2) => hpw'.
  move: hnb => /in_set_of_array[p hp].
  move: himg1 => /bfor_alli_matrix_balenP hcell.
  have hij := hcell (cast_ord (esym (graph_len hgf)) k) p.
  have hcE : (L.mapping (facet_of k)
              =? L.mapping (BigArray.get (L.facets c) (aget (baget (L.graph c) k) p)))%uint63
             || L.mem_sorted Uint63.ltb
                  (BigArray.get (L.geom_graph c) (L.mapping (facet_of k)))
                  (L.mapping (BigArray.get (L.facets c) (aget (baget (L.graph c) k) p))) := hij.
  have hfwE : BigArray.get (L.facets c) (aget (baget (L.graph c) k) p) = facet_of w'.
    by rewrite /facet_of /baget -hp nat_of_intK.
  rewrite hfwE in hcE.
  case/orP: hcE => [heq|hmem].
    move: heq; rewrite eqb_natE => /eqP heq.
    exfalso; apply: hvw; rewrite -hpv -hpw'; congr point_of_vertex.
    by apply: val_inj; rewrite /= heq.
  have [q [hq hqv]] := mem_sorted_sound hmem.
  have hrowg : baget (L.geom_graph c) (Ordinal hb1)
               = BigArray.get (L.geom_graph c) (L.mapping (facet_of k)).
    by rewrite /baget nat_of_intK.
  rewrite -hrowg in hq.
  rewrite in_succ_geom //; apply/and3P; split.
  + by apply/eqP => he; apply: hvw; rewrite he.
  + exact: hw.
  + apply/existsP; exists (Ordinal hb1); apply/existsP; exists (Ordinal hb2).
    apply/and3P; split; [by rewrite hpv|by rewrite hpw'|].
    apply/in_set_of_array; exists (Ordinal hq).
    have hqE := congr1 (fun a : array int => nat_of_int (PArray.get a (int_of_nat q))) hrowg.
    exact: eq_trans hqE hqv.
Qed.

(* -------------------------------------------------------------------------- *)
(* Support for T7: the diff list along a neighbour row                        *)
(* -------------------------------------------------------------------------- *)

(* The active-set differences the checker builds along [v]'s neighbour row,
   in the reversed order its [fold] produces them. *)
#[local] Definition geom_diffs (v : 'I_nv) : seq (seq int) :=
  rev [seq L.diff Uint63.ltb (L.activeSet (vertex_of v))
             (L.activeSet (BigArray.get (L.vertices c)
                (PArray.get (baget (L.geom_graph c) v) (int_of_nat j))))
      | j <- iota 0 (alen (baget (L.geom_graph c) v))].

Lemma geom_diffs_size (v : 'I_nv) : size (geom_diffs v) = alen (baget (L.geom_graph c) v).
Proof. by rewrite /geom_diffs size_rev size_map size_iota. Qed.

Lemma geom_diffs_nth (v : 'I_nv) (j : 'I_(alen (baget (L.geom_graph c) v))) :
  nth [::] (geom_diffs v) (alen (baget (L.geom_graph c) v) - j.+1)
  = L.diff Uint63.ltb (L.activeSet (vertex_of v))
      (L.activeSet (BigArray.get (L.vertices c)
         (PArray.get (baget (L.geom_graph c) v) (int_of_nat j)))).
Proof. exact: (@nth_rev_map_iota _ _ [::] _ _ (ltn_ord j)). Qed.

Lemma geom_diffs_index (v : 'I_nv) (j : 'I_(alen (baget (L.geom_graph c) v))) :
  (alen (baget (L.geom_graph c) v) - j.+1 < size (geom_diffs v))%N.
Proof.
by rewrite geom_diffs_size ltn_subrL /=; exact: leq_ltn_trans (leq0n _) (ltn_ord j).
Qed.

(* The per-vertex content of [geom_edge_difference_pairwise_check]. *)
Lemma geom_check_at (hchk : L.geom_edge_difference_pairwise_check c) :
  forall v : 'I_nv, L.pairwise_incomparable (geom_diffs v).
Proof.
move=> v; move: hchk; rewrite /L.geom_edge_difference_pairwise_check; cbv zeta.
move=> /bfor_alli_balenP/(_ v); cbv beta zeta.
by rewrite fold_consE => h; exact: h.
Qed.

(* -------------------------------------------------------------------------- *)
(* T7: active-set difference incomparability                                  *)
(* -------------------------------------------------------------------------- *)

(* Distinct neighbours cut incomparable slices out of the active set. *)
Lemma geom_edge_difference_pairwise_correct (hm : (0 < m)%N) :
  L.areInequalitiesWellFormed c -> L.arePointsWellFormed c -> L.areActiveSetsWellFormed c ->
  L.areActiveSetsUnique c -> L.feasibility_check c ->
  L.geom_edge_difference_pairwise_check c ->
  @H.geom_edge_difference_pairwise_check d R (interp_cert hm).
Proof.
move=> hineq hpts hact hasu hfeas hchk.
have hAS := activeSets_of_vertex hm hineq hpts hact hasu hfeas.
have hinj := point_of_vertex_inj hm hineq hpts hact hasu hfeas.
rewrite /H.geom_edge_difference_pairwise_check /interp_cert /H.geom_graph /H.activeSets
  vtx_geom_graph_of.
move=> x hx w w' [hw hw'] hne.
move: hw; rewrite in_succ_geom //.
move=> /and3P[_ _ /existsP[v1 /existsP[w1 /and3P[/eqP hp1 /eqP hpw1 hnb1]]]].
move: hw'; rewrite in_succ_geom //.
move=> /and3P[_ _ /existsP[v2 /existsP[w2 /and3P[/eqP hp2 /eqP hpw2 hnb2]]]].
have hv12 : v2 = v1 by apply: hinj; rewrite hp2 hp1.
rewrite hv12 in hnb2.
move: hnb1 => /in_set_of_array[j1 hj1]; move: hnb2 => /in_set_of_array[j2 hj2].
have hw12 : nat_of_ord w1 <> nat_of_ord w2.
  by move=> he; apply: hne; rewrite -hpw1 -hpw2; congr point_of_vertex; apply/val_inj.
have hj12 : j1 <> j2.
  by move=> he; apply: hw12; rewrite -hj1 -hj2 he.
(* the checker's pairwise incomparability, at two distinct row positions *)
have hpair : forall jA jB : 'I_(alen (baget (L.geom_graph c) v1)), (jA < jB)%N ->
    L.incomparable
      (L.diff Uint63.ltb (L.activeSet (vertex_of v1))
        (L.activeSet (BigArray.get (L.vertices c)
           (PArray.get (baget (L.geom_graph c) v1) (int_of_nat jB)))))
      (L.diff Uint63.ltb (L.activeSet (vertex_of v1))
        (L.activeSet (BigArray.get (L.vertices c)
           (PArray.get (baget (L.geom_graph c) v1) (int_of_nat jA))))).
  move=> jA jB hAB.
  have hpw := geom_check_at hchk v1.
  have hk12 : (alen (baget (L.geom_graph c) v1) - jB.+1
               < alen (baget (L.geom_graph c) v1) - jA.+1)%N.
    by apply: ltn_sub2l; [exact: leq_ltn_trans hAB (ltn_ord jB) | exact: hAB].
  have := pairwise_incomparable_nth hpw hk12 (geom_diffs_index jA).
  by rewrite !geom_diffs_nth.
(* row entries carry w1 and w2 *)
have hvw1 : BigArray.get (L.vertices c)
              (PArray.get (baget (L.geom_graph c) v1) (int_of_nat j1)) = vertex_of w1.
  by rewrite /vertex_of /baget -hj1 nat_of_intK.
have hvw2 : BigArray.get (L.vertices c)
              (PArray.get (baget (L.geom_graph c) v1) (int_of_nat j2)) = vertex_of w2.
  by rewrite /vertex_of /baget -hj2 nat_of_intK.
have hinc : L.incomparable
    (L.diff Uint63.ltb (L.activeSet (vertex_of v1)) (L.activeSet (vertex_of w1)))
    (L.diff Uint63.ltb (L.activeSet (vertex_of v1)) (L.activeSet (vertex_of w2))).
  case hlt: (j1 < j2)%N.
    have h := hpair j1 j2 hlt; rewrite hvw1 hvw2 in h.
    by move: h => /andP[h21 h12]; apply/andP; split; [exact: h12 | exact: h21].
  have hlt2 : (j2 < j1)%N.
    rewrite ltn_neqAle; apply/andP; split.
      by apply/eqP => he; apply: hj12; apply/val_inj; exact: esym he.
    by rewrite leqNgt hlt.
  by have h := hpair j2 j1 hlt2; rewrite hvw1 hvw2 in h.
have hsorted1 := diff_sorted (activeSet_sorted v1 hact) (activeSet_sorted w1 hact).
have hsorted2 := diff_sorted (activeSet_sorted v1 hact) (activeSet_sorted w2 hact).
have [[y1 [hy1 hy1']] [y2 [hy2 hy2']]] := incomparable_sound hsorted1 hsorted2 hinc.
rewrite -hp1 -hpw1 -hpw2 !hAS /H.incomparable.
have hy1m : (y1 < m)%N := diff_lt_m hm hact hy1.
have hy2m : (y2 < m)%N := diff_lt_m hm hact hy2.
apply/andP; split; apply/subsetPn.
  exists (Ordinal hy1m).
    by rewrite -(diff_seq_setE hm v1 w1 hact (Ordinal hy1m)); exact: hy1.
  apply/negP; rewrite -(diff_seq_setE hm v1 w2 hact (Ordinal hy1m)) => hin2.
  by rewrite hin2 in hy1'.
exists (Ordinal hy2m).
  by rewrite -(diff_seq_setE hm v1 w2 hact (Ordinal hy2m)); exact: hy2.
apply/negP; rewrite -(diff_seq_setE hm v1 w1 hact (Ordinal hy2m)) => hin1.
by rewrite hin1 in hy2'.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assembly: the GraphEquality checker                                        *)
(* -------------------------------------------------------------------------- *)

(* The three geometric-graph conditions follow from the two checker bundles;
   the image condition comes in its corrected form
   ([geomGraphIsImageOfGraph_ne]). *)
Theorem graph_equality_correct (hm : (0 < m)%N) (hnv : (0 < nv)%N) (hnf : (0 < nf)%N)
    (hd : (0 < d)%N) :
  L.VtxContainment.check_certificate c -> L.GraphEquality.check_certificate c ->
  [/\ @H.geomGraphVerticesArePoints d R (interp_cert hm),
      geomGraphIsImageOfGraph_ne hm &
      @H.geom_edge_difference_pairwise_check d R (interp_cert hm)].
Proof.
move=> /certP[/wfP hwf hfeas _ hgraph _] /geqP[[hg hsrc htgt] [himg hpair]].
move: hgraph; rewrite /L.graph_check; cbv zeta => /andP[hreg _].
split.
- exact: (geomGraphVerticesArePoints_correct hm).
- have h := geomGraphIsImageOfGraph_correct (hm := hm) hnv hnf hd (wf_graph hwf) (wf_desc hwf)
              (wf_map hwf) (wf_fu hwf) hreg hg hsrc htgt himg.
  exact: h.
- have h := geom_edge_difference_pairwise_correct (hm := hm) (wf_ineq hwf) (wf_pts hwf)
              (wf_act hwf) (wf_asu hwf) hfeas hpair.
  exact: h.
Qed.

(* -------------------------------------------------------------------------- *)
(* The distance certificate: interpretation and index well-formedness         *)
(* -------------------------------------------------------------------------- *)

Section Distance.

Variable (dc : L.DistanceCertificate).

(* Its source as a point, and the label of a point, read through the vertex
   index carrying it. *)
Definition source_of : 'cV[R]_d :=
  point_of R d (L.point (BigArray.get (L.vertices c) (L.dist_source dc))).
Definition label_of (v : 'I_nv) : nat := nat_of_int (baget (L.distances dc) v).
Definition distance_of (x : 'cV[R]_d) : nat :=
  \max_(v : 'I_nv | point_of_vertex v == x) label_of v.

Definition interp_dist : H.DistanceCertificate R d :=
  @H.Build_DistanceCertificate R d source_of distance_of.

Lemma distP : L.Diameter.check_certificate c dc ->
  [/\ L.areDistancesWellFormed c dc, L.distance_source_check dc, L.distance_edge_check c dc
    & L.distance_parent_check c dc].
Proof. by rewrite /L.Diameter.check_certificate => /andP[/andP[/andP[h1 h2] h3] h4]. Qed.

Lemma dist_len : L.areDistancesWellFormed c dc -> balen (L.distances dc) = nv.
Proof.
rewrite /L.areDistancesWellFormed; cbv zeta => /andP[/andP[hl _] _].
by rewrite eqb_balenE in hl; move/eqP: hl.
Qed.

Lemma dist_source_ord (hnv : (0 < nv)%N) : L.areDistancesWellFormed c dc ->
  (nat_of_int (L.dist_source dc) < nv)%N.
Proof.
move=> hwf; have hl := dist_len hwf; move: hwf.
rewrite /L.areDistancesWellFormed; cbv zeta => /andP[/andP[_ hs] _].
have h0 : (0 < nat_of_int (BigArray.length (L.distances dc)))%N by rewrite balenE hl.
by have := inRangeP h0 hs; rewrite balenE hl.
Qed.

Lemma label_lt_nv : L.areDistancesWellFormed c dc -> forall v : 'I_nv, (label_of v < nv)%N.
Proof.
move=> hwf v; have hl := dist_len hwf; move: hwf.
rewrite /L.areDistancesWellFormed; cbv zeta => /andP[_ hb].
have hv : (v < balen (L.distances dc))%N by rewrite hl.
move: hb => /bfor_all_balenP/(_ (Ordinal hv)); cbv beta; rewrite ltb_natE balenE => h.
have h' : (nat_of_int (baget (L.distances dc) v) < balen (L.distances dc))%N := h.
by rewrite hl in h'.
Qed.

Lemma source_of_vertex (hnv : (0 < nv)%N) (hwf : L.areDistancesWellFormed c dc) :
  source_of = point_of_vertex (Ordinal (dist_source_ord hnv hwf)).
Proof. by rewrite /source_of /point_of_vertex /vertex_of /= baget_natE. Qed.

(* The label of a certified point is the label of its (unique) vertex index. *)
Lemma distance_of_vertex (hm : (0 < m)%N) :
  L.areInequalitiesWellFormed c -> L.arePointsWellFormed c -> L.areActiveSetsWellFormed c ->
  L.areActiveSetsUnique c -> L.feasibility_check c ->
  forall v : 'I_nv, distance_of (point_of_vertex v) = label_of v.
Proof.
move=> hineq hpts hact hasu hfeas v; rewrite /distance_of.
rewrite (eq_bigl (pred1 v)) ?big_pred1_eq // => v' /=.
apply/idP/idP => [/eqP he|/eqP ->]; last exact: eqxx.
by apply/eqP; apply: (point_of_vertex_inj hm hineq hpts hact hasu hfeas); exact: he.
Qed.

(* The largest label, as computed by the checker's running maximum. *)
Lemma max_distance_ge (hwf : L.areDistancesWellFormed c dc) (v : 'I_nv) :
  (label_of v <= nat_of_int (L.max_distance dc))%N.
Proof.
have hv : (v < balen (L.distances dc))%N by rewrite dist_len.
by have := bfold_int_max_ge (Ordinal hv).
Qed.

Lemma max_distance_in (hnv : (0 < nv)%N) (hwf : L.areDistancesWellFormed c dc) :
  L.distance_source_check dc ->
  exists v : 'I_nv, label_of v = nat_of_int (L.max_distance dc).
Proof.
move=> hsrc; rewrite /L.max_distance.
have [h0|[v hv]] := bfold_int_max_in (L.distances dc).
  exists (Ordinal (dist_source_ord hnv hwf)); rewrite /label_of /= baget_natE h0.
  by move: hsrc; rewrite /L.distance_source_check eqb_natE nat_of_int0 => /eqP.
have hv' : (v < nv)%N by rewrite -(dist_len hwf).
by exists (Ordinal hv').
Qed.

(* -------------------------------------------------------------------------- *)
(* D1: the source                                                             *)
(* -------------------------------------------------------------------------- *)

Lemma distance_source_correct (hm : (0 < m)%N) (hnv : (0 < nv)%N) :
  L.areInequalitiesWellFormed c -> L.arePointsWellFormed c -> L.areActiveSetsWellFormed c ->
  L.areActiveSetsUnique c -> L.feasibility_check c ->
  L.areDistancesWellFormed c dc -> L.distance_source_check dc ->
  @H.distance_source_check d R (interp_cert hm) interp_dist.
Proof.
move=> hineq hpts hact hasu hfeas hwf hsrc.
rewrite /H.distance_source_check /source_labelled /interp_cert /interp_dist /H.geom_graph /H.source
  /H.distance vtx_geom_graph_of (source_of_vertex hnv hwf); split.
  by apply/in_points_of; eexists; reflexivity.
rewrite (distance_of_vertex hm hineq hpts hact hasu hfeas) /label_of /= baget_natE.
by move: hsrc; rewrite /L.distance_source_check eqb_natE nat_of_int0 => /eqP.
Qed.

(* -------------------------------------------------------------------------- *)
(* D2: labels grow by at most one along the edges                             *)
(* -------------------------------------------------------------------------- *)

Lemma distance_edge_correct (hm : (0 < m)%N) :
  L.areInequalitiesWellFormed c -> L.arePointsWellFormed c -> L.areActiveSetsWellFormed c ->
  L.areActiveSetsUnique c -> L.feasibility_check c ->
  L.isGeomGraphWellFormed c -> L.areDistancesWellFormed c dc -> L.distance_edge_check c dc ->
  @H.distance_edge_check d R (interp_cert hm) interp_dist.
Proof.
move=> hineq hpts hact hasu hfeas hg hwf hchk.
rewrite /H.distance_edge_check /edges_labelled /interp_cert /interp_dist /H.geom_graph /H.distance.
move=> x y hxy.
have hx : x \in points_of by have := edge_vtxl hxy; rewrite vtx_geom_graph_of.
have hy : y \in points_of by have := edge_vtxr hxy; rewrite vtx_geom_graph_of.
move: hxy; rewrite /geom_graph_of edge_mk_graph //.
move=> /andP[_ /existsP[v1 /existsP[w1 /and3P[/eqP hp1 /eqP hpw hnb]]]].
rewrite -hp1 -hpw !(distance_of_vertex hm hineq hpts hact hasu hfeas).
move: hnb => /in_set_of_array[j hj].
have hb : (v1 < balen (L.geom_graph c))%N by rewrite geom_graph_len.
move: hchk; rewrite /L.distance_edge_check; cbv zeta.
move=> /bfor_alli_balenP/(_ (Ordinal hb)); cbv beta => /for_all_alenP/(_ j); cbv beta.
rewrite leb_natE bagetE -baget_natE hj.
rewrite (add1_balenE (t := L.distances dc)); first by [].
by rewrite dist_len //; exact: label_lt_nv.
Qed.
Arguments distance_edge_correct : clear implicits.

(* -------------------------------------------------------------------------- *)
(* D3: every other vertex has a neighbour labelled one less                   *)
(* -------------------------------------------------------------------------- *)

Lemma distance_parent_correct (hm : (0 < m)%N) (hnv : (0 < nv)%N) :
  L.areInequalitiesWellFormed c -> L.arePointsWellFormed c -> L.areActiveSetsWellFormed c ->
  L.areActiveSetsUnique c -> L.feasibility_check c ->
  L.isGeomGraphWellFormed c -> L.areDistancesWellFormed c dc -> L.distance_parent_check c dc ->
  @H.distance_parent_check d R (interp_cert hm) interp_dist.
Proof.
move=> hineq hpts hact hasu hfeas hg hwf hchk.
have hinj := point_of_vertex_inj hm hineq hpts hact hasu hfeas.
rewrite /H.distance_parent_check /parents_labelled /interp_cert /interp_dist /H.geom_graph /H.source
  /H.distance vtx_geom_graph_of (source_of_vertex hnv hwf).
move=> y /in_points_of[v1 <-] hne.
have hv1s : v1 <> Ordinal (dist_source_ord hnv hwf) by move=> he; apply: hne; rewrite he.
have hb : (v1 < balen (L.geom_graph c))%N by rewrite geom_graph_len.
move: hchk; rewrite /L.distance_parent_check; cbv zeta.
move=> /bfor_alli_balenP/(_ (Ordinal hb)); cbv beta.
have -> : (int_of_nat (Ordinal hb) =? L.dist_source dc)%uint63 = false.
  apply/negbTE; rewrite eqb_natE; apply/eqP => he; apply: hv1s; apply/val_inj => /=.
  by rewrite -he (int_of_natK_le (i := blength (L.vertices c)) (ltnW (ltn_ord v1))).
rewrite orFb => /exist_alenP[j]; cbv beta.
have hw : (nat_of_int (aget (baget (L.geom_graph c) v1) j) < nv)%N := geom_nbrs_ord hg j.
rewrite eqb_natE bagetE -baget_natE (add1_balenE (t := L.distances dc)); last first.
  by rewrite dist_len //; have := label_lt_nv hwf (Ordinal hw).
move=> /eqP hlab.
exists (point_of_vertex (Ordinal hw)).
have hw1 : Ordinal hw \in geom_nbrs v1 by apply/in_set_of_array; exists j.
have hne1 : point_of_vertex (Ordinal hw) != point_of_vertex v1.
  apply/eqP => /hinj he.
  have hval : nat_of_int (aget (baget (L.geom_graph c) v1) j) = v1 := congr1 (@nat_of_ord nv) he.
  have hlab' : (nat_of_int (baget (L.distances dc) (nat_of_int (aget (baget (L.geom_graph c) v1) j)))).+1
               = nat_of_int (baget (L.distances dc) v1) := hlab.
  rewrite hval in hlab'.
  by have := n_Sn (nat_of_int (baget (L.distances dc) v1)); rewrite hlab'.
have hv1p : point_of_vertex v1 \in points_of by apply/in_points_of; exists v1.
have hwp : point_of_vertex (Ordinal hw) \in points_of by apply/in_points_of; eexists; reflexivity.
split.
  rewrite /geom_graph_of edge_mk_graph // hne1 /=.
  apply/existsP; exists v1; apply/existsP; exists (Ordinal hw).
  by rewrite !eqxx hw1.
by rewrite !(distance_of_vertex hm hineq hpts hact hasu hfeas).
Qed.
Arguments distance_parent_correct : clear implicits.

(* -------------------------------------------------------------------------- *)
(* Assembly: the Diameter checker                                             *)
(* -------------------------------------------------------------------------- *)

(* The value returned by the checker is the eccentricity of the source in
   the geometric graph. *)
Theorem diameter_correct (hm : (0 < m)%N) (hnv : (0 < nv)%N) (D : int) :
  L.VtxContainment.check_certificate c -> L.isGeomGraphWellFormed c ->
  L.Diameter.eccentricity c dc = Some D ->
  [/\ @H.distance_source_check d R (interp_cert hm) interp_dist,
      @H.distance_edge_check d R (interp_cert hm) interp_dist,
      @H.distance_parent_check d R (interp_cert hm) interp_dist
    & @H.eccentricity_check d R (interp_cert hm) interp_dist (nat_of_int D)].
Proof.
move=> /certP[/wfP hwf hfeas _ _ _] hg.
rewrite /L.Diameter.eccentricity; case E: (L.Diameter.check_certificate c dc) => // [] [<-].
have [hdw hsrc hedge hpar] := distP E.
split.
- exact: (distance_source_correct hm hnv (wf_ineq hwf) (wf_pts hwf) (wf_act hwf)
            (wf_asu hwf) hfeas hdw hsrc).
- exact: (distance_edge_correct hm (wf_ineq hwf) (wf_pts hwf) (wf_act hwf) (wf_asu hwf)
            hfeas hg hdw hedge).
- exact: (distance_parent_correct hm hnv (wf_ineq hwf) (wf_pts hwf) (wf_act hwf)
            (wf_asu hwf) hfeas hg hdw hpar).
- rewrite /H.eccentricity_check /interp_cert /interp_dist /H.geom_graph /H.distance vtx_geom_graph_of; split.
    move=> v /in_points_of[v1 <-].
    rewrite (distance_of_vertex hm (wf_ineq hwf) (wf_pts hwf) (wf_act hwf) (wf_asu hwf) hfeas).
    exact: max_distance_ge.
  have [v1 hv1] := max_distance_in hnv hdw hsrc.
  exists (point_of_vertex v1); split; first by apply/in_points_of; exists v1.
  by rewrite (distance_of_vertex hm (wf_ineq hwf) (wf_pts hwf) (wf_act hwf) (wf_asu hwf) hfeas).
Qed.

Corollary eccentricity_correct (hm : (0 < m)%N) (hnv : (0 < nv)%N) (D : int) :
  L.VtxContainment.check_certificate c -> L.isGeomGraphWellFormed c ->
  L.Diameter.eccentricity c dc = Some D ->
  eccentricity_is geom_graph_of source_of (nat_of_int D).
Proof.
move=> hvc hg hecc; have [h1 h2 h3 h4] := diameter_correct hm hnv hvc hg hecc.
have h := @H.eccentricity_cert d R (interp_cert hm) interp_dist (nat_of_int D)
            (geom_edges_sym hg) h1 h2 h3 h4.
exact: h.
Qed.

End Distance.

(* -------------------------------------------------------------------------- *)
(* Assembling the vertex-containment checker                                  *)
(* -------------------------------------------------------------------------- *)

(* The positivity hypotheses [0 < m], [0 < nv], [0 < nf], [0 < d] are the only
   premises the checker does not provide: its range checks [inRange 0 (n - 1)]
   are vacuous when n = 0, [0 < m] inhabits 'I_m for the special simplex, and
   [0 < d] makes [const_mx 1] nonzero. *)

Theorem vtx_containment_correct (hm : (0 < m)%N) (hnv : (0 < nv)%N) (hnf : (0 < nf)%N) :
  L.VtxContainment.check_certificate c ->
  [/\ @H.feasibility_check d R (interp_cert hm),
      @H.mapping_check d R (interp_cert hm),
      @H.graph_check d R (interp_cert hm),
      @H.inversibility_check d R (interp_cert hm) &
      @H.separability_check d R (interp_cert hm)].
Proof.
move=> /certP[/wfP hwf hfeas hmap hgraph [/rootP[hspc hinv hsep] _]].
split.
- exact: feasibility_check_correct hm (wf_ineq hwf) (wf_pts hwf) (wf_act hwf) hfeas.
- exact: mapping_check_correct hm hnv (wf_map hwf) hmap.
- exact: graph_check_correct hm (wf_graph hwf) (wf_desc hwf) (wf_fu hwf) hgraph.
- exact: inversibility_check_correct hm hnf (wf_ineq hwf) (wf_desc hwf) (wf_si hwf) (wf_ai hwf)
    (wf_wit hwf) (wf_sp hwf) hmap hspc hinv.
- exact: separability_check_correct hm (wf_ineq hwf) (wf_ai hwf) (wf_wit hwf) (wf_sp hwf)
    (wf_wt hwf) hmap hspc hsep.
Qed.

Theorem well_formedness_check_correct (hm : (0 < m)%N) (hnv : (0 < nv)%N) (hnf : (0 < nf)%N)
    (hd : (0 < d)%N) :
  L.VtxContainment.well_formedness_check c -> L.feasibility_check c -> L.separability_check c ->
  @CC.well_formedness_check_completeness d R (interp_cert hm).
Proof.
move=> /wfP hwf hfeas hsep.
split; first exact: facetsAreDSimplices_correct hm (wf_desc hwf).
split; first exact: mappingHasImageInPoints_correct hm hnv (wf_map hwf).
split; first exact: graphVerticesAreFacets_correct.
split; first exact: graphIsUndirected_correct hm (wf_graph hwf).
split; first exact: specialSimplexInSpecialCone_correct hm hnf (wf_si hwf) (wf_desc hwf) (wf_fu hwf).
exact: weightsAreStrictlyPositiveVectors_correct hm hnv hnf hd (wf_ineq hwf) (wf_pts hwf)
  (wf_act hwf) (wf_desc hwf) (wf_map hwf) (wf_si hwf) (wf_wt hwf) (wf_asu hwf) hfeas hsep.
Qed.

Theorem check_certificate_correct (hm : (0 < m)%N) (hnv : (0 < nv)%N) (hnf : (0 < nf)%N)
    (hd : (0 < d)%N) :
  L.VtxContainment.check_certificate c -> @CC.check_certificate_completeness d R (interp_cert hm).
Proof.
move=> hchk; have [h1 h2 h3 h4 h5] := vtx_containment_correct hm hnv hnf hchk.
have [hwf hfeas _ _ [/rootP[_ _ hsep] hfd]] := certP hchk.
have hdata := wfP hwf.
have hwf' := well_formedness_check_correct hm hnv hnf hd hwf hfeas hsep.
by split; [|split; [exact: full_dim_check_correct hm (wf_ineq hdata) (wf_fd hdata) hfd|]].
Qed.

End Interp.

(* -------------------------------------------------------------------------- *)
(* End to end: the certified points contain every vertex of the polytope      *)
(* -------------------------------------------------------------------------- *)

(* Imported last: [polyhedron]/[poly_base] introduce notations (['[P]], ...)
   that conflict with the grammar used above (['[u, v]], [||]). *)
From Polyhedra Require Import polyhedron poly_base.

Section EndToEnd.

Context (R : realFieldType) (c : L.Certificate).

Local Notation m := (nat_of_int (L.nb_inequalities c)).
Local Notation d := (nat_of_int (L.dimension c)).
Local Notation nv := (balen (L.vertices c)).
Local Notation nf := (balen (L.facets c)).

Corollary vertex_containment (hm : (0 < m)%N) (hnv : (0 < nv)%N) (hnf : (0 < nf)%N)
    (hd : (0 < d)%N) :
  L.VtxContainment.check_certificate c ->
  (vertex_set '[hpoly_of R c] `<=` points_of R c /\ compact '[hpoly_of R c])%fset.
Proof.
move=> hchk.
have [/wfP hdata _ _ _ _] := certP hchk.
apply: (@CC.certificate_completeness d R (interp_cert R hm) hd
          (normal_of_neq0 (wf_ineq hdata))).
by exact: check_certificate_correct hm hnv hnf hd hchk.
Qed.

End EndToEnd.
