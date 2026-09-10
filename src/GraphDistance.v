(* -------------------------------------------------------------------------- *)
(* Distance labellings of a graph                                             *)
(*                                                                            *)
(* A labelling [lab] of the vertices of a graph, together with a source [s],  *)
(* certifies the distances from [s] when [lab s = 0], the label grows by at   *)
(* most one along every edge, and every other vertex has a neighbour          *)
(* labelled one less. The first two conditions bound distances from below     *)
(* along any path, the third exhibits a path of length [lab y] to every [y]:  *)
(* the eccentricity of [s] is then the largest label.                         *)
(* -------------------------------------------------------------------------- *)

From mathcomp Require Import all_ssreflect finmap.
From PolyhedraHirsch Require Import high_graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section DistanceLabelling.

Context (T : choiceType) (G : graph T) (s : T) (lab : T -> nat).

Definition source_labelled := s \in vertices G /\ lab s = 0.

Definition edges_labelled :=
  forall x y : T, edges G x y -> lab y <= (lab x).+1.

Definition parents_labelled :=
  forall y : T, y \in vertices G -> y <> s ->
  exists x : T, edges G y x /\ (lab x).+1 = lab y.

(* The eccentricity of [s] is [D]: every vertex is within distance [D], and
   some vertex is at distance at least [D]. *)
Definition eccentricity_is (D : nat) :=
  (forall y : T, y \in vertices G ->
     exists p : epath G, is_path p s y /\ size_path p <= D)
  /\ (exists y : T, y \in vertices G /\
        forall p : epath G, is_path p s y -> D <= size_path p).

Hypothesis edges_sym : forall x y : T, edges G x y -> edges G y x.
Hypothesis hs : source_labelled.
Hypothesis he : edges_labelled.
Hypothesis hp : parents_labelled.

(* -------------------------------------------------------------------------- *)
(* Lower bound: along a walk the label grows by at most its length            *)
(* -------------------------------------------------------------------------- *)

Lemma lab_walk (x : T) (w : seq T) :
  path (edges G) x w -> lab (last x w) <= lab x + size w.
Proof.
elim: w x => [|y w ih] x /=; first by rewrite addn0.
move=> /andP[hxy hw]; apply: (leq_trans (ih _ hw)).
by rewrite addnS -addSn leq_add2r; exact: he.
Qed.

Lemma lab_le_path (p : epath G) : lab (dst p) <= lab (src p) + size_path p.
Proof. by rewrite -(last_dst p); exact: lab_walk (path_walk p). Qed.

Lemma lab_le_path_from_source (y : T) (p : epath G) :
  is_path p s y -> lab y <= size_path p.
Proof.
move=> [hsrc hdst]; have := lab_le_path p.
by rewrite hsrc hdst; case: hs => _ ->.
Qed.

(* -------------------------------------------------------------------------- *)
(* Upper bound: following parents yields a path of length [lab y]             *)
(* -------------------------------------------------------------------------- *)

(* A walk from [s] whose labels are 0, 1, ..., [size w] in order. *)
Lemma walk_of_lab (n : nat) (y : T) :
  y \in vertices G -> lab y = n ->
  exists w : seq T,
    [/\ path (edges G) s w, last s w = y, size w = n & map lab (s :: w) = iota 0 n.+1].
Proof.
elim: n y => [|n ih] y hy hlab.
  case: (y =P s) => [->|hne]; first by exists [::]; split=> //=; case: hs => _ ->.
  by have [x [_ hx]] := hp hy hne; rewrite hlab in hx.
have hne : y <> s by move=> he0; rewrite he0 in hlab; case: hs => _ h0; rewrite h0 in hlab.
have [x [hyx hx]] := hp hy hne.
have hxG : x \in vertices G := edge_vtxr hyx.
have [w [hw hlast hsize hlabs]] := ih x hxG (eq_add_S _ _ (etrans hx hlab)).
exists (rcons w y); split.
- by rewrite rcons_path hw hlast; exact: edges_sym.
- exact: last_rcons.
- by rewrite size_rcons hsize.
- rewrite -rcons_cons map_rcons hlabs hlab.
  by rewrite -cats1 -[n.+2]addn1 iotaD add0n.
Qed.

Lemma path_of_lab (y : T) : y \in vertices G ->
  exists p : epath G, is_path p s y /\ size_path p = lab y.
Proof.
move=> hy; have [w [hw hlast hsize hlabs]] := @walk_of_lab (lab y) y hy (erefl _).
have huniq : uniq (s :: w).
  by apply: (map_uniq (f := lab)); rewrite hlabs; exact: iota_uniq.
have hsG : s \in vertices G by case: hs.
have hlast' : last s w == y by apply/eqP.
by exists (@EPath _ _ (@GPath _ _ s y w hsG hw hlast') huniq); split.
Qed.

(* -------------------------------------------------------------------------- *)
(* The eccentricity                                                           *)
(* -------------------------------------------------------------------------- *)

Theorem eccentricity_of_labelling (D : nat) :
  (forall y : T, y \in vertices G -> lab y <= D) ->
  (exists y : T, y \in vertices G /\ lab y = D) ->
  eccentricity_is D.
Proof.
move=> hbound [y0 [hy0 hlab0]]; split.
- move=> y hy; have [p [hpath hsize]] := path_of_lab hy.
  by exists p; split=> //; rewrite hsize; exact: hbound.
- exists y0; split=> // p hpath.
  by rewrite -hlab0; exact: lab_le_path_from_source hpath.
Qed.

End DistanceLabelling.
