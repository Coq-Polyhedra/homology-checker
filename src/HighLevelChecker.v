From mathcomp Require Import finmap all_ssreflect all_algebra.
From Polyhedra Require Import hpolyhedron inner_product polyhedron poly_base affine vector_order.
From PolyhedraHirsch Require Import high_graph.
Import HPolyhedron. 

Section HighLevelChecks.

Context (R : realFieldType).
Context (d : nat).

Definition simplex m := {set 'I_m}.
Definition simplicialComplex m := {set simplex m}.

Notation simplex_graph m := (graph [choiceType of (simplex m)]).
Notation vertex_graph := (graph [choiceType of ('cV[R]_d)]).
Notation "'[ u , v ]" := (vdot u v).
Notation " A *m B" := (mulmx A B).
Notation "x <=m y" := (lev x y).
Notation "a %:M" := (scalar_mx a).
Notation "\matrix_ ( i < m , j < n ) E" := (matrix_of_fun (m:=m) (n:=n) matrix_key (fun i j => E)).
Notation "''[' P ]" := (@mk_poly2 _ _ P).
Notation "\pdim P" := (adim (hull P)).

Record Certificate := {
    polytope : 'hpoly[R]_d;
    points : {fset 'cV[R]_d};
    full_dim_point : 'cV[R]_d;
    full_dim_dir : 'M[R]_(d,d);
    full_dim_inv : 'M[R]_(d,d);
    activeSets : 'cV[R]_d -> {set 'I_(polytope.`c)};
    facets : simplicialComplex (polytope.`c);
    mapping : simplex (polytope.`c) -> 'cV[R]_d;
    graph : simplex_graph (polytope.`c);
    specialVertex : 'cV[R]_d;
    specialSimplex : 'I_d -> 'I_(polytope.`c);
    witnesses : 'M[R]_(d,d);
    weights : simplex (polytope.`c) -> 'cV[R]_d;
    geom_graph : vertex_graph
}.

Definition normalVector (polytope : 'hpoly[R]_d) (i : 'I_(polytope.`c)) :=
  trmx (row i polytope.`A).

Definition incomparable {T : finType} (A B : {set T}) :=
  ~~ (A \subset B) && ~~ (B \subset A).

(* Well-formedness condition on facets *)
Definition facetsAreDSimplices (cert : Certificate) :=
  forall f : simplex (polytope cert).`c, f \in (facets cert) -> #|f| == d.

(* Well-formedness condition on mapping *)
Definition mappingHasImageInPoints (cert : Certificate) :=
  forall f : simplex (polytope cert).`c, f \in facets cert -> mapping cert f \in points cert.

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
  forall f : simplex (polytope cert).`c, mapping cert f = (specialVertex cert)
  -> f != (specialSimplex cert @: 'I_d) -> (0 <=m (weights cert f)) /\ (weights cert f <> 0%R).
  
(* Well-formedness condition on the geometric graph *)
Definition geomGraphVerticesArePoints (cert : Certificate) :=
  vertices (geom_graph cert) = points cert.

Definition geomGraphIsImageOfGraph (cert : Certificate) :=
  forall v w : 'cV[R]_d, v \in vertices (geom_graph cert) -> w \in vertices (geom_graph cert)
  -> (w \in successors (geom_graph cert) v <-> exists fv fw : simplex (polytope cert).`c, 
  fv \in vertices (graph cert) /\ fw \in successors (graph cert) fv /\ mapping cert fv = v /\ mapping cert fw = w).

(* Full dimension hypothesis *)
Definition full_dim_check (cert : Certificate) :=
  full_dim_point cert \in points cert 
  /\ forall i : 'I_d, (full_dim_point cert + col i (full_dim_dir cert))%R \in points cert
  /\ forall (i j : 'I_d), (i = j /\ '[col i (full_dim_dir cert), col j (full_dim_inv cert)] <> 0)%R
  \/ (i <> j /\ '[col i (full_dim_dir cert), col j (full_dim_inv cert)] = 0)%R.

(* Condition T1 *)
Definition feasibility_check (cert : Certificate) :=
  let hP := polytope cert in
  {subset (points cert) <= hP} /\ forall x : 'cV[R]_d, (x \in points cert) ->
  activeSets cert x = [set i | i : 'I_(hP.`c) & '[normalVector hP i , x] == hP.`b i ord0].

(* Condition T2 *)
Definition mapping_check (cert : Certificate) :=
  forall f : simplex (polytope cert).`c, f \in facets cert ->
  f \subset activeSets cert (mapping cert f).

(* Condition T3 *)
Definition graph_check (cert : Certificate) :=
  forall f, f \in vertices (graph cert) -> #|successors (graph cert) f| <= d /\
  forall i, (i \in f) -> exists f', (f' \in successors (graph cert) f) /\ f:\i \subset f'.

(* Condition T4 *)
Definition inversibility_check (cert : Certificate) :=
  forall (i j : 'I_d), (i = j /\ '[\col_k ((polytope cert).`A (specialSimplex cert i) k), (col j (witnesses cert))] > 0)%R
  \/ (i <> j /\ '[\col_k ((polytope cert).`A (specialSimplex cert i) k), (col j (witnesses cert))] = 0)%R.

(* Condition T5 *)
Definition separability_check (cert : Certificate) :=
  forall f : simplex (polytope cert).`c, mapping cert f = (specialVertex cert)
  -> f != (specialSimplex cert @: 'I_d)
  -> forall i : 'I_(polytope cert).`c, i \in f ->
  ('[(witnesses cert) *m (weights cert f) , normalVector (polytope cert) i] <= 0)%R.

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



