From mathcomp Require Import finmap all_ssreflect all_algebra.
From Polyhedra Require Import hpolyhedron inner_product polyhedron poly_base affine vector_order.
From DepotThese Require Import high_graph.
Import HPolyhedron. 

Section HighLevelChecks.

Context (R : realFieldType).
Context (d : nat).

Definition simplex m := {set 'I_m}.
Definition simplicialComplex m := {fset simplex m}.

Notation simplex_graph m := (graph [choiceType of (simplex m)]).
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
    activeSets : 'cV[R]_d -> {set 'I_(polytope.`c)};
    facets : simplicialComplex (polytope.`c);
    mapping : simplex (polytope.`c) -> 'cV[R]_d;
    graph : simplex_graph (polytope.`c);
    specialVertex : 'cV[R]_d;
    specialSimplex : 'I_d -> 'I_(polytope.`c);
    witnesses : 'M[R]_(d,d);
    weights : simplex (polytope.`c) -> 'cV[R]_d
}.

Definition normalVector (polytope : 'hpoly[R]_d) (i : 'I_(polytope.`c)) :=
  trmx (row i polytope.`A).

(* General hypothesis *)
Definition polytopeIsFullDimensional (cert : Certificate) :=
  \pdim '[polytope cert] = d.+1.

(* Well-formedness condition on facets *)
Definition facetsAreDSimplices (cert : Certificate) :=
  forall f : simplex (polytope cert).`c, f \in (facets cert) -> #|f| == d.

(* Well-formedness condition on mapping *)
Definition mappingHasImageInPoints (cert : Certificate) :=
  forall f : simplex (polytope cert).`c, f \in facets cert -> mapping cert f \in points cert.

(* Well-formedness condition on graph *)
Definition graphVerticesAreFacets (cert : Certificate) :=
  vertices (graph cert) = facets cert.

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

End HighLevelChecks.



