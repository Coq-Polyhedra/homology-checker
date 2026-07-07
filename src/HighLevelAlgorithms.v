From mathcomp Require Import finmap all_ssreflect all_algebra.
From Polyhedra Require Import hpolyhedron inner_product polyhedron poly_base affine.
From DepotThese Require Import high_graph.
Import HPolyhedron. 

Section HighLevelChecks.

Context (R : realFieldType).
Context (d : nat).

Definition simplex m := {set 'I_m}.
Definition simplicialComplex m := {set simplex m}.

Notation simplex_graph m := (graph [choiceType of (simplex m)]).
Notation "'[ u , v ]" := (vdot u v).
Notation " A *m B" := (mulmx A B).
Notation "a %:M" := (scalar_mx a).
Notation "\matrix_ ( i < m , j < n ) E" := (matrix_of_fun (m:=m) (n:=n) matrix_key (fun i j => E)).
Notation "''[' P ]" := (@mk_poly2 _ _ P).
Notation "\pdim P" := (adim (hull P)).

Record Certificate := {
    polytope : 'hpoly[R]_d;
    points : {fset 'cV[R]_d};
    activeSets : 'cV[R]_d -> {set 'I_(polytope.`c)};
    triangulations : 'cV[R]_d -> simplicialComplex (polytope.`c);
    graph : simplex_graph (polytope.`c);
    specialVertex : 'cV[R]_d;
    (* specialSimplex : simplex (polytope.`c); *)
    specialSimplex : 'I_d -> 'I_(polytope.`c);
    witnesses : 'M[R]_(d,d);
    indices : simplex (polytope.`c) -> 'I_d
}.

(* General hypothesis *)
Definition polytopeIsFullDimensional (cert : Certificate) :=
  \pdim '[polytope cert] = d.+1.

(* Definitiion of the set F *)
Definition facets (cert : Certificate) :=
  [fset f | x in points cert, f in triangulations cert x].

(* Well-formedness condition on facets *)
Definition facetsAreDSimplices (cert : Certificate) :=
  forall sig : simplex (polytope cert).`c, sig \in (facets cert) -> #|sig| == d.

Definition triangulationsAreBasedOnActiveSets (cert : Certificate) :=
  forall x : 'cV[R]_d, x \in points cert -> 
  triangulations cert x \subset powerset (activeSets cert x).

(* Well-formedness condition on graph *)
Definition graphVerticesAreFacets (cert : Certificate) :=
  vertices (graph cert) = facets cert.

Definition graphIsUndirected (cert : Certificate) :=
  forall x y, y \in successors (graph cert) x <-> x \in successors (graph cert) y.

(* Well-formedness condition on the facets sigma^* *)
Definition specialSimplexInSpecialCone(cert : Certificate) :=
  (specialSimplex cert @: 'I_d) \in triangulations cert (specialVertex cert).

(* Condition T1 *)
Definition feasibility_check (cert : Certificate) :=
  let hP := polytope cert in
  let normal i := trmx (row i hP.`A) in
  let offset i := hP.`b i ord0 in
  {subset (points cert) <= hP} /\ forall x : 'cV[R]_d, (x \in points cert) ->
  activeSets cert x = [set i | i : 'I_(hP.`c) & '[normal i , x] == offset i].

(* Condition T2 *)
Definition triangulationsAreDisjoint (cert : Certificate) :=
  forall x y: 'cV[R]_d, x \in points cert -> y \in points cert -> x != y 
  -> triangulations cert x :&: triangulations cert y = set0.

(* Condition T3 *)
Definition graph_check (cert : Certificate) :=
  forall f, f \in vertices (graph cert) -> #|successors (graph cert) f| <= d /\
  forall i, (i \in f) -> exists f', (f' \in successors (graph cert) f) /\ f:\i \subset f'.

(* Condition T4 *)
Definition inversibility_check (cert : Certificate) :=
  \matrix_(i < d, j < d) ((polytope cert).`A (specialSimplex cert i) j) *m (witnesses cert) = 1%:M.

(* Condition T5 *)
Definition separation_check (cert : Certificate) :=
  forall f : simplex (polytope cert).`c, f \in triangulations cert (specialVertex cert)
  -> f != (specialSimplex cert @: 'I_d) -> exists j : 'I_(polytope cert).`c, j \in f /\
  ('[col (indices cert f) (witnesses cert), trmx (row j (polytope cert).`A)] <= 0)%R.

End HighLevelChecks.



