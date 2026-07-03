From mathcomp Require Import finmap all_ssreflect all_algebra.
From Polyhedra Require Import hpolyhedron inner_product.
From DepotThese Require Import high_graph.
Import HPolyhedron. 

Section HighLevelChecks.

Context (R : realFieldType).
Context (d : nat).

Definition simplex m := {set 'I_m}.
Definition simplicialComplex m := {set simplex m}.

Notation m_graph m := (graph [choiceType of (simplex m)]).

Record Certificate := {
    polytope : 'hpoly[R]_d;
    points : {fset 'cV[R]_d};
    activeSets : 'cV[R]_d -> {set 'I_(polytope.`c)};
    abstractTriangulations : 'cV[R]_d -> simplicialComplex (polytope.`c);
    graph : m_graph (polytope.`c)
}.

Definition facets (cert : Certificate) :=
  [fset sig | x in points cert, sig in abstractTriangulations cert x].

Definition areAbstractTriangulationsWellConstructed (cert : Certificate) :=
  forall x : 'cV[R]_d, x \in points cert -> forall sig : simplex (polytope cert).`c, 
  sig \in (abstractTriangulations cert x) -> sig \subset (activeSets cert x).

Definition isGraphWellConstructed (cert : Certificate) :=
  vertices (graph cert) = facets cert.

Definition areActiveSetsUnique (cert : Certificate) :=
  {in (points cert) &, injective (activeSets cert)}.

(* Vérifie-t-on (/doit-on vérifier) que les facettes 
n'apparaissent pas dans des cônes normaux différents ? *)

Definition isUndirectedGraph (cert : Certificate) :=
  (forall x y, (y \in successors (graph cert) x) <-> (x \in successors (graph cert) y)).

Definition allFacetsHaveCardinality (cert : Certificate) :=
  forall sig : simplex (polytope cert).`c, sig \in (facets cert) -> #|sig| == d.

Definition isGraphDRegular (cert : Certificate) :=
  forall x, x \in vertices (graph cert) -> #|successors (graph cert) x| = d.  

Notation "'[ u , v ]" := (vdot u v).

Definition feasibility_check (cert : Certificate) :=
  let hP := polytope cert in
  let normal i := trmx (row i hP.`A) in
  let offset i := hP.`b i ord0 in
  {subset (points cert) <= hP} /\ forall x : 'cV[R]_d, (x \in points cert) ->
  activeSets cert x = [set i | i : 'I_(hP.`c) & '[normal i , x] == offset i].

Definition adjacencyProperty (cert : Certificate) :=
    forall sig, (sig \in vertices (graph cert)) -> forall i, (i \in sig) -> 
    exists! rho, (rho \in successors (graph cert) sig) /\ (sig:\i \subset rho). 

End HighLevelChecks.



