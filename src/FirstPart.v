From Coq Require Import Uint63 BinNat.
From mathcomp Require Import all_ssreflect.
From Bignums Require Import BigQ.
From BinReader Require Import BinReader.
Require Import PArray.
Require Import Coq.Program.Basics.
Import Order.Theory.

Section Uint63.

Fixpoint ifold_ {T : Type} (n : nat) (f : int -> T -> T) (i M : int) (x : T) :=
  if (i =? M)%uint63 then (i, x) else
    if n is n.+1 then
      let: (i, x) := ((i + 1)%uint63, f i x) in
      let: (i, x) := ifold_ n f i M x in
      let: (i, x) := ifold_ n f i M x in
      (i, x)
    else (i, x).

Definition ifold {T : Type} (f : int -> T -> T) (i : int) (x : T) :=
  (ifold_ Uint63.size f 0 i x).2.

End Uint63.

Section Array.

Definition defaultIntArray : array int := make 0%uint63 0%uint63.

Definition map {T1 T2 : Type} (f : T1 -> T2) (a : array T1):=
  ifold (fun i acc=> acc.[i <- f a.[i]]) (length a) (make (length a) (f (default a))).

Definition fold {T A : Type} (f : T -> A -> A) (a : array T) (x0 : A) :=
  ifold (fun i acc => f a.[i] acc) (length a) x0.

Definition foldi {T A : Type} (f : int -> T -> A -> A) (a : array T) (x0 : A) :=
  ifold (fun i acc => f i a.[i] acc) (length a) x0.

Definition fold_compose {A B C : Type} (f : B -> C -> C) (g : A -> B) (a : array A) (x0 : C) :=
  fold (compose f g) a x0.

Definition foldi_compose {A B C : Type} (f : int -> B -> C -> C) (g : A -> B) (a : array A) (x0 : C) :=
  foldi (fun i => compose (f i) g) a x0.

Definition fold2 {T1 T2 A : Type} (f : T1 -> T2 -> A -> A) (a1 : array T1) (a2 : array T2) (x0 : A) :=
  ifold (fun i acc => f a1.[i] a2.[i] acc) (if (length a1 <? length a2)%uint63 then length a1 else length a2) x0.

Definition fold_alt {T A : Type} (f_in f_notin : T -> A -> A) (s : array T) (notin : array int) (x : A) :=
  let res := foldi (fun i x acc =>
    if (acc.2 <? length notin)%uint63 ==> (i <? notin.[acc.2])%uint63 then 
      (f_notin x acc.1, acc.2) 
      else (f_in x acc.1, (acc.2+1)%uint63)
    ) s (x, 0%uint63) in
    res.1.

Definition for_alli {T : Type} (f : int -> T -> bool) (a : array T) :=
  foldi (fun i x acc => acc && f i x) a true.

Definition for_all_compose {A B : Type} (f : B -> bool) (g : A -> B) (a : array A) :=
  fold_compose (fun x acc => acc && f x) g a true.

Definition for_alli_compose {A B : Type} (f : int -> B -> bool) (g : A -> B) (a : array A) :=
  foldi_compose (fun i x acc => acc && (f i x)) g a true.

Definition for_all2 {T1 T2 : Type} (f : T1 -> T2 -> bool) (a : array T1) (b : array T2) :=
  fold2 (fun x y acc => acc && f x y) a b true.

Definition for_all {T : Type} (f : T -> bool) (a : array T) :=
  fold (fun x acc => acc && f x) a true.

Definition for_all_alt {T : Type} (f_in f_notin : T -> bool) (s : array T) (notin : array int) :=
  fold_alt (fun x acc => f_in x && acc) (fun x acc => f_notin x && acc) s notin true.

Definition for_all_matrix {T : Type} (f : T -> bool) (a : array (array T)) : bool :=
  for_all (for_all f) a.

Definition for_alli_matrix {T : Type} (f : int -> int -> T -> bool) (a : array (array T)) : bool :=
  for_alli (fun i _ => for_alli (f i) a.[i]) a.

Definition existi {T : Type} (f : int -> T -> bool) (a : array T) :=
  foldi (fun i x acc => acc || f i x) a false.

Definition exist {T : Type} (f : T -> bool) (a : array T) :=
  fold (fun x acc => acc || f x) a false.

Definition mem {T : Type} (eqT : T -> T -> bool) (a : array T) (x : T) : bool :=
  exist (fun y => eqT x y) a.

Definition mem_sorted {T : Type} (ltT : T -> T -> bool) (a : array T) (x : T) : bool :=
  let res := 
  fold (fun y acc => 
    if acc is Some _ then acc 
    else 
      if ltT y x then None
      else if ltT x y then Some false
      else Some true) a None
  in
  match res with
  | None => false
  | Some b => b
  end. 

Definition eqbArray {T : Type} (eqT : T -> T -> bool) (a b : array T) : bool :=
  for_all2 eqT a b.

(* We define a strict lexicographic order on arrays. *)
Definition isLtWitness {T : Type} (eqT : T -> T -> bool) (ltT : T -> T -> bool) (a b : array T) (i : int) : bool :=
  (for_alli (fun j y => (i <=? j)%uint63 || eqT y b.[j]) a) && ltT a.[i] b.[i].

Definition ltbArray {T : Type} (eqT : T -> T -> bool) (ltT : T -> T -> bool) (a b : array T) : bool :=
  (((length a) <? (length b))%uint63) || 
  ((((length a) =? (length b))%uint63) && existi (fun i _ => isLtWitness eqT ltT a b i) a).

Definition countOccurences {T: Type} (eqT : T -> T -> bool) (a : array T) (x : T) : int :=
  fold (fun y acc => if eqT x y then (acc + 1)%uint63 else acc) a 0%uint63.

Definition isUnique {T : Type} (eqT : T -> T -> bool) (a : array T) (x : T) : bool := 
  ((countOccurences eqT a x) <=? 1)%uint63.

(* For more efficiency, we could iterate through a, count and store the number of occurences of
each element in a dictionary. *)

Definition isDuplicateFree {T : Type} (eqT : T -> T -> bool) (a : array T) : bool :=
  for_all (isUnique eqT a) a.

Definition compareConsecutive {T : Type} (ltT : T -> T -> bool) (a : array T) (i : int) : bool :=
  ltT (a.[i]) (a.[(i+1)%uint63]). 

Definition isStrictlySorted {T : Type} (ltT : T -> T -> bool) (a : array T) : bool := 
  for_alli (fun i _ => ((i =? (length(a)-1)%uint63)%uint63) || (compareConsecutive ltT a i)) a.

Definition inRange {T : Type} (leT : T -> T -> bool) (m M : T) (x : T) : bool :=
  (leT m x) && (leT x M).

Definition allInRange {T : Type} (leT : T -> T -> bool) (m M : T) (a : array T) : bool :=
  for_all (inRange leT m M) a.

Definition hasLength {T : Type} (k : int) (a : array T) : bool :=
  (length a =? k)%uint63.

Definition isEmpty {T : Type} (a : array T) : bool :=
  hasLength 0%uint63 a.

Definition isValidIndex {T : Type} (a : array T) (x : int) : bool :=
  inRange Uint63.leb 0%uint63 (length a - 1)%uint63 x.

Definition areComposableSimpleArray {T : Type} (a : array int) (b : array T) : bool :=
  for_all (isValidIndex b) a.

Definition isValidPairIndex {T : Type} (a : array (array T)) (c : int*int) : bool :=
  (isValidIndex a (c.1)) && (isValidIndex a.[c.1] (c.2)).

Definition areComposablePairArray {T : Type} (a : array (int*int)) (b : array (array T)) : bool :=
  for_all (isValidPairIndex b) a.

Definition areComposableMatrix {T : Type} (a : array (array int)) (b : array T) : bool :=
  for_all_matrix (isValidIndex b) a.

(* The function is not defined for all a and b and must be used together with areComposableSimpleArray. *)
Definition composeSimpleArray {T : Type} (a : array int) (b : array T) : array T :=
  map (fun x => b.[x]) a.

Definition isInverseSimpleArrayAtIndex (a : array int) (b : array int) (i : int) : bool :=
  (b.[a.[i]] =? i)%uint63.

(* The function is not defined for all a and b and must be used together with areComposableSimpleArray *) 
Definition isInverseSimpleArray (a : array int) (b: array int) :=
  for_alli (fun i _ => isInverseSimpleArrayAtIndex a b i) a.

Definition isInversePairArrayAtIndex (a : array (int*int)) (b : array (array int)) (i : int) : bool :=
  (b.[a.[i].1].[a.[i].2] =? i)%uint63.

(* The function is not defined for all a and b and must be used together with areComposablePairArray *) 
Definition isInversePairArray (a : array (int*int)) (b : array (array int)) : bool :=
  for_alli (fun i _ => isInversePairArrayAtIndex a b i) a.

Definition isInverseMatrixAtIndex (a : array (array int)) (b: array (int*int)) (i j : int) : bool :=
  ((b.[a.[i].[j]]).1 =? i)%uint63 && ((b.[a.[i].[j]]).2 =? j)%uint63.

(* The function is not defined for all a and b and must be used together with areComposableMatrix *) 
Definition isInverseMatrix (a : array (array int)) (b : array (int*int)) : bool :=
  for_alli_matrix (fun i j _ => isInverseMatrixAtIndex a b i j) a.

End Array.

Definition Graph := array (array int).

Section Graph.

Definition isVertex (g : Graph) (x : int) :=
  isValidIndex g x. 

(* The function is not defined for all x and must be used together with isVertex. *)
Definition isLocallyUndirected (g : Graph) (x : int) :=
  for_all (fun y => mem (Uint63.eqb) g.[y] x) g.[x].

Definition isUndirected (g : Graph) :=
  for_alli (fun i _ => isLocallyUndirected g i) g. 

Definition hasSimpleEdges (g : Graph) := 
  for_all (isDuplicateFree Uint63.eqb) g.

Definition hasLocallyNoLoop (g : Graph) (x : int) :=
  negb (mem (Uint63.eqb) g.[x] x).

Definition hasNoLoops (g : Graph) :=
  for_alli (fun i _ => hasLocallyNoLoop g i) g.

Definition isSimpleGraph (g : Graph) :=
  (hasSimpleEdges g) && (hasNoLoops g).

Definition isRegular (g : Graph) (k : int) := 
  for_all (hasLength k) g.

End Graph.

Section BigZ.

Definition array_bigZ_dot (x y : array bigZ) : bigZ :=
  fold2 (fun x y res=> BigZ.add res (BigZ.mul x y)) x y 0%bigZ.

End BigZ.

Definition Normal := array bigZ. 
Definition Bound := bigZ.

Record Inequality := {
  normal : Normal;
  bound : Bound
}.

Definition Inequalities := array Inequality.

Definition LocalDescription := array int.
Definition FacetIndex := int.

Record LocalFacet := {
  localDescription : LocalDescription;
  facetIndex : FacetIndex
}.

Definition Numerators := array bigZ. 
Definition CommonDenominator := bigN.

Record Point := {
  numerators : Numerators;
  commonDenominator : CommonDenominator
}.

Definition ActiveSet := array int.
Definition LocalFacets := array LocalFacet.

Record Vertex := {
  activeSet : array int;
  point : Point;
  localFacets : LocalFacets
}.

Definition Vertices := array Vertex.

Definition GlobalDescription := array int.
Definition FacetLabel := (int * int)%type.

Record GlobalFacet := {
  globalDescription : GlobalDescription;
  facetLabel : FacetLabel
}.

Definition GlobalFacets := array GlobalFacet.

Record Certificate := {
  inequalities : Inequalities;
  vertices : Vertices;
  graph : Graph;
  facets : GlobalFacets;
  root : int * (array int * (array (array bigQ) * array int))
}.

Definition build_cert cert := 
  let inequalities := cert.1 in 
  let vertices := cert.2.1 in
  let graph := cert.2.2.1.1 in
  let facets := cert.2.2.1.2 in
  let root := cert.2.2.2 in
  {| inequalities := inequalities; vertices := vertices; graph := graph; facets := facets; root := root |}.

Section ActiveSets.

Definition foldActiveSets {T : Type} (f : ActiveSet -> T -> T) (cert : Certificate) (x0 : T) :=
  let vertices := vertices cert in
  fold_compose f activeSet vertices x0.

Definition foldiActiveSets {T : Type} (f : int -> ActiveSet -> T -> T) (cert : Certificate) (x0 : T) :=
  let vertices := vertices cert in
  foldi_compose f activeSet vertices x0.

Definition forAllActiveSets (f : ActiveSet -> bool) (cert : Certificate) :=
  foldActiveSets (fun x acc => acc && f x) cert true.

Definition forAlliActiveSets (f : int -> ActiveSet -> bool) (cert : Certificate) :=
  foldiActiveSets (fun i x acc => acc && f i x) cert true.

End ActiveSets.

Section LocalFacetsSets.

Definition foldLocalFacetsSets {T : Type} (f : LocalFacets -> T -> T) (cert : Certificate) (x0 : T) :=
  let vertices := vertices cert in
  fold_compose f localFacets vertices x0.

Definition foldiLocalFacetsSets {T : Type} (f : int -> LocalFacets -> T -> T) (cert : Certificate) (x0 : T) :=
  let vertices := vertices cert in
  foldi_compose f localFacets vertices x0.

Definition forAllLocalFacetsSets (f : LocalFacets -> bool) (cert : Certificate) :=
  foldLocalFacetsSets (fun x acc => acc && f x) cert true.

Definition forAlliLocalFacetsSets (f : int -> LocalFacets -> bool) (cert : Certificate) :=
  foldiLocalFacetsSets (fun i x acc => acc && f i x) cert true.

End LocalFacetsSets.

Section LocalFacets.

Definition foldLocalFacets {T : Type} (f : LocalDescription -> T -> T) (cert : Certificate) (x0 : T) :=
  foldLocalFacetsSets (fun lcl_facets acc => fold_compose f localDescription lcl_facets acc) cert x0.

Definition foldiLocalFacets {T : Type} (f : int -> int -> LocalDescription -> T -> T) (cert : Certificate) (x0 : T) :=
  foldiLocalFacetsSets (fun i lcl_facets acc => foldi_compose (f i) localDescription lcl_facets acc) cert x0.

Definition forAllLocalFacets (f : LocalDescription -> bool) (cert : Certificate) :=
  foldLocalFacets (fun x acc => acc && f x) cert true.

Definition forAlliLocalFacets (f : int -> int -> LocalDescription -> bool) (cert : Certificate) :=
  foldiLocalFacets (fun i j x acc => acc && f i j x) cert true.

End LocalFacets.

Section FacetIndices.

Definition foldFacetIndices {T : Type} (f : FacetIndex -> T -> T) (cert : Certificate) (x0 : T) :=
  foldLocalFacetsSets (fun lcl_facets acc => fold_compose f facetIndex lcl_facets acc) cert x0.

Definition foldiFacetIndices {T : Type} (f : int -> int -> FacetIndex -> T -> T) (cert : Certificate) (x0 : T) :=
  foldiLocalFacetsSets (fun i lcl_facets acc => foldi_compose (f i) facetIndex lcl_facets acc) cert x0.

Definition forAllFacetIndices (f : FacetIndex -> bool) (cert : Certificate) :=
  foldFacetIndices (fun x acc => acc && f x) cert true.

Definition forAlliFacetIndices (f : int -> int -> FacetIndex -> bool) (cert : Certificate) :=
  foldiFacetIndices (fun i j x acc => acc && f i j x) cert true.

End FacetIndices.

Section GlobalFacets.

Definition foldGlobalFacets {T : Type} (f : GlobalDescription -> T -> T) (cert : Certificate) (x0 : T) :=
  let facets := facets cert in
  fold_compose f globalDescription facets x0.

Definition foldiGlobalFacets {T : Type} (f : int -> GlobalDescription -> T -> T) (cert : Certificate) (x0 : T) :=
  let facets := facets cert in
  foldi_compose f globalDescription facets x0.

Definition forAllGlobalFacets (f : GlobalDescription -> bool) (cert : Certificate) :=
  foldGlobalFacets (fun x acc => acc && f x) cert true.

Definition forAlliGlobalFacets (f : int -> GlobalDescription -> bool) (cert : Certificate) :=
  foldiGlobalFacets (fun i x acc => acc && f i x) cert true.

End GlobalFacets.

Section FacetLabels.

Definition foldFacetLabels {T : Type} (f : FacetLabel -> T -> T) (cert : Certificate) (x0 : T) :=
  let facets := facets cert in
  fold_compose f facetLabel facets x0.

Definition foldiFacetLabels {T : Type} (f : int -> FacetLabel -> T -> T) (cert : Certificate) (x0 : T) :=
  let facets := facets cert in
  foldi_compose f facetLabel facets x0.

Definition forAllFacetLabels (f : FacetLabel -> bool) (cert : Certificate) :=
  foldFacetLabels (fun x acc => acc && f x) cert true.

Definition forAlliFacetLabels (f : int -> FacetLabel -> bool) (cert : Certificate) :=
  foldiFacetLabels (fun i x acc => acc && f i x) cert true.

End FacetLabels.


Definition areActiveSetsWellConstructed (cert : Certificate) :=
  let m := length (inequalities cert) in
  let vertices := vertices cert in
  (forAllActiveSets (isStrictlySorted Uint63.ltb) cert)
  && (forAllActiveSets (allInRange Uint63.leb (0%uint63) (m-1)%uint63) cert). 

Definition areLocalFacetSetsWellConstructed (cert : Certificate) :=
  let vertices := vertices cert in
  (forAllLocalFacets (isStrictlySorted Uint63.ltb) cert)
  && (forAlliLocalFacets (fun i j facet => (allInRange Uint63.leb (0%uint63) (length (activeSet vertices.[i])-1)%uint63) facet) cert).

(* We should use the areComposable_functions. *)

Definition isLocalFacetIndexingWellConstructed (cert : Certificate) :=
  let nbFacets := length (facets cert) in
  forAllFacetIndices (inRange Uint63.leb 0%uint63 (nbFacets-1)%uint63) cert.

(* The bijection between the facets appearing in the abstract triangulations of the normal cones
   and the set of facets represented by lbl ensures that the facets appearing in both structures
   are exactly the same, up to a local renumbering induced by the activation sets.
   The previous functions are sufficient to verify that the facets appearing in the labels
   are well-constructed (no duplicates and in the right range). *)

Definition isFacetLabelingWellConstructed (cert : Certificate) :=
  let vertices := vertices cert in 
  forAllFacetLabels (fun label => (inRange (Uint63.leb) 0%uint63 (length (vertices)-1)%uint63 label.1)
  && (inRange (Uint63.leb) 0%uint63 (length (localFacets vertices.[label.1])-1)%uint63 label.2)) cert.

Definition isGraphWellConstructed (cert : Certificate) :=
  let graph := graph cert in
  let nbFacets := length (facets cert) in
  (length graph =? nbFacets)%uint63 && (for_all_matrix (isVertex graph) graph).
  
Definition areActiveSetsUnique (cert : Certificate) :=
  let vertices := vertices cert in
  isStrictlySorted (fun vertex1 vertex2 => (ltbArray Uint63.eqb Uint63.ltb) (activeSet vertex1) (activeSet vertex2)) vertices.

Definition areFacetsUnique (cert : Certificate) :=
  let facets := facets cert in
  isStrictlySorted (fun f1 f2 => (ltbArray Uint63.eqb Uint63.ltb) (globalDescription f1) (globalDescription f2)) facets.

Definition isUndirectedSimpleGraph (cert : Certificate) :=
  let graph := graph cert in
  (isUndirected graph) && (hasNoLoops graph).

Definition allFacetsHaveCardinality (cert : Certificate) :=
  let d := length (normal ((inequalities cert).[0])) in
  forAllGlobalFacets (hasLength d) cert.

Definition isGraphDRegular (cert : Certificate) :=
  let graph := graph cert in
  let d := length (normal ((inequalities cert).[0])) in
  isRegular graph d.

Definition isFacetLabelingBijective (cert : Certificate) :=
  let vertices := vertices cert in
  let facets := facets cert in
  (forAlliFacetLabels (fun i label => (facetIndex (localFacets vertices.[label.1]).[label.2] =? i)%uint63) cert)
  && (forAlliFacetIndices (fun i j index => ((facetLabel (facets.[index])).1 =? i)%uint63 && 
  ((facetLabel (facets.[index])).2 =? j)%uint63) cert).

Definition isFacetIndexingBijective (cert : Certificate) :=
  let vertices := vertices cert in
  let facets := facets cert in
  forAlliFacetLabels (fun i label => eqbArray (fun x y => (x =? (activeSet vertices.[label.1]).[y])%uint63) 
  (globalDescription facets.[i]) (localDescription (localFacets (vertices.[label.1])).[label.2])) cert.

Definition check_ineqs (ineqs : Inequalities) (active_set : ActiveSet) (x : Point) :=
  for_all_alt 
    (fun ineq => (array_bigZ_dot (normal ineq) (numerators x) =? BigZ.mul (bound ineq) (BigZ.Pos (commonDenominator x)))%bigZ)
    (fun ineq => (array_bigZ_dot (normal ineq) (numerators x) <? BigZ.mul (bound ineq) (BigZ.Pos (commonDenominator x)))%bigZ)
    ineqs active_set.

(* The following variant of check_ineqs is easier to prove, but 25% slower on non-Hirsch polytopes *)
(*
Definition check_ineqs (ineqs : array (array bigZ * bigZ)) (saturated : array int) (x : array bigZ * bigN) :=
  for_alli (fun i ineq =>
    if mem_sorted Uint63.ltb i saturated then 
      (array_bigZ_dot ineq.1 x.1 =? BigZ.mul ineq.2 (BigZ.Pos x.2))%bigZ
    else 
      (array_bigZ_dot ineq.1 x.1 <? BigZ.mul ineq.2 (BigZ.Pos x.2))%bigZ
  ) ineqs.
*)

Definition feasibility_check (cert : Certificate) := 
  let inequalities := inequalities cert in
  let vertices := vertices cert in
  ifold (fun i acc => acc && check_ineqs inequalities (activeSet vertices.[i]) (point vertices.[i])) 
    (length vertices) true.

Definition adjacency_check (cert : Certificate) :=
  let graph := graph cert in
  let facets := facets cert in
  for_alli_matrix (fun i j v => for_all (fun x => (x =? (globalDescription (facets.[i])).[j])%uint63
  || (mem Uint63.eqb (globalDescription facets.[v]) x)) (globalDescription (facets.[i]))) graph.

Definition check_certificate (cert : Certificate) :=
  (areActiveSetsWellConstructed cert)
  && (areLocalFacetSetsWellConstructed cert)
  && (isLocalFacetIndexingWellConstructed cert)
  && (isFacetLabelingWellConstructed cert)
  && (isGraphWellConstructed cert)
  && (areActiveSetsUnique cert)
  && (areFacetsUnique cert)
  && (isUndirectedSimpleGraph cert)
  && (allFacetsHaveCardinality cert)
  && (isGraphDRegular cert)
  && (isFacetLabelingBijective cert)
  && (isFacetIndexingBijective cert)
  && (feasibility_check cert)
  && (adjacency_check cert). 

Time LoadData "../lrs-postprocess/data/poly20dim21-cert.bin" As cert.

Section Benchmark.

Let cert := build_cert cert.
Time Eval vm_compute in 
  feasibility_check cert.
Time Eval vm_compute in
  


End Benchmark.
