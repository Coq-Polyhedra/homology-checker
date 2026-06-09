From Coq Require Import Uint63 BinNat.
From mathcomp Require Import all_ssreflect.
From Bignums Require Import BigQ.
From BinReader Require Import BinReader.
Require Import PArray.
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

Definition map {T1 T2 : Type} (f : T1 -> T2) (a : array T1):=
  ifold (fun i acc=> acc.[i <- f a.[i]]) (length a) (make (length a) (f (default a))).

Definition fold {T A : Type} (f : T -> A -> A) (a : array T) (x0 : A) :=
  ifold (fun i acc => f a.[i] acc) (length a) x0.

Definition foldi {T A : Type} (f : int -> T -> A -> A) (a : array T) (x0 : A) :=
  ifold (fun i acc => f i a.[i] acc) (length a) x0.

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

Definition for_all2 {T1 T2 : Type} (f : T1 -> T2 -> bool) (a : array T1) (b : array T2) :=
  fold2 (fun x y acc => acc && f x y) a b true.

Definition for_all {T : Type} (f : T -> bool) (a : array T) :=
  fold (fun x acc => acc && f x) a true.

Definition for_all_alt {T : Type} (f_in f_notin : T -> bool) (s : array T) (notin : array int) :=
  fold_alt (fun x acc => f_in x && acc) (fun x acc => f_notin x && acc) s notin true.

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

Definition countOccurences {T: Type} (eqT : T -> T -> bool) (a : array T) (x : T) : int :=
  fold (fun y acc => if eqT x y then (acc + 1)%uint63 else acc) a 0%uint63.

Definition isUnique {T : Type} (eqT : T -> T -> bool) (a : array T) (x : T) : bool := 
  ((countOccurences eqT a x) <=? 1)%uint63.

(* For more efficiency, we could iterate through a, count and store the number of occurences of
each element in a dictionary. *)

Definition isDuplicateFree {T : Type} (eqT : T -> T -> bool) (a : array T) : bool := 
  for_all (isUnique eqT a) a.

Definition inRange {T : Type} (leT : T -> T -> bool) (m M : T) (x : T) : bool :=
  (leT m x) && (leT x M).

Definition allInRange {T : Type} (leT : T -> T -> bool) (m M : T) (a : array T) : bool :=
  for_all (inRange leT m M) a.

Definition hasLength {T : Type} (k : int) (a : array T) : bool :=
  (length a =? k)%uint63.

Definition isEmpty {T : Type} (a : array T) : bool :=
  hasLength 0%uint63 a.

Definition proj1 {A B : Type} (a : array (A*B)) : array A :=
  map (fun c => fst c) a.

Definition proj2 {A B : Type} (a : array (A*B)) : array B :=
  map (fun c => snd c) a.

Definition eqbArray {T : Type} (eqT : T -> T -> bool) (a b : array T) : bool :=
  for_all2 eqT a b.

Definition areComposableSimpleArray {T : Type} (a : array int) (b : array T) : bool :=
  for_all (inRange Uint63.leb 0%uint63 (length b - 1)%uint63) a.

Definition areComposablePairArray {T : Type} (a : array (int*int)) (b : array (array T)) : bool :=
  for_all (fun c => (inRange Uint63.leb 0%uint63 (length b - 1)%uint63 (fst c)) &&
  (inRange Uint63.leb 0%uint63 (length b.[fst c] - 1)%uint63 (snd c))) a.

Definition areComposableMatrix {T : Type} (a : array (array int)) (b : array T) : bool :=
  for_all (fun l => for_all (fun j => inRange Uint63.leb 0%uint63 ((length b-1)%uint63) j) l) a.

(* The function is not defined for all a and b and must be used together with areComposableSimpleArray. *)
Definition composeSimpleArray {T : Type} (a : array int) (b : array T) : array T :=
  map (fun x => b.[x]) a.

(* The functioj*) 
Definition isInverseSimpleArray (a : array int) (b: array int) :=
  (areComposableSimpleArray a b) && for_alli (fun i _ => (b.[a.[i]] =? i)%uint63) a.

Definition isInversePairArray (a : array (int*int)) (b : array (array int)) : bool :=
  (areComposablePairArray a b) && (for_alli (fun i _ => (b.[fst a.[i]].[snd a.[i]] =? i)%uint63) a).

Definition isInverseMatrix (a : array (array int)) (b : array (int*int)) : bool :=
  (areComposableMatrix a b) && (for_alli (fun i _ => for_alli (fun j _ => (fst (b.[a.[i].[j]]) =? i)%uint63 && 
  (snd (b.[a.[i].[j]]) =? j)%uint63) a.[i]) a).

End Array.

Definition Graph := array (array int).

Section Graph.

Definition isVertex (g : Graph) (x : int) :=
  inRange (Uint63.leb) 0%uint63 (((length g) - 1)%uint63) x. 

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


Definition array_bigZ_dot (x y : array bigZ) : bigZ :=
  fold2 (fun x y res=> BigZ.add res (BigZ.mul x y)) x y 0%bigZ.

Definition check_ineqs (ineqs : array (array bigZ * bigZ)) (saturated : array int) (x : array bigZ * bigN) :=
  for_all_alt 
    (fun ineq => (array_bigZ_dot ineq.1 x.1 =? BigZ.mul ineq.2 (BigZ.Pos x.2))%bigZ)
    (fun ineq => (array_bigZ_dot ineq.1 x.1 <? BigZ.mul ineq.2 (BigZ.Pos x.2))%bigZ)
    ineqs saturated.

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

Record Certificate := {
  ineqs : array (array bigZ * bigZ);
  vert : array (array int * (array bigZ * bigN * array (array int * int)));
  graph : Graph;
  lbl : array (array int * (int * int));
  root : int * (array int * (array (array bigQ) * array int))
}.

Definition build_cert cert := 
  let ineqs := cert.1 in 
  let vert := cert.2.1 in
  let graph := cert.2.2.1.1 in
  let lbl := cert.2.2.1.2 in
  let root := cert.2.2.2 in
  {| ineqs := ineqs; vert := vert; graph := graph; lbl := lbl; root := root |}.

Definition areActiveSetsWellConstructed (cert : Certificate) :=
  let m := length (ineqs cert) in
  let vert := vert cert in
  let activeSets := proj1 vert in
  (for_all (isDuplicateFree Uint63.eqb) activeSets) && 
  (for_all (allInRange Uint63.leb (0%uint63) (m-1)%uint63) activeSets).

Definition areFacetSetsLocallyWellConstructed (activeSet : array int) (facetSet : array (array int)) :=
  let l := length activeSet in 
  (for_all (isDuplicateFree Uint63.eqb) facetSet) &&
  (for_all (allInRange Uint63.leb (0%uint63) (l-1)%uint63) facetSet).

Definition areFacetSetsWellConstructed (cert : Certificate) :=
  let vert := vert cert in
  let facetSets := map proj1 (proj2 (proj2 vert)) in
  for_alli (fun i x => areFacetSetsLocallyWellConstructed ((proj1 vert).[i]) x) facetSets. (* pas besoin de for_alli *)

Definition isLocalFacetIndexingWellConstructed (cert : Certificate) :=
  let vert := vert cert in
  let indexFacets := map (proj2) (proj2 (proj2 vert)) in
  let nbFacets := length (lbl cert) in
  for_all (allInRange Uint63.leb (0%uint63) (nbFacets - 1)%uint63) indexFacets.

(* The bijection between the facets appearing in the abstract triangulations of the normal cones
   and the set of facets represented by lbl ensures that the facets appearing in both structures
   are exactly the same, up to a local renumbering induced by the activation sets.
   The previous functions are sufficient to verify that the facets appearing in the labels
   are well-constructed (no duplicates and in the right range). *)
Definition isFacetLabelingWellConstructed (cert : Certificate) :=
  let vert := vert cert in
  let labels :=  proj2 (lbl cert) in 
  let nbSamples := length vert in
  for_all (fun x => (inRange (Uint63.leb) (0%uint63) (nbSamples-1)%uint63 (fst x)) && 
  (inRange (Uint63.leb) (0%uint63) (length ((proj2 (proj2 vert)).[fst x])-1)%uint63 (snd x))) labels.

Definition isGraphWellConstructed (cert : Certificate) :=
  let graph := graph cert in
  let nbFacets := length (lbl cert) in
  (length graph =? nbFacets)%uint63 && (for_all (fun l => for_all (isVertex graph) l) graph).  
  
Definition areActiveSetsUnique (cert : Certificate) :=
  let vert := vert cert in
  let activeSets := proj1 vert in
  isDuplicateFree (eqbArray Uint63.eqb) activeSets.

Definition areFacetsLocallyUnique (cert : Certificate) :=
  let vert := vert cert in
  let facetSets := map proj1 (proj2 (proj2 vert)) in
  for_all (isDuplicateFree (eqbArray Uint63.eqb)) facetSets.

Definition areFacetsUnique (cert : Certificate) :=
  let facets := proj1 (lbl cert) in
  isDuplicateFree (eqbArray Uint63.eqb) facets. 

Definition isUndirectedSimpleGraph (cert : Certificate) :=
  let graph := graph cert in
  (isUndirected graph) && (isSimpleGraph graph).

Definition allFacetsHaveCardinality (cert : Certificate) :=
  let facets := proj1 (lbl cert) in
  let d := length (fst (ineqs cert).[0]) in
  for_all (hasLength d) facets.

Definition isGraphDRegular (cert : Certificate) :=
  let graph := graph cert in
  let d := length (fst (ineqs cert).[0]) in
  isRegular graph d.

Definition isFacetLabelingBijective (cert : Certificate) :=
  let vert := vert cert in
  let indexFacets := map (proj2) (proj2 (proj2 vert))  in
  let labels :=  proj2 (lbl cert) in
  (isInverseMatrix (indexFacets) (labels)) && (isInversePairArray (labels) (indexFacets)).

Definition isFacetIndexingBijective (cert : Certificate) :=
  let vert := vert cert in
  let activeSets := proj1 vert in
  let labels :=  proj2 (lbl cert) in
  let facets := proj1 (lbl cert) in
  let localFacetSets := map proj1 (proj2 (proj2 vert)) in
  for_alli (fun i s => eqbArray (Uint63.eqb) s (composeSimpleArray (activeSets.[fst labels.[i]]) 
  (localFacetSets.[fst labels.[i]].[snd labels.[i]]))) facets.

Definition feasibility_check (cert : Certificate) := 
  let ineqs := cert.(ineqs) in
  let vertices := cert.(vert) in
  ifold (fun i acc => acc && check_ineqs ineqs vertices.[i].1 vertices.[i].2.1) 
    (length vertices) true.

Definition adjacency_check (cert : Certificate) :=
  let graph := graph cert in
  let facets := proj1 (lbl cert) in
  for_alli (fun i x => for_alli (fun k y => for_all (fun s => (s =? facets.[i].[k])%uint63 || (mem Uint63.eqb facets.[y] s)) facets.[i]) x) graph.

Time LoadData "../lrs-postprocess/data/poly20dim21-cert.bin" As cert.

Section Benchmark.

Let cert := build_cert cert.
Time Eval vm_compute in 
  feasibility_check cert.

End Benchmark.
