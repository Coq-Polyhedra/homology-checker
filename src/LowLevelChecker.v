From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Printf.
From Coq Require Import Uint63 BinNat.
From mathcomp Require Import all_ssreflect.
From Bignums Require Import BigQ.
From BinReader Require Import BinReader.
Require Import PArray.
Require Import Coq.Program.Basics.
Require Import NArith.
Import Order.Theory.

Section Uint63.

Fixpoint ifold_ {T : Type} (n : nat) (f : int -> T -> T) (i M : int) (stopCondition : int -> T -> bool) (x : T) :=
  if (i =? M)%uint63 || (stopCondition i x) then (i, x) else
    if n is n.+1 then
      let: (i, x) := ((i + 1)%uint63, f i x) in
      let: (i, x) := ifold_ n f i M stopCondition x in
      let: (i, x) := ifold_ n f i M stopCondition x in
      (i, x)
    else (i, x).

Definition ifold {T : Type} (f : int -> T -> T) (i : int) (x : T) :=
  (ifold_ Uint63.size f 0 i (fun _ _ => false) x).2.  

Definition ifold_from_until {T : Type} (f : int -> T -> T) (k : int) (i : int) (stopCondition: int -> T -> bool) (x : T) :=
  (ifold_ Uint63.size f k i stopCondition x).2.

End Uint63.

Section Array.

Definition fold {T A : Type} (f : T -> A -> A) (a : array T) (x0 : A) :=
  ifold (fun i acc => f a.[i] acc) (length a) x0.

Definition foldi {T A : Type} (f : int -> T -> A -> A) (a : array T) (x0 : A) :=
  ifold (fun i acc => f i a.[i] acc) (length a) x0.

Definition fold_from_until {T A : Type} (f : T -> A -> A) (a : array T) (k : int) (stopCondition : int -> A -> bool) (x0 : A) :=
  ifold_from_until (fun i acc => f a.[i] acc) k (length a) stopCondition x0.

Definition foldi_from_until {T A : Type} (f : int -> T -> A -> A) (a : array T) (k : int) (stopCondition : int -> A -> bool) (x0 : A) :=
  ifold_from_until (fun i acc => f i a.[i] acc) k (length a) stopCondition x0.
 
Definition fold_compose {A B C : Type} (f : B -> C -> C) (g : A -> B) (a : array A) (x0 : C) :=
  fold (compose f g) a x0.

Definition foldi_compose {A B C : Type} (f : int -> B -> C -> C) (g : A -> B) (a : array A) (x0 : C) :=
  foldi (fun i => compose (f i) g) a x0.

Definition fold2 {T1 T2 A : Type} (f : T1 -> T2 -> A -> A) (a1 : array T1) (a2 : array T2) (x0 : A) :=
  ifold (fun i acc => f a1.[i] a2.[i] acc) (if (length a1 <? length a2)%uint63 then length a1 else length a2) x0.

Definition fold3 {T1 T2 T3 A : Type} (f : T1 -> T2 -> T3 -> A -> A) (a1 : array T1) (a2 : array T2) (a3 : array T3) (x0 : A) :=
  ifold (fun i acc => f a1.[i] a2.[i] a3.[i] acc) 
  (if (length a1 <? length a3)%uint63 then 
    if (length a1 <? length a2)%uint63 then length a1 else length a2
    else 
      if (length a2 <? length a3)%uint63 then length a2 else
      length a3
  )    
  x0.

Definition fold_alt {T A : Type} (f_in f_notin : T -> A -> A) (s : array T) (notin : array int) (x : A) :=
  let res := foldi (fun i x acc =>
    if (acc.2 <? length notin)%uint63 ==> (i <? notin.[acc.2])%uint63 then 
      (f_notin x acc.1, acc.2) 
      else (f_in x acc.1, (acc.2+1)%uint63)
    ) s (x, 0%uint63) in
    res.1.

Definition for_all {T : Type} (f : T -> bool) (a : array T) :=
  fold (fun x acc => acc && f x) a true.

Definition for_alli {T : Type} (f : int -> T -> bool) (a : array T) :=
  foldi (fun i x acc => acc && f i x) a true.

Definition for_all2 {T1 T2 : Type} (f : T1 -> T2 -> bool) (a : array T1) (b : array T2) :=
  fold2 (fun x y acc => acc && f x y) a b true.

Definition for_all_matrix {T : Type} (f : T -> bool) (a : array (array T)) : bool :=
  for_all (for_all f) a.

Definition for_alli_matrix {T : Type} (f : int -> int -> T -> bool) (a : array (array T)) : bool :=
  for_alli (fun i _ => for_alli (f i) a.[i]) a.

Definition for_all_compose {A B : Type} (f : B -> bool) (g : A -> B) (a : array A) :=
  fold_compose (fun x acc => acc && f x) g a true.

Definition for_alli_compose {A B : Type} (f : int -> B -> bool) (g : A -> B) (a : array A) :=
  foldi_compose (fun i x acc => acc && (f i x)) g a true.

Definition for_all_alt {T : Type} (f_in f_notin : T -> bool) (s : array T) (notin : array int) :=
  fold_alt (fun x acc => f_in x && acc) (fun x acc => f_notin x && acc) s notin true.

Definition exist {T : Type} (f : T -> bool) (a : array T) :=
  fold_from_until (fun x acc => acc || f x) a 0 (fun _ acc => acc) false.

Definition existi {T : Type} (f : int -> T -> bool) (a : array T) :=
  foldi_from_until (fun i x acc => acc || f i x) a 0 (fun _ acc => acc) false.

Definition mem {T : Type} (eqT : T -> T -> bool) (a : array T) (x : T) : bool :=
  exist (fun y => eqT x y) a.

Definition mem_sorted {T : Type} (ltT : T -> T -> bool)(a : array T) (x : T) : bool :=
  let len := length a in

  let step :=
    fun '(lo, hi, found) =>
      if found then (lo, hi, found)
      else if (lo <? hi)%uint63 then
        let mid := (lo + ((hi - lo) / 2))%uint63 in
        let y := a.[mid] in
        if (ltT x y) then
          (lo, mid, false)
        else if (ltT y x) then
          ((mid + 1)%uint63, hi, false)
        else
          (lo, hi, true)
      else
        (lo, hi, found)
  in

  let stop :=
    fun _ '(lo, hi, found) =>
      found || negb (lo <? hi)%uint63
  in

  (ifold_from_until (fun _ st => step st)0%uint63 len
     stop
     (0%uint63, len, false)).2.

Definition find_from_until {T : Type} (eqT : T -> T -> bool) (a : array T) (x : T) (k : int) : option int :=
  foldi_from_until (fun i _ acc => if (eqT x a.[i]) then Some(i) else None) a k (fun i x => (if x is Some _ then true else false)) None. 

Definition subset {t : Type} (lt_t : rel t) (a b : array t) : bool :=
  let subset_step :=
    fun _ '(i, j, ok) =>
      if (i <? length a)%uint63 then
        if (j <? length b)%uint63 then
          if lt_t a.[i] b.[j] then
            (* a[i] < b[j], so a[i] is missing from b *)
            (i, j, false)
          else if lt_t b.[j] a.[i] then
            (* b[j] < a[i], advance in b *)
            (i, (j + 1)%uint63, true)
          else
            (* a[i] = b[j] *)
            ((i + 1)%uint63, (j + 1)%uint63, true)
        else
          (* b exhausted while a still has elements *)
          (i, j, false)
      else
        (* all elements of a have been matched *)
        (i, j, true)
  in
  let res :=
    ifold (*_until
      (length a + length b)%uint63
      (fun _ '(i, _, ok) =>
         ~~ ok || ~~ (i <? length a)%uint63)*)
      subset_step
      (length a + length b)%uint63
      (0%uint63, 0%uint63, true)
  in
  res.2.
  
Definition diff {t : Type} (lt_t : rel t) (a b : array t) : seq t :=
  let diff_step :=
    fun '(i, j, acc) =>
      if (i <? length a)%uint63 then
        if (j <? length b)%uint63 then
          if lt_t a.[i] b.[j] then
            ((i+1)%uint63, j, a.[i] :: acc)
          else if lt_t b.[j] a.[i] then
            (i, (j+1)%uint63, acc)
          else
            ((i+1)%uint63, (j+1)%uint63, acc)
        else
          ((i+1)%uint63, j, a.[i] :: acc)
      else
        (i, j, acc)
    in
    (ifold
      (fun _ ijacc => diff_step ijacc)
      (length a + length b)%uint63
      (0%uint63, 0%uint63, [::])).2.

Definition count {T : Type} (P : T -> bool) (a : array T) :=
  fold (fun x acc => if P x then (acc + 1)%uint63 else acc) a 0%uint63.

Definition counti {T : Type} (P : int -> T -> bool) (a : array T) :=
  foldi (fun i x acc => if P i x then (acc + 1)%uint63 else acc) a 0%uint63.

Definition eqbArray {T : Type} (eqT : T -> T -> bool) (a b : array T) : bool :=
  for_all2 eqT a b.

Definition lex_cmp {T : Type} (ltT : T -> T -> bool) (a b : array T) : comparison :=
  let c :=
    fold2
      (fun x y acc =>
         match acc with
         | Lt => Lt
         | Gt => Gt
         | Eq =>
             if ltT x y then Lt
             else if ltT y x then Gt
             else Eq
         end)
      a b Eq
  in
  match c with
  | Lt => Lt
  | Gt => Gt
  | Eq =>
      if (length a <? length b)%uint63 then Lt
      else if (length b <? length a)%uint63 then Gt
      else Eq
  end.

Definition ltbArray {T : Type} (eqT : T -> T -> bool) (ltT : T -> T -> bool) (a b : array T) : bool :=
  if lex_cmp ltT a b is Lt then true else false.

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

Definition isValidIndex {T : Type} (a : array T) (x : int) : bool :=
  inRange Uint63.leb 0%uint63 (length a - 1)%uint63 x.

End Array.

Section IntList.

(* in this section, lists are supposed to be sorted decreasingly *)
Fixpoint not_subset (a b : seq int) : bool :=
  match a, b with
  | [::], _ => false
  | _, [::] => true
  | x :: a', y :: b' =>
      if (x =? y)%uint63 then
        not_subset a' b'
      else if (x <? y)%uint63 then
        (* [y > x], so advance in [b]. *)
        not_subset a b'
      else
        (* [x > y], hence x is absent from [b]. *)
        true
  end.

Definition incomparable (a b : seq int) : bool :=
  not_subset a b && not_subset b a.

Fixpoint incomparable_with_all
  (d : seq int)
  (ds : seq (seq int)) : bool :=
  match ds with
  | [::] => true
  | e :: ds' =>
      incomparable d e
      && incomparable_with_all d ds'
  end.

Fixpoint pairwise_incomparable
  (ds : seq (seq int)) : bool :=
  match ds with
  | [::] => true
  | d :: ds' =>
      incomparable_with_all d ds'
      && pairwise_incomparable ds'
  end.

End IntList.

Section Queue.

Context {T : Type}.

Record queue := Queue { front : seq T; back : seq T; }.

Implicit Types (q : queue) (x : T) (xs : seq T).

Definition empty := Queue [::] [::].

Definition enqueue q x :=
  Queue q.(front) (x :: q.(back)).

Definition pull q :=
  if q is Queue [::] back
  then Queue (rev back) [::] 
  else q.

Definition dequeue q :=
  if pull q is Queue (x :: front) back
  then Some (x, Queue front back)
  else None.

End Queue.

Section Graph.

Definition Graph := array (array int).

Definition isVertex (g : Graph) (x : int) :=
  isValidIndex g x. 

(* The function is not defined for all x and must be used together with isVertex. *)
Definition isLocallyUndirected (g : Graph) (x : int) :=
  for_all (fun y => mem (Uint63.eqb) g.[y] x) g.[x].

Definition isUndirected (g : Graph) :=
  for_alli (fun i _ => isLocallyUndirected g i) g. 

Definition hasSimpleEdges (g : Graph) := 
  for_all (isStrictlySorted Uint63.ltb) g.

Definition hasLocallyNoLoop (g : Graph) (x : int) :=
  negb (mem (Uint63.eqb) g.[x] x).

Definition hasNoLoops (g : Graph) :=
  for_alli (fun i _ => hasLocallyNoLoop g i) g.

Definition isSimpleGraph (g : Graph) :=
  (hasSimpleEdges g) && (hasNoLoops g).

Definition hasBoundedDegree (g : Graph) (k : int) := 
  for_all (fun x => ((length x) <=? k)%uint63) g.

End Graph.

Section BFS.

Arguments queue T : clear implicits.
Arguments empty T : clear implicits.

Definition bfsqueue := queue (int * N)%type.
Definition marks := array bool.

Record state := State {
  nb_visited : int;
  visited : marks;
  to_visit : bfsqueue;
}.

Definition init_state (n : int) (y : int) :=
  {| nb_visited  := 1%uint63;
      visited  := (PArray.make n false).[y <- true]; 
      to_visit    := empty _; |}.

Definition mark_vertex (st : state) (y : int) (k : N) :=
  if st.(visited).[y] then st else
    {| nb_visited := (st.(nb_visited)+1)%uint63;
        visited := st.(visited).[y <- true]; 
        to_visit := enqueue st.(to_visit) (y, k); |}.

Definition bfs_dequeue (st : state) :=
  if dequeue st.(to_visit) is Some ((y, k), q) then
    let st := {|
      nb_visited := st.(nb_visited);
      visited := st.(visited);
      to_visit   := q;
    |} in Some (st, y, k)
  else None.

Definition bfs_step (g : Graph) (st : state * int * N) :=
  let: (st, x, k) := st in
  let: st :=
    fold (fun y acc => mark_vertex acc y (N.succ k)) g.[x] st
  in
  match bfs_dequeue st with
  | Some st => inl st
  | None    => inr st
  end.

Definition bfs_ (g : Graph) (x : int) :=
  let out := bfs_step g (init_state (length g) x, x, 0%N) in
  let out := ifold_from_until (fun _ out => if out is inl s then bfs_step g s else out)
  0%uint63 (length g)%uint63 (fun _ out => if out is inr _ then true else false) out
  in if out is inr v then Some v else None.

(* This function returns the number of vertices visited by a BFS starting 
from vertex 0 in an undirected graph. *)
Definition bfs (g : Graph) (x : int) :=
  odflt 0%uint63 (omap (fun x => x.(nb_visited)) (bfs_ g x)).

Definition isConnected (g : Graph) :=
  if (length g =? 0)%uint63 then true else (bfs g (0%uint63) =? length g)%uint63.

End BFS.

Section BigZ.

Definition array_bigZ_dot (x y : array bigZ) : bigZ :=
  fold2 (fun x y res=> BigZ.add res (BigZ.mul x y)) x y 0%bigZ.

Definition sparse_array_bigZ_dot (a : array (int * bigZ)) (b : array bigZ) : bigZ :=
  fold (fun x acc => BigZ.add acc (BigZ.mul b.[x.1] x.2)) a 0%bigZ.

Definition array_bigZ_add_dot (x y z : array bigZ) : bigZ :=
  fold3 (fun x y z res=> BigZ.add res (BigZ.mul x (BigZ.add y z))) x y z 0%bigZ.

End BigZ.

Section Types.

Definition Bound := bigZ.
Definition Normal := array bigZ.
Definition Inequality := (Normal * Bound)%type.
Definition Inequalities := array Inequality.

Definition CommonDenominator := bigN. 
Definition Numerators := array bigZ. 
Definition Point := (Numerators * CommonDenominator)%type.
Definition ActiveSet := array int.
Definition Vertex := (ActiveSet * Point)%type.
Definition Vertices := array Vertex.

Definition Mapping := int.
Definition Description := array int. 
Definition Facet := (Description * Mapping)%type.
Definition Facets := array Facet.

Definition SimplexIndex := int.
Definition ActiveInverse := array int.
Definition Witness := array bigZ.
Definition Witnesses := array Witness.
Definition ScalarProducts := array (array bigZ).
Definition Weight := array (int * bigZ). (* sparse representation *)
Definition Weights := array Weight.
Definition FullDim := (Point * (array (array bigZ) * array (array bigZ)))%type.
Definition Root := (SimplexIndex * (ActiveInverse * (Witnesses * (ScalarProducts * Weights))))%type. 

Record Certificate := {
  nb_inequalities : int;
  dimension : int;
  inequalities : Inequalities;
  vertices : Vertices;
  graph : Graph;
  facets : Facets;
  geom_graph : Graph;
  geom_edge_sources : array (array int);
  geom_edge_local_targets : array (array int);
  full_dim : FullDim;
  root : Root
}.

End Types.

Section Projectors.

Definition normal : Inequality -> Normal := fst.
Definition bound : Inequality -> Bound := snd.
Definition numerators : Point -> Numerators := fst.
Definition commonDenominator : Point -> CommonDenominator := snd.
Definition activeSet : Vertex -> ActiveSet := fst.
Definition point : Vertex -> Point := snd.
Definition description : Facet -> Description := fst.
Definition mapping : Facet -> Mapping := snd.
Definition simplexIndex : Root -> SimplexIndex := fst.
Definition activeInverse : Root -> ActiveInverse := compose fst snd.
Definition witnesses : Root -> Witnesses := compose (compose fst snd) snd.
Definition scalarProducts : Root -> ScalarProducts := compose (compose (compose fst snd) snd) snd.
Definition weights : Root -> Weights := compose (compose (compose snd snd) snd) snd.
Definition fullDimPoint : FullDim -> Point := fst.
Definition fullDimDir : FullDim -> array (array bigZ) := compose fst snd.
Definition fullDimInverse : FullDim -> array (array bigZ) := compose snd snd.

End Projectors.

Definition areInequalitiesWellFormed (cert : Certificate) :=
  let inequalities := inequalities cert in
  (nb_inequalities cert =? length inequalities)%uint63
  && (for_all_compose (hasLength (dimension cert)) normal inequalities)
  && (for_all_compose (exist (fun x => ~~(x =? 0)%bigZ)) normal inequalities).

Definition arePointsWellFormed (cert : Certificate) :=
  let vertices := vertices cert in
  (for_all_compose (fun x => ~~(x =? 0)%bigN) (compose commonDenominator point) vertices)
  && (for_all_compose (hasLength (dimension cert)) (compose numerators point) vertices).

Definition areActiveSetsWellFormed (cert : Certificate) :=
  let m := nb_inequalities cert in
  let vertices := vertices cert in
  (for_all_compose (isStrictlySorted Uint63.ltb) activeSet vertices)
  && (for_all_compose (allInRange Uint63.leb (0%uint63) (m-1)%uint63) activeSet vertices).

Definition areVerticesWellFormed (cert : Certificate) :=
  (arePointsWellFormed cert)
  && (areActiveSetsWellFormed cert).
  
Definition isGraphWellFormed (cert : Certificate) :=
  let graph := graph cert in
  let nbFacets := length (facets cert) in
  (length graph =? nbFacets)%uint63 
  && (for_all_matrix (isVertex graph) graph) (* perhaps we could replace this condition by 
                                              * for_all_matrix 
                                                (allInRange Uint63.leb (0%uint63) ((length graph)-1)%uint63) 
                                                graph
                                              * more explicitely *)
  && (hasNoLoops graph) 
  && (isUndirected graph).

Definition areDescriptionsWellFormed (cert : Certificate) :=
  let m := nb_inequalities cert in
  let d := dimension cert in 
  let facets := facets cert in
  (for_all_compose (isStrictlySorted Uint63.ltb) description facets)
  && (for_all_compose (allInRange Uint63.leb (0%uint63) (m-1)%uint63) description facets)
  && (for_all_compose (hasLength d) description facets).

Definition isMappingWellFormed (cert : Certificate) :=
  let nbVertices := length (vertices cert) in
  let facets := facets cert in
  for_all_compose (inRange Uint63.leb (0%uint63) (nbVertices-1)%uint63) mapping facets.

Definition areFacetsWellFormed (cert : Certificate) :=
  (areDescriptionsWellFormed cert)
  && (isMappingWellFormed cert).

Definition isGeomGraphWellFormed (cert : Certificate) :=
  let geom_graph := geom_graph cert in
  let nbVertices := length (vertices cert) in
  (length geom_graph =? nbVertices)%uint63 
  && (for_all_matrix (isVertex geom_graph) geom_graph) (* see remark above *)
  && (isSimpleGraph geom_graph)
  && (isUndirected geom_graph). (* the undirectness should be a consequence of graph_image_check below *)

Definition areGeomEdgeSourcesWellFormed (cert : Certificate) :=
  let geom_graph := geom_graph cert in
  let geom_edge_sources := geom_edge_sources cert in
  let nbVertices := length (vertices cert) in
  let nbFacets := length (facets cert) in
  (length geom_edge_sources =? nbVertices)%uint63 
  && for_alli (fun i l => hasLength (length geom_graph.[i]) l) geom_edge_sources
  && for_all (allInRange Uint63.leb (0%uint63) (nbFacets-1)%uint63) geom_edge_sources.

Definition areGeomEdgeLocalTargetsWellFormed (cert : Certificate) :=
  let graph := graph cert in
  let geom_graph := geom_graph cert in
  let geom_edge_local_targets := geom_edge_local_targets cert in
  let geom_edge_sources := geom_edge_sources cert in
  let nbVertices := length (vertices cert) in
  (length geom_edge_local_targets =? nbVertices)%uint63
  && for_alli (fun i l => hasLength (length geom_graph.[i]) l) geom_edge_local_targets
  && for_alli_matrix (fun i j v => inRange Uint63.leb (0%uint63) 
  (length(graph.[geom_edge_sources.[i].[j]])-1)%uint63 v) geom_edge_local_targets.

Definition isFullDimPointWellFormed (cert : Certificate) :=
  let fullDimPoint := fullDimPoint (full_dim cert) in
  (~~(commonDenominator fullDimPoint =? 0)%bigN)
  && (hasLength (dimension cert) (numerators fullDimPoint)).

Definition isFullDimDirWellFormed (cert : Certificate) :=
  let fullDimDir := fullDimDir (full_dim cert) in
  (hasLength (dimension cert) fullDimDir)
  && (for_all (hasLength (dimension cert)) fullDimDir).

Definition isFullDimInverseWellFormed (cert : Certificate) :=
  let fullDimInverse := fullDimInverse (full_dim cert) in
  (hasLength (dimension cert) fullDimInverse)
  && (for_all (hasLength (dimension cert)) fullDimInverse).

Definition isFullDimWellFormed (cert : Certificate) :=
  (isFullDimPointWellFormed cert)
  && (isFullDimDirWellFormed cert)
  && (isFullDimInverseWellFormed cert).

Definition isSimplexIndexWellFormed (cert : Certificate) :=
  let root := root cert in
  let nbFacets := length (facets cert) in
  inRange Uint63.leb (0%uint63) (nbFacets-1)%uint63 (simplexIndex root).

Definition isActiveInverseWellFormed (cert : Certificate) :=
  let activeInverse := activeInverse (root cert) in
  let vertices := vertices cert in
  let vstar := mapping (facets cert).[simplexIndex (root cert)] in
  (length activeInverse =? nb_inequalities cert)%uint63
  && for_alli (fun i k => (activeInverse.[k] =? i)%uint63) (activeSet vertices.[vstar]).

(* witnesses = vectors f_j *)
Definition areWitnessesWellFormed (cert : Certificate) :=
  let d := dimension cert in 
  let witnesses := (witnesses (root cert)) in
  (length witnesses =? d)%uint63 
  && (for_all (hasLength d) witnesses).

Definition areScalarProductsWellFormed (cert : Certificate) :=
  let d := dimension cert in
  let facets := facets cert in
  let scalarProducts := (scalarProducts (root cert)) in
  let simplexIndex := (simplexIndex (root cert)) in
  let vertices := vertices cert in
  (length scalarProducts =? length (activeSet vertices.[mapping facets.[simplexIndex]]))%uint63
  && (for_all (hasLength d) scalarProducts).

Definition isSparseVectorWellFormed d (w : Weight) :=
  for_all (fun '(i,_) => inRange Uint63.leb (0%uint63) (d-1)%uint63 i) w (* this test can be replace by 
                                                                          * w.[length w - 1] < d
                                                                          * if need be *)
  && isStrictlySorted (fun '(i,_) '(j, _) => (i <? j)%uint63) w
  && for_all (fun '(_, x) => ~~ (0 =? x)%bigZ) w.

Definition areWeightsWellFormed (cert : Certificate) :=
  let d := dimension cert in 
  let weights := weights (root cert) in
  let simplexIndex := simplexIndex (root cert) in
  let facets := facets cert in
  let n := counti (fun i x => ~~(i =? simplexIndex)%uint63 && (mapping x =? 
  mapping facets.[simplexIndex])%uint63) facets in
  (length weights =? n)%uint63 
  && for_all (isSparseVectorWellFormed d) weights.

Definition isRootWellFormed (cert : Certificate) :=
  (isSimplexIndexWellFormed cert)
  && (isActiveInverseWellFormed cert)
  && (areWitnessesWellFormed cert)
  && (areScalarProductsWellFormed cert)
  && (areWeightsWellFormed cert).
  
Definition areActiveSetsUnique (cert : Certificate) :=
  let vertices := vertices cert in
  isStrictlySorted (fun vertex1 vertex2 => (ltbArray Uint63.eqb Uint63.ltb) (activeSet vertex1) (activeSet vertex2)) vertices.

Definition areFacetsUnique (cert : Certificate) :=
  let facets := facets cert in
  isStrictlySorted (fun f1 f2 => (ltbArray Uint63.eqb Uint63.ltb) (description f1) (description f2)) facets.

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

(* Check if s1 \ s2 = v *)
Definition isRidgeInFacet (s1 s2 : array int) (v : int) :=
  match diff Uint63.ltb s1 s2 with
  | [:: x] => (x =? v)%uint63
  | _ => false
  end.
  
Definition graph_check (cert : Certificate) :=
  let graph := graph cert in
  let facets := facets cert in
  let d := dimension cert in
  (hasBoundedDegree graph d) &&  
  for_alli_matrix (fun i j v => isRidgeInFacet (description (facets.[i])) (description (facets.[v]))
  (description (facets.[i])).[j]) graph.

Definition mapping_check (cert : Certificate) :=
  let facets := facets cert in
  let vertices := vertices cert in
  for_all (fun f => subset Uint63.ltb f.1 (activeSet vertices.[f.2])) facets.

Definition scalarProducts_check (cert : Certificate) :=
  let inequalities := inequalities cert in
  let vertices := vertices cert in
  let witnesses := witnesses (root cert) in
  let scalarProducts := scalarProducts (root cert) in
  let vstar := mapping (facets cert).[simplexIndex (root cert)] in 
  for_alli_matrix (fun i j x => (x =? array_bigZ_dot (normal 
  (inequalities.[(activeSet vertices.[vstar]).[i]])) witnesses.[j])%bigZ) scalarProducts.

Definition inversibility_check (cert : Certificate) :=
  let d := dimension cert in
  let activeInverse := activeInverse (root cert) in
  let scalarProducts := scalarProducts (root cert) in 
  let vstar := description (facets cert).[simplexIndex (root cert)] in 
  ifold (fun i acc => acc && (ifold (fun j acc => acc && (if (i =? j)%uint63 then 
  (0 <? scalarProducts.[activeInverse.[vstar.[i]]].[j])%bigZ else 
  (0 =? scalarProducts.[activeInverse.[vstar.[i]]].[j])%bigZ)) d%uint63 true)) d%uint63 true.

Definition isSparseVectorPositive (w : Weight) :=
  (0 <? length w)%uint63 && (for_all (fun '(_,x) => (0 <=? x)%bigZ) w).

Definition separability_check (cert : Certificate) :=
  let facets := facets cert in
  let activeInverse := activeInverse (root cert) in
  let simplexIndex := simplexIndex (root cert) in
  let scalarProducts := scalarProducts (root cert) in
  let weights := weights (root cert) in
  let vstar := mapping (facets).[simplexIndex] in 
  let res := 
    foldi 
    (fun k f acc => 
      if ~~(k =? simplexIndex)%uint63 && (f.2 =? vstar)%uint63 then
        (acc.1 
        && 
        for_all 
          (fun i => 
            (isSparseVectorPositive weights.[acc.2])
            && (sparse_array_bigZ_dot weights.[acc.2] scalarProducts.[activeInverse.[i]] <=? 0)%bigZ) 
            f.1,
        (acc.2 + 1)%uint63) 
      else 
        acc) 
    facets (true, 0%uint63) in res.1.

Definition graph_image_check (cert : Certificate) :=
  let facets := facets cert in
  let graph := graph cert in
  let geom_graph := geom_graph cert in
  let geom_edge_sources := geom_edge_sources cert in
  let geom_edge_local_targets := geom_edge_local_targets cert in

  (* check graph edges are mapped to geom_graph edges *)
  for_alli_matrix (fun i _ j =>
    let src := mapping facets.[i] in
    let tgt := mapping facets.[j] in
    (src =? tgt)%uint63 || mem_sorted Uint63.ltb (geom_graph.[src]) tgt) graph
  && 
  (* check geom_graph edges are images of graph edges *)
  for_alli_matrix (fun i j v =>
    let src := geom_edge_sources.[i].[j] in
    let tgt := graph.[src].[geom_edge_local_targets.[i].[j]] in
    (i =? mapping facets.[src])%uint63 && (v =? mapping facets.[tgt])%uint63) geom_graph. 

Definition geom_edge_pairwise_check (cert : Certificate) :=
  let geom_graph := geom_graph cert in
  let vertices := vertices cert in
  for_alli (fun i v =>
    let neighbors := geom_graph.[i] in
    let diffs :=
      fold
        (fun w acc =>
           diff Uint63.ltb (activeSet v) (activeSet vertices.[w]) :: acc)
        neighbors
        [::]
    in
    all (fun d => if d is [::] then false else true) diffs (* T6 *)
    && pairwise_incomparable diffs (* T8 *))
  vertices.

Definition connectivity_check (cert : Certificate) :=
  let geom_graph := geom_graph cert in
  isConnected geom_graph.

Definition full_dim_feasibility_check (cert : Certificate) :=
  let ineqs := inequalities cert in
  let point := fullDimPoint (full_dim cert) in
  let dirs := fullDimDir (full_dim cert) in
  for_all (fun dir => 
    for_all (fun ineq => 
    (array_bigZ_add_dot (normal ineq) (numerators point) dir <=? (bound ineq) * (BigZ.Pos (commonDenominator point)))%bigZ) 
    ineqs
  ) dirs
  &&
  for_all 
    (fun ineq => (array_bigZ_dot (normal ineq) (numerators point) <=? (bound ineq) * (BigZ.Pos (commonDenominator point)))%bigZ) 
    ineqs.

Definition full_dim_inverse_check (cert : Certificate) :=
  let dirs := fullDimDir (full_dim cert) in
  let inv := fullDimInverse (full_dim cert) in
  for_alli_matrix 
    (fun i j x => 
      let x := array_bigZ_dot dirs.[i] inv.[j] in
      if (i =? j)%uint63 then ~~ (x =? 0)%bigZ else (x =? 0)%bigZ
    ) inv.

Definition full_dim_check (cert : Certificate) :=
  (full_dim_feasibility_check cert) 
  && (full_dim_inverse_check cert).

Definition well_formedness_check (cert : Certificate) :=
  (areInequalitiesWellFormed cert)
  && (areVerticesWellFormed cert)
  && (isGraphWellFormed cert)
  && (areFacetsWellFormed cert)
  && (isGeomGraphWellFormed cert)
  && (areGeomEdgeSourcesWellFormed cert)
  && (areGeomEdgeLocalTargetsWellFormed cert)
  && (isFullDimWellFormed cert)
  && (isRootWellFormed cert).

Definition well_unique_check (cert : Certificate) :=
  (areInequalitiesWellFormed cert)
  && (areVerticesWellFormed cert)
  && (isGraphWellFormed cert)
  && (areFacetsWellFormed cert)
  && (isFullDimWellFormed cert)
  && (isRootWellFormed cert)
  && (areActiveSetsUnique cert)
  && (areFacetsUnique cert).

Definition uniqueness_check (cert : Certificate) :=
  (areActiveSetsUnique cert)
  && (areFacetsUnique cert).

Definition root_check (cert : Certificate) :=
     (scalarProducts_check cert)
  && (inversibility_check cert)
  && (separability_check cert).

Definition geom_graph_check (cert : Certificate) :=
     (graph_image_check cert)
  && (geom_edge_pairwise_check cert)
  && (connectivity_check cert).

Definition check_certificate (cert : Certificate) :=
     (well_formedness_check cert)
  && (uniqueness_check cert)
  && (feasibility_check cert)
  && (graph_check cert)
  && (mapping_check cert)
  && (full_dim_check cert)
  && (root_check cert)
  && (geom_graph_check cert)
  && (full_dim_check cert).


Section Benchmark.

Definition build_cert c : Certificate :=
  let '(nb_ineq, (dim, (ineqs, (verts, ((gr,facs), ((geom_gr, (src, tgt)), (full_dim, rt))))))) := c in
  {|
    nb_inequalities := nb_ineq;
    dimension := dim;
    inequalities := ineqs;
    vertices := verts;
    graph := gr;
    facets := facs;
    geom_graph := geom_gr;
    geom_edge_sources := src;
    geom_edge_local_targets := tgt;
    full_dim := full_dim;
    root := rt
  |}.

Ltac2 Eval printf "".
Ltac2 Eval printf "Loading certificate".

(* Time LoadData "../lrs-postprocess/data/poly20dim21-cert.bin" As cert. *)
(* Time LoadData "../lrs-postprocess/data/poly23dim24-cert.bin" As cert. *)
(* Time LoadData "../lrs-postprocess/data/cross8-cert.bin" As cert. *)
(* Time LoadData "../lrs-postprocess/data/birkhoff5-cert.bin" As cert. *)
(* Time LoadData "../lrs-postprocess/data/birkhoff6-cert.bin" As cert. *)
(* Time LoadData "../lrs-postprocess/data/dual_cyclic_d13_n26-cert.bin" As cert. *)
(* Time LoadData "../lrs-postprocess/data/dual_cyclic_d14_n28-cert.bin" As cert. *)
Time LoadData "../lrs-postprocess/data/permutohedron3-cert.bin" As cert. 
(* Time LoadData "../lrs-postprocess/data/permutohedron7-cert.bin" As cert. *)
(* Time LoadData "../lrs-postprocess/data/permutohedron8-cert.bin" As cert. *)
(* Time LoadData "../lrs-postprocess/data/hypersimplex15-cert.bin" As cert. *)
(* Time LoadData "../lrs-postprocess/data/hypersimplex16-cert.bin" As cert.  *)

Let cert := build_cert cert.

(*
Ltac2 Eval printf "".
Ltac2 Eval printf "Certificate check".
Time Eval vm_compute in 
  check_certificate cert. *)


Ltac2 Eval printf "".
Ltac2 Eval printf "Uniqueness check".
Time Eval vm_compute in 
  well_unique_check cert.

Ltac2 Eval printf "".
Ltac2 Eval printf "Feasibility check".
Time Eval vm_compute in 
  feasibility_check cert.

Ltac2 Eval printf "".
Ltac2 Eval printf "Graph check".
Time Eval vm_compute in
  graph_check cert.

Ltac2 Eval printf "".
Ltac2 Eval printf "Mapping check".
Time Eval vm_compute in
  mapping_check cert.

Ltac2 Eval printf "".
Ltac2 Eval printf "Root check".
Time Eval vm_compute in
  root_check cert.

Ltac2 Eval printf "".
Ltac2 Eval printf "Geometric graph check".
Time Eval vm_compute in
  geom_graph_check cert.

Ltac2 Eval printf "".
Ltac2 Eval printf "Full dimension check".
Time Eval vm_compute in
  full_dim_check cert.

End Benchmark.