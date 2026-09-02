(* -------------------------------------------------------------------------- *)
(* Bridges between the vocabulary of the executable checker (LowLevelChecker) *)
(* and mathcomp: Uint63 <-> nat, iteration <-> folds and quantifiers,         *)
(* bigZ <-> a realFieldType, arrays <-> vectors, sorted int arrays <-> finite *)
(* sets, and the merge-based subset/difference/lexicographic tests.           *)
(*                                                                            *)
(* Every lemma has a left-hand side in the low-level vocabulary (int, array,  *)
(* bigZ, ifold, ...) and a right-hand side in the mathcomp vocabulary (nat,   *)
(* 'I_n, \sum_, ...). Nothing here mentions certificates: the interpretation  *)
(* lives in Refinement.v.                                                     *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import Uint63 PArray ZArith Lia.
From Bignums Require Import BigZ BigN.
From mathcomp Require Import all_ssreflect all_algebra.
From Polyhedra Require Import inner_product.
From Cert Require LowLevelChecker.

Module L := LowLevelChecker.

Import GRing.Theory Num.Theory Order.Theory.

(* [all_algebra] exports mathcomp's [int]; in this file [int] is always the
   primitive 63-bit integer type used by LowLevelChecker. *)
Local Notation int := PrimInt63.int.

(* ssrint re-delimits [%Z] to mathcomp's int_scope; restore Coq's Z_scope,
   for this file only. *)
#[local] Delimit Scope Z_scope with Z.

Local Open Scope array_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(* Uint63 <-> nat                                                             *)
(* -------------------------------------------------------------------------- *)

(* [nat_of_int]/[int_of_nat] are sealed behind an opaque module signature:
   if unification ever unfolds them it reaches [to_Z_rec 63] and hangs, and
   [Opaque] is not honoured by term elaboration (only by conversion-checking
   tactics). They are only ever reasoned about through [nat_of_intE]. *)
Module Type NatOfIntSig.
  Parameter nat_of_int : int -> nat.
  Parameter int_of_nat : nat -> int.
  Axiom nat_of_int_def : nat_of_int = fun i => Z.to_nat (to_Z i).
  Axiom int_of_nat_def : int_of_nat = fun n => of_Z (Z.of_nat n).
End NatOfIntSig.

Module NatOfInt : NatOfIntSig.
  Definition nat_of_int (i : int) : nat := Z.to_nat (to_Z i).
  Definition int_of_nat (n : nat) : int := of_Z (Z.of_nat n).
  Lemma nat_of_int_def : nat_of_int = fun i => Z.to_nat (to_Z i). Proof. by []. Qed.
  Lemma int_of_nat_def : int_of_nat = fun n => of_Z (Z.of_nat n). Proof. by []. Qed.
End NatOfInt.

Export NatOfInt.

Section Uint63Bridge.

Lemma nat_of_intE i : nat_of_int i = Z.to_nat (to_Z i).
Proof. by rewrite nat_of_int_def. Qed.

Lemma int_of_natE n : int_of_nat n = of_Z (Z.of_nat n).
Proof. by rewrite int_of_nat_def. Qed.

Lemma to_Z_nat_of_int i : to_Z i = Z.of_nat (nat_of_int i).
Proof. by rewrite nat_of_intE Z2Nat.id //; case: (to_Z_bounded i). Qed.

Lemma nat_of_int_ltwB i : (Z.of_nat (nat_of_int i) < wB)%Z.
Proof. by rewrite -to_Z_nat_of_int; case: (to_Z_bounded i). Qed.

Lemma int_of_natK_wB n : (Z.of_nat n < wB)%Z -> nat_of_int (int_of_nat n) = n.
Proof.
move=> hn; rewrite nat_of_intE int_of_natE of_Z_spec Z.mod_small ?Nat2Z.id //.
lia.
Qed.

(* The form actually used downstream: n is bounded by an existing int. *)
Lemma int_of_natK_le i n : n <= nat_of_int i -> nat_of_int (int_of_nat n) = n.
Proof.
move=> /ssrnat.leP hn; apply: int_of_natK_wB.
have := nat_of_int_ltwB i; lia.
Qed.

Lemma nat_of_intK : cancel nat_of_int int_of_nat.
Proof.
move=> i; rewrite int_of_natE -to_Z_nat_of_int; apply: to_Z_inj.
by rewrite of_Z_spec Z.mod_small //; apply: to_Z_bounded.
Qed.

Lemma nat_of_int_inj : injective nat_of_int.
Proof. exact: can_inj nat_of_intK. Qed.

Lemma nat_of_int0 : nat_of_int 0 = 0%N.
Proof. by rewrite nat_of_intE to_Z_0. Qed.

Lemma int_of_nat0 : int_of_nat 0 = 0%uint63.
Proof. by rewrite -nat_of_int0 nat_of_intK. Qed.

Lemma ltb_natE i j : (i <? j)%uint63 = (nat_of_int i < nat_of_int j).
Proof.
apply/idP/idP => [/Uint63.ltbP|/ssrnat.ltP] h; [apply/ssrnat.ltP|apply/Uint63.ltbP];
  by move: h; rewrite (to_Z_nat_of_int i) (to_Z_nat_of_int j); lia.
Qed.

Lemma leb_natE i j : (Uint63.leb i j) = (nat_of_int i <= nat_of_int j).
Proof.
apply/idP/idP => [/Uint63.lebP|/ssrnat.leP] h; [apply/ssrnat.leP|apply/Uint63.lebP];
  by move: h; rewrite (to_Z_nat_of_int i) (to_Z_nat_of_int j); lia.
Qed.

Lemma eqb_natE i j : (i =? j)%uint63 = (nat_of_int i == nat_of_int j).
Proof.
apply/idP/idP => [/Uint63.eqbP h | /eqP h].
  by rewrite (to_Z_inj _ _ h).
by rewrite (nat_of_int_inj h); apply/Uint63.eqbP.
Qed.

Lemma add1_natE i j : (i <? j)%uint63 -> nat_of_int (i + 1)%uint63 = (nat_of_int i).+1.
Proof.
move/Uint63.ltbP => hij; rewrite !nat_of_intE add_spec to_Z_1 Z.mod_small.
  by rewrite Z.add_1_r Z2Nat.inj_succ //; case: (to_Z_bounded i).
have := to_Z_bounded i; have := to_Z_bounded j; lia.
Qed.

End Uint63Bridge.

Lemma Nat2Z_expn n : Z.of_nat (2 ^ n) = (2 ^ Z.of_nat n)%Z.
Proof.
elim: n => [|n ih]; first by rewrite expn0.
by rewrite expnS -multE Nat2Z.inj_mul ih (Nat2Z.inj_succ n) Z.pow_succ_r //; lia.
Qed.

Lemma nat_of_int_lt_size i : nat_of_int i < 2 ^ Uint63.size.
Proof.
apply/ssrnat.ltP/Nat2Z.inj_lt; rewrite Nat2Z_expn; exact: nat_of_int_ltwB.
Qed.

Lemma sub1_natE i : 0 < nat_of_int i -> nat_of_int (i - 1)%uint63 = (nat_of_int i).-1.
Proof.
move=> hi; have [hb hwB] := to_Z_bounded i.
have h0 : (0 < to_Z i)%Z.
  by apply/(Z2Nat.inj_lt 0 _ (Z.le_refl 0) hb)/ssrnat.ltP; rewrite -nat_of_intE.
rewrite !nat_of_intE sub_spec to_Z_1 Z.mod_small; last by lia.
by rewrite Z2Nat.inj_sub //= minusE subn1.
Qed.

(* The checker encodes "x < n" as [inRange leb 0 (n - 1) x]; meaningful only
   when [0 < n] (the subtraction wraps around at n = 0). *)
Lemma inRangeP (n x : int) : (0 < nat_of_int n)%N ->
  L.inRange Uint63.leb 0%uint63 (n - 1)%uint63 x -> (nat_of_int x < nat_of_int n)%N.
Proof. by move=> hn /andP[_]; rewrite leb_natE sub1_natE // -ltnS prednK. Qed.

Lemma int_of_natS k M : k < nat_of_int M -> (int_of_nat k + 1)%uint63 = int_of_nat k.+1.
Proof.
move=> hk; have hkk : nat_of_int (int_of_nat k) = k by apply: (int_of_natK_le (i := M)); exact: ltnW.
have hlt : (int_of_nat k <? M)%uint63 by rewrite ltb_natE hkk.
by rewrite -{1}(nat_of_intK (int_of_nat k + 1)%uint63) (add1_natE hlt) hkk.
Qed.


(* -------------------------------------------------------------------------- *)
(* Iteration <-> mathcomp folds / quantifiers                                 *)
(*                                                                            *)
(* [L.ifold_ n] recurses twice per level, hence performs at most [2^n - 1]    *)
(* steps of a plain sequential loop. Everything about the doubling recursion  *)
(* is confined to [ifold_loopE]; the bound [2^63] only enters in [ifoldE].    *)
(* -------------------------------------------------------------------------- *)

Section IFold.

Context {T : Type} (f : int -> T -> T) (M : int).

Implicit Types (stop : int -> T -> bool).

Fixpoint loop stop (k : nat) (i : int) (x : T) : int * T :=
  if (i =? M)%uint63 || stop i x then (i, x) else
  if k is k'.+1 then loop stop k' (i + 1)%uint63 (f i x) else (i, x).

Lemma loop0 stop i x : loop stop 0 i x = (i, x).
Proof. by rewrite /=; case: ifP. Qed.

Lemma loop_stop stop k i x : (i =? M)%uint63 || stop i x -> loop stop k i x = (i, x).
Proof. by case: k => [|k] /= ->. Qed.

Lemma loopD stop a b i x :
  loop stop (a + b) i x = let: (i', x') := loop stop a i x in loop stop b i' x'.
Proof.
elim: a i x => [|a ih] i x; first by rewrite add0n loop0.
rewrite addSn /=; case: ifP => h; first by rewrite /= (loop_stop b h).
by rewrite ih.
Qed.

Lemma ifold_loopE stop n i x : L.ifold_ n f i M stop x = loop stop (2 ^ n).-1 i x.
Proof.
elim: n i x => [|n ih] i x; first by rewrite expn0 /=; case: ifP.
have -> : (2 ^ n.+1).-1 = ((2 ^ n).-1 + (2 ^ n).-1).+1.
  by rewrite expnS mul2n -addnn -[2 ^ n](prednK (expn_gt0 2 n)) addSn !succnK addnS.
rewrite /=; case: ifP => // _; rewrite loopD ih.
case: (loop _ _ _ _) => i1 x1 /=; rewrite ih.
by case: (loop _ _ _ _).
Qed.

Lemma loop_nostop stop k i x : (forall j y, stop j y = false) ->
  nat_of_int i <= nat_of_int M -> nat_of_int M - nat_of_int i <= k ->
  loop stop k i x =
    (M, foldl (fun acc j => f (int_of_nat j) acc) x
              (iota (nat_of_int i) (nat_of_int M - nat_of_int i))).
Proof.
move=> hstop; elim: k i x => [|k ih] i x hle.
  rewrite leqn0 subn_eq0 => hge.
  have heq : nat_of_int i = nat_of_int M by apply/eqP; rewrite eqn_leq hle hge.
  by rewrite loop0 (nat_of_int_inj heq) subnn.
rewrite /= hstop orbF eqb_natE; case: ifP => [/eqP heq _|/eqP hne hk].
  by rewrite (nat_of_int_inj heq) subnn.
have hlt : nat_of_int i < nat_of_int M by rewrite ltn_neqAle hle andbT; apply/eqP.
have hS : nat_of_int (i + 1)%uint63 = (nat_of_int i).+1.
  by apply: (@add1_natE i M); rewrite ltb_natE.
rewrite ih ?hS //; last by rewrite subnS -subn1 leq_subLR add1n.
have -> : nat_of_int M - nat_of_int i = (nat_of_int M - (nat_of_int i).+1).+1.
  by rewrite subnS prednK // subn_gt0.
by rewrite /= nat_of_intK.
Qed.

Lemma loop_fix k i x : (forall j, f j x = x) -> (loop (fun _ _ => false) k i x).2 = x.
Proof.
move=> hx; elim: k i => [|k ih] i /=; case: ifP => // _.
by rewrite hx ih.
Qed.

(* A stop condition that only fires on states fixed by [f] can be dropped. *)
Lemma loop_absorb stop k i x :
  (forall j y, stop j y -> forall j', f j' y = y) ->
  (loop stop k i x).2 = (loop (fun _ _ => false) k i x).2.
Proof.
move=> habs; elim: k i x => [|k ih] i x; first by rewrite !loop0.
rewrite /= orbF; case: (i =? M)%uint63 => //=.
case: ifP => [hst|_]; last exact: ih.
by have hx := habs _ _ hst; rewrite hx loop_fix.
Qed.

End IFold.

Lemma ifoldE T (f : int -> T -> T) M (x : T) :
  L.ifold f M x = foldl (fun acc j => f (int_of_nat j) acc) x (iota 0 (nat_of_int M)).
Proof.
rewrite /L.ifold ifold_loopE loop_nostop ?nat_of_int0 ?subn0 //.
by rewrite -ltnS prednK ?expn_gt0 // nat_of_int_lt_size.
Qed.

Lemma ifold_from_until_absorbE T (f : int -> T -> T) k M (stop : int -> T -> bool) (x : T) :
  (forall j y, stop j y -> forall j', f j' y = y) ->
  nat_of_int k <= nat_of_int M ->
  L.ifold_from_until f k M stop x =
    foldl (fun acc j => f (int_of_nat j) acc) x
          (iota (nat_of_int k) (nat_of_int M - nat_of_int k)).
Proof.
move=> habs hkM; rewrite /L.ifold_from_until ifold_loopE (loop_absorb _ _ _ _ habs).
rewrite loop_nostop //.
by rewrite -ltnS prednK ?expn_gt0 // (leq_ltn_trans (leq_subr _ _) (nat_of_int_lt_size M)).
Qed.

(* Every LowLevelChecker traversal unfolds to [L.ifold_ 63 ...], a doubly
   recursive fixpoint that the conversion machine unrolls exponentially as soon
   as it is compared against anything not syntactically identical. From here
   on it is only reasoned about through [ifoldE]/[ifold_from_until_absorbE], so
   make it opaque for unification: hangs become fast failures. *)
#[global] Opaque L.ifold_ L.ifold L.ifold_from_until.
(* [global]: the opacity must also protect the certificate layer (Refinement.v)
   and any further refinement built on these bridges. It does not affect
   [vm_compute]/[native_compute], so CheckCert is unaffected. *)

Section ArrayBridge.

(* Array length as a nat, through a single monomorphic constant: bridge
   statements and hypotheses must both use [alen] so that unification never has
   to identify two universe instances of the polymorphic primitive
   [PArray.length] (which fails first-order and then falls back to unfolding). *)
Definition alength {T} (a : array T) : int := length a.
Arguments alength : simpl never.
Definition alen {T} (a : array T) : nat := nat_of_int (alength a).
Arguments alen : simpl never.
(* [PArray.length] is universe polymorphic: an [array int] gives [length@{Set}],
   a lemma over [T : Type] gives [length@{u}] with [Set < u], and unification
   refuses to identify the two (conversion accepts them). Statements therefore
   mention [alength]/[alen] only; raw [length] is met only under conversion. *)

Definition aget {T} (a : array T) {n} (i : 'I_n) : T := a.[int_of_nat i].

(* Length tests, reflected through [alen]. *)
Lemma hasLengthP T (k : int) (a : array T) : reflect (alen a = nat_of_int k) (L.hasLength k a).
Proof. by rewrite /L.hasLength eqb_natE /alen; apply: eqP. Qed.


Lemma foldl_andb (I : Type) (p : I -> bool) b (s : seq I) :
  foldl (fun acc j => acc && p j) b s = b && all p s.
Proof. by elim: s b => [|j s ih] b /=; [rewrite andbT | rewrite ih andbA]. Qed.

Lemma foldl_orb (I : Type) (p : I -> bool) b (s : seq I) :
  foldl (fun acc j => acc || p j) b s = b || has p s.
Proof. by elim: s b => [|j s ih] b /=; [rewrite orbF | rewrite ih orbA]. Qed.

Lemma all_iotaP n (p : nat -> bool) : reflect (forall i : 'I_n, p i) (all p (iota 0 n)).
Proof.
apply: (iffP allP) => [h i|h j]; first by apply: h; rewrite mem_iota leq0n add0n ltn_ord.
by rewrite mem_iota leq0n add0n => hj; exact: (h (Ordinal hj)).
Qed.

Lemma has_iotaP n (p : nat -> bool) : reflect (exists i : 'I_n, p i) (has p (iota 0 n)).
Proof.
apply: (iffP hasP) => [[j]|[i hi]].
  by rewrite mem_iota leq0n add0n => hj hp; exists (Ordinal hj).
by exists (val i) => //; rewrite mem_iota leq0n add0n ltn_ord.
Qed.

Lemma for_allP T (f : T -> bool) (a : array T) n : alen a = n ->
  reflect (forall i : 'I_n, f (aget a i)) (L.for_all f a).
Proof.
move=> <-; rewrite /alen /L.for_all /L.fold ifoldE /= foldl_andb /=.
exact: all_iotaP.
Qed.

Lemma for_alliP T (f : int -> T -> bool) (a : array T) n : alen a = n ->
  reflect (forall i : 'I_n, f (int_of_nat i) (aget a i)) (L.for_alli f a).
Proof.
move=> <-; rewrite /alen /L.for_alli /L.foldi ifoldE /= foldl_andb /=.
exact: all_iotaP.
Qed.

Lemma existP T (f : T -> bool) (a : array T) n : alen a = n ->
  reflect (exists i : 'I_n, f (aget a i)) (L.exist f a).
Proof.
move=> <-; rewrite /alen /L.exist /L.fold_from_until ifold_from_until_absorbE.
- by rewrite nat_of_int0 subn0 /= foldl_orb /=; exact: has_iotaP.
- by move=> j y /= -> j'.
- by rewrite nat_of_int0.
Qed.

(* The same three reflections with the length pre-instantiated to [alen a]:
   the form almost every use site wants. *)
Lemma for_all_alenP T (f : T -> bool) (a : array T) :
  reflect (forall i : 'I_(alen a), f (aget a i)) (L.for_all f a).
Proof. by apply: for_allP. Qed.

Lemma exist_alenP T (f : T -> bool) (a : array T) :
  reflect (exists i : 'I_(alen a), f (aget a i)) (L.exist f a).
Proof. by apply: existP. Qed.


Lemma foldl_map (T1 T2 R : Type) (h : T1 -> T2) (g : R -> T2 -> R) z (s : seq T1) :
  foldl g z (map h s) = foldl (fun z x => g z (h x)) z s.
Proof. by elim: s z => [|x s ih] z //=. Qed.

Lemma fold2E T1 T2 A (f : T1 -> T2 -> A -> A) (a1 : array T1) (a2 : array T2) (x0 : A) n :
  alen a1 = n -> alen a2 = n ->
  L.fold2 f a1 a2 x0 = foldl (fun acc (i : 'I_n) => f (aget a1 i) (aget a2 i) acc) x0 (enum 'I_n).
Proof.
move=> h1 h2; rewrite /alen in h1 h2; rewrite /L.fold2.
have -> : (if (length a1 <? length a2)%uint63 then length a1 else length a2) = length a2.
  by rewrite ltb_natE h1 h2 ltnn.
by rewrite ifoldE h2 -val_enum_ord foldl_map.
Qed.

Lemma fold3E T1 T2 T3 A (f : T1 -> T2 -> T3 -> A -> A)
    (a1 : array T1) (a2 : array T2) (a3 : array T3) (x0 : A) n :
  alen a1 = n -> alen a2 = n -> alen a3 = n ->
  L.fold3 f a1 a2 a3 x0
  = foldl (fun acc (i : 'I_n) => f (aget a1 i) (aget a2 i) (aget a3 i) acc) x0 (enum 'I_n).
Proof.
move=> h1 h2 h3; rewrite /alen in h1 h2 h3; rewrite /L.fold3.
have -> : (if (length a1 <? length a3)%uint63 then
             if (length a1 <? length a2)%uint63 then length a1 else length a2
           else if (length a2 <? length a3)%uint63 then length a2 else length a3) = length a3.
  by rewrite !ltb_natE h1 h2 h3 !ltnn.
by rewrite ifoldE h3 -val_enum_ord foldl_map.
Qed.

(* Same, indexed by naturals, over the shorter array. *)
Lemma fold2_min_iotaE T1 T2 A (f : T1 -> T2 -> A -> A) (a1 : array T1) (a2 : array T2) (x0 : A) :
  L.fold2 f a1 a2 x0
  = foldl (fun acc j => f a1.[int_of_nat j] a2.[int_of_nat j] acc) x0
          (iota 0 (minn (alen a1) (alen a2))).
Proof.
rewrite /L.fold2 ifoldE; cbv beta.
have -> : nat_of_int (if (length a1 <? length a2)%uint63 then length a1 else length a2)
          = minn (alen a1) (alen a2).
  rewrite /minn ltb_natE -[nat_of_int (length a1)]/(alen a1) -[nat_of_int (length a2)]/(alen a2).
  by case: ifP.
done.
Qed.

(* Folding a three-way comparison: [Lt] comes from a first differing index. *)
Section CmpFold.

Variable (c : nat -> comparison).

#[local] Definition cstep (acc : comparison) (j : nat) : comparison :=
  match acc with Lt => Lt | Gt => Gt | Eq => c j end.

Lemma foldl_cmp_absorb r s : r <> Eq -> foldl cstep r s = r.
Proof.
move=> hr; have hstep j : cstep r j = r by case: r hr.
by elim: s => //= j s ih; rewrite hstep.
Qed.

Lemma foldl_cmp_Lt k n : foldl cstep Eq (iota k n) = Lt ->
  exists p, [/\ k <= p, p < k + n, (forall q, k <= q < p -> c q = Eq) & c p = Lt].
Proof.
elim: n k => [|n ih] k //= hfold.
have {hfold} hfold : foldl cstep (c k) (iota k.+1 n) = Lt by exact: hfold.
move: hfold; case hck: (c k) => hfold.
- have [p [hkp hpn hpre hp]] := ih _ hfold; exists p; split=> //.
  + exact: ltnW.
  + by rewrite -addSnnS.
  move=> q /andP[hkq hqp]; move: hkq; rewrite leq_eqVlt => /orP[/eqP <- //|hkq].
  by apply: hpre; rewrite hkq hqp.
- exists k; split; [exact: leqnn | by rewrite addnS ltnS leq_addr | | exact: hck].
  by move=> q /andP[hkq hqk]; have := leq_ltn_trans hkq hqk; rewrite ltnn.
- by rewrite foldl_cmp_absorb in hfold.
Qed.


Lemma foldl_cmp_Eq k n : foldl cstep Eq (iota k n) = Eq -> forall q, k <= q < k + n -> c q = Eq.
Proof.
elim: n k => [|n ih] k /=.
  by move=> _ q; rewrite addn0 => /andP[hkq hqk]; have := leq_ltn_trans hkq hqk; rewrite ltnn.
move=> hfold; have {hfold} hfold : foldl cstep (c k) (iota k.+1 n) = Eq by exact: hfold.
move: hfold; case hck: (c k) => hfold.
- move=> q /andP[hkq hqk]; move: hkq; rewrite leq_eqVlt => /orP[/eqP <- //|hkq].
  by apply: (ih k.+1 hfold); rewrite hkq addSnnS hqk.
- by rewrite foldl_cmp_absorb in hfold.
- by rewrite foldl_cmp_absorb in hfold.
Qed.
End CmpFold.

(* Counting with an int accumulator (no overflow: the count is bounded by an
   existing int [M]). *)
Lemma foldl_count_int (p : nat -> bool) (s : seq nat) (z M : int) :
  (nat_of_int z + size s <= nat_of_int M)%N ->
  nat_of_int (foldl (fun acc j => if p j then (acc + 1)%uint63 else acc) z s)
  = nat_of_int z + count p s.
Proof.
elim: s z => [|j s ih] z hz /=; first by rewrite addn0.
case: (p j) => /=; last by rewrite ih ?add0n //; move: hz; rewrite addnS => /ltnW.
have hS : nat_of_int (z + 1)%uint63 = (nat_of_int z).+1.
  by apply: (add1_natE (j := M)); rewrite ltb_natE (leq_trans _ hz) // addnS ltnS leq_addr.
by rewrite ih ?hS ?addSn ?addnS //; move: hz; rewrite addnS.
Qed.

Lemma countiE T (P : int -> T -> bool) (a : array T) :
  nat_of_int (L.counti P a) = count (fun j => P (int_of_nat j) a.[int_of_nat j]) (iota 0 (alen a)).
Proof.
rewrite /L.counti /L.foldi ifoldE; cbv beta; rewrite -[nat_of_int (length a)]/(alen a).
rewrite (@foldl_count_int _ _ _ (alength a)) ?nat_of_int0 ?add0n //.
by rewrite size_iota -[nat_of_int (alength a)]/(alen a) leqnn.
Qed.

End ArrayBridge.

(* -------------------------------------------------------------------------- *)
(* BigZ -> Z -> R                                                             *)
(*                                                                            *)
(* [Z2R] is defined by cases on [Z]; the ring-morphism lemmas go through the  *)
(* decomposition [z = of_nat (to_nat z) - of_nat (to_nat (-z))] so that only  *)
(* [Z2R_sub_nat] needs any case analysis. The bigZ bridges are one-liners     *)
(* over [BigZ.spec_*].                                                        *)
(* -------------------------------------------------------------------------- *)

Section ZBridge.

Context (R : realFieldType).

Local Open Scope ring_scope.

Definition Z2R (z : Z) : R :=
  match z with
  | Z0 => 0
  | Zpos p => (Pos.to_nat p)%:R
  | Zneg p => - (Pos.to_nat p)%:R
  end.

Lemma Z2R_of_nat n : Z2R (Z.of_nat n) = n%:R.
Proof. by case: n => [|n] //=; rewrite SuccNat2Pos.id_succ. Qed.

Lemma Z2R_opp z : Z2R (- z) = - Z2R z.
Proof. by case: z => [|p|p] /=; rewrite ?oppr0 ?opprK. Qed.

Lemma Z2R_sub_nat a b : Z2R (Z.of_nat a - Z.of_nat b) = a%:R - b%:R.
Proof.
case: (leqP b a) => [hba|hab].
  by rewrite -Nat2Z.inj_sub ?Z2R_of_nat ?minusE ?natrB //; apply/ssrnat.leP.
have -> : (Z.of_nat a - Z.of_nat b = - (Z.of_nat b - Z.of_nat a))%Z by lia.
rewrite -Nat2Z.inj_sub; last by apply/ssrnat.leP/ltnW.
by rewrite Z2R_opp Z2R_of_nat minusE natrB ?opprB //; apply/ltnW.
Qed.

Lemma Zdecomp z : z = (Z.of_nat (Z.to_nat z) - Z.of_nat (Z.to_nat (- z)))%Z.
Proof. lia. Qed.

Lemma Z2R_decomp z : Z2R z = (Z.to_nat z)%:R - (Z.to_nat (- z))%:R.
Proof. by rewrite {1}(Zdecomp z) Z2R_sub_nat. Qed.

Lemma Z2R_add a b : Z2R (a + b) = Z2R a + Z2R b.
Proof.
rewrite (Z2R_decomp a) (Z2R_decomp b).
have -> : (a + b = Z.of_nat (Z.to_nat a + Z.to_nat b)%coq_nat
                 - Z.of_nat (Z.to_nat (-a) + Z.to_nat (-b))%coq_nat)%Z.
  by rewrite !Nat2Z.inj_add; lia.
by rewrite Z2R_sub_nat !plusE !natrD opprD addrACA.
Qed.

Lemma Z2R_sub a b : Z2R (a - b) = Z2R a - Z2R b.
Proof. by rewrite -Z.add_opp_r Z2R_add Z2R_opp. Qed.

Lemma Z2R_mul_nat n z : Z2R (Z.of_nat n * z) = Z2R z *+ n.
Proof.
elim: n => [|n ih]; first by rewrite /= mulr0n.
by rewrite Nat2Z.inj_succ Z.mul_succ_l Z2R_add ih mulrSr.
Qed.

Lemma Z2R_mul a b : Z2R (a * b) = Z2R a * Z2R b.
Proof.
(* [-!mulr_natl] would loop: [n%:R] is itself [1 *+ n]. *)
rewrite {1}(Zdecomp a) Z.mul_sub_distr_r Z2R_sub !Z2R_mul_nat -!(mulr_natl (Z2R b)) -mulrBl.
by rewrite -Z2R_decomp.
Qed.

Lemma Z2R_gt0 z : (0 < Z2R z) = (0 <? z)%Z.
Proof.
case: z => [|p|p] /=; first by rewrite ltxx.
  by rewrite ltr0n; apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
by rewrite oppr_gt0 ltNge ler0n.
Qed.

Lemma Z2R_eq0 z : (Z2R z == 0) = (z =? 0)%Z.
Proof.
case: z => [|p|p] /=; first by rewrite eqxx.
  by rewrite pnatr_eq0; apply/negbTE; rewrite -lt0n; apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
by rewrite oppr_eq0 pnatr_eq0; apply/negbTE; rewrite -lt0n; apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
Qed.

Lemma Z2R_lt a b : (Z2R a < Z2R b) = (a <? b)%Z.
Proof.
rewrite -subr_gt0 -Z2R_sub Z2R_gt0.
by apply/idP/idP => /Z.ltb_lt h; apply/Z.ltb_lt; lia.
Qed.

Lemma Z2R_eq a b : (Z2R a == Z2R b) = (a =? b)%Z.
Proof.
rewrite -subr_eq0 -Z2R_sub Z2R_eq0.
by apply/idP/idP => /Z.eqb_eq h; apply/Z.eqb_eq; lia.
Qed.

Lemma Z2R_le a b : (Z2R a <= Z2R b) = (a <=? b)%Z.
Proof.
rewrite le_eqVlt Z2R_eq Z2R_lt; apply/idP/idP.
  by case/orP=> [/Z.eqb_eq|/Z.ltb_lt] h; apply/Z.leb_le; lia.
move/Z.leb_le => h; case: (Z.eqb_spec a b) => [//|hne] /=.
by apply/Z.ltb_lt; lia.
Qed.

Lemma eq_divr_mulr (x y z : R) : 0 < z -> (x / z == y) = (x == y * z).
Proof.
move=> hz; have hz0 := lt0r_neq0 hz.
by apply/idP/idP => [/eqP <-|/eqP ->]; rewrite ?divfK ?mulfK // eqxx.
Qed.

(* bigZ / bigN *)

Definition bigZ2R (z : bigZ) : R := Z2R (BigZ.to_Z z).

Lemma bigZ2R_add z1 z2 : bigZ2R (z1 + z2)%bigZ = bigZ2R z1 + bigZ2R z2.
Proof. by rewrite /bigZ2R BigZ.spec_add Z2R_add. Qed.

Lemma bigZ2R_mul z1 z2 : bigZ2R (z1 * z2)%bigZ = bigZ2R z1 * bigZ2R z2.
Proof. by rewrite /bigZ2R BigZ.spec_mul Z2R_mul. Qed.

Lemma bigZ2R_0 : bigZ2R 0%bigZ = 0.
Proof. by rewrite /bigZ2R BigZ.spec_0. Qed.

Lemma bigZ_eqbE z1 z2 : (z1 =? z2)%bigZ = (bigZ2R z1 == bigZ2R z2).
Proof. by rewrite BigZ.spec_eqb /bigZ2R Z2R_eq. Qed.

Lemma bigZ_ltbE z1 z2 : (z1 <? z2)%bigZ = (bigZ2R z1 < bigZ2R z2).
Proof. by rewrite BigZ.spec_ltb /bigZ2R Z2R_lt. Qed.

Lemma bigZ_lebE z1 z2 : (z1 <=? z2)%bigZ = (bigZ2R z1 <= bigZ2R z2).
Proof. by rewrite BigZ.spec_leb /bigZ2R Z2R_le. Qed.

(* Never [simpl] a BigN/BigZ term: it unfolds the whole word tower. *)
(* The checker routes every bigN/bigZ operation through the [NativeBig]
   aliases (for extraction).  They are definitional, but keyed rewriting does
   not see through them; [nbE] renormalizes a checker-spelled goal. *)
Lemma nb_z0E : L.NativeBig.z_zero = 0%bigZ.
Proof. by []. Qed.
Lemma nb_addE : L.NativeBig.z_add = BigZ.add.
Proof. by []. Qed.
Lemma nb_mulE : L.NativeBig.z_mul = BigZ.mul.
Proof. by []. Qed.
Lemma nb_eqbE : L.NativeBig.z_eqb = BigZ.eqb.
Proof. by []. Qed.
Lemma nb_ltbE : L.NativeBig.z_ltb = BigZ.ltb.
Proof. by []. Qed.
Lemma nb_lebE : L.NativeBig.z_leb = BigZ.leb.
Proof. by []. Qed.
Lemma nb_of_nE : L.NativeBig.z_of_n = BigZ.Pos.
Proof. by []. Qed.
Lemma nb_n0E : L.NativeBig.n_zero = 0%bigN.
Proof. by []. Qed.
Lemma nb_n_eqbE : L.NativeBig.n_eqb = BigN.eqb.
Proof. by []. Qed.
Definition nbE := (nb_z0E, nb_addE, nb_mulE, nb_eqbE, nb_ltbE, nb_lebE, nb_of_nE, nb_n0E, nb_n_eqbE).

Lemma to_Z_Pos n : BigZ.to_Z (BigZ.Pos n) = BigN.to_Z n.
Proof. by []. Qed.

Lemma bigN2R_gt0 n : ~~ (n =? 0)%bigN -> 0 < bigZ2R (BigZ.Pos n).
Proof.
rewrite BigN.spec_eqb BigN.spec_0 /bigZ2R to_Z_Pos Z2R_gt0 => /negbTE /Z.eqb_neq hn.
by apply/Z.ltb_lt; have := BigN.spec_pos n; lia.
Qed.

End ZBridge.

(* -------------------------------------------------------------------------- *)
(* Arrays of bigZ <-> column vectors                                          *)
(* -------------------------------------------------------------------------- *)

Section VecBridge.

Context (R : realFieldType).

Local Open Scope ring_scope.

Definition vec_of_array d (a : array bigZ) : 'cV[R]_d :=
  \col_i bigZ2R R (aget a i).

Lemma vec_of_arrayE d a (i : 'I_d) : vec_of_array d a i 0 = bigZ2R R (aget a i).
Proof. by rewrite mxE. Qed.

(* Accumulating fold of bigZ additions, seen in R. No [simpl] on bigZ terms. *)
Lemma bigZ2R_foldl_add (I : Type) (g : I -> bigZ) z (s : seq I) :
  bigZ2R R (foldl (fun acc i => (acc + g i)%bigZ) z s)
  = bigZ2R R z + \sum_(i <- s) bigZ2R R (g i).
Proof.
elim: s z => [|i s ih] z; first by rewrite big_nil addr0.
rewrite -[foldl _ z (i :: s)]/(foldl _ (z + g i)%bigZ s).
by rewrite ih big_cons bigZ2R_add addrA.
Qed.

Lemma array_bigZ_dotE d (a b : array bigZ) :
  alen a = d -> alen b = d ->
  bigZ2R R (L.array_bigZ_dot a b) = '[vec_of_array d a, vec_of_array d b].
Proof.
move=> ha hb; rewrite /L.array_bigZ_dot (fold2E _ _ ha hb).
rewrite (bigZ2R_foldl_add (fun i : 'I_d => (aget a i * aget b i)%bigZ)) bigZ2R_0 add0r.
rewrite enumT; apply: eq_bigr => i _.
by rewrite bigZ2R_mul !vec_of_arrayE.
Qed.

Lemma array_bigZ_add_dotE d (a b e : array bigZ) :
  alen a = d -> alen b = d -> alen e = d ->
  bigZ2R R (L.array_bigZ_add_dot a b e) = '[vec_of_array d a, vec_of_array d b + vec_of_array d e].
Proof.
move=> ha hb he; rewrite /L.array_bigZ_add_dot (fold3E _ _ ha hb he).
rewrite (bigZ2R_foldl_add (fun i : 'I_d => (aget a i * (aget b i + aget e i))%bigZ)) bigZ2R_0 add0r.
rewrite enumT; apply: eq_bigr => i _.
by rewrite bigZ2R_mul bigZ2R_add !mxE.
Qed.

Definition point_of d (p : L.Point) : 'cV[R]_d :=
  (bigZ2R R (BigZ.Pos (L.commonDenominator p)))^-1 *: vec_of_array d (L.numerators p).

Lemma vdot_point_of d (u : 'cV[R]_d) p :
  '[u, point_of d p]
  = '[u, vec_of_array d (L.numerators p)] / bigZ2R R (BigZ.Pos (L.commonDenominator p)).
Proof. by rewrite vdotZr mulrC. Qed.

(* Sparse vectors (index, coefficient), as used for the root weights. *)
Definition sparse_of d (w : L.Weight) : 'cV[R]_d :=
  \col_j \sum_(p < alen w | nat_of_int (aget w p).1 == j) bigZ2R R (aget w p).2.

Lemma sparse_array_bigZ_dotE (w : L.Weight) (b : array bigZ) :
  bigZ2R R (L.sparse_array_bigZ_dot w b)
  = \sum_(p < alen w) bigZ2R R (aget w p).2 * bigZ2R R (PArray.get b (aget w p).1).
Proof.
rewrite /L.sparse_array_bigZ_dot /L.fold ifoldE; cbv beta.
rewrite -[nat_of_int (length w)]/(alen w).
rewrite (bigZ2R_foldl_add (fun j => (PArray.get b (PArray.get w (int_of_nat j)).1
                                     * (PArray.get w (int_of_nat j)).2)%bigZ)).
rewrite bigZ2R_0 add0r -val_enum_ord big_map enumT; apply: eq_bigr => p _.
by rewrite bigZ2R_mul mulrC.
Qed.

(* Linear-algebra identities. *)
Lemma vdot_mulmx n (A : 'M[R]_(n, n)) (v u : 'cV[R]_n) :
  '[A *m v, u] = \sum_j v j 0 * '[col j A, u].
Proof.
rewrite /vdot (eq_bigr (fun r => \sum_j A r j * v j 0 * u r 0)); last first.
  by move=> r _; rewrite mxE big_distrl.
rewrite exchange_big; apply: eq_bigr => j _; rewrite big_distrr; apply: eq_bigr => r _.
by rewrite mxE mulrAC mulrC.
Qed.

Lemma big_ord_eq n (F : 'I_n -> R) (k : nat) (hk : (k < n)%N) :
  \sum_(j < n | k == j) F j = F (Ordinal hk).
Proof. by apply: big_pred1 => j; rewrite /= -val_eqE. Qed.

Lemma sum_sparse_of d (w : L.Weight) (G : 'I_d -> R) :
  \sum_(j < d) sparse_of d w j 0 * G j
  = \sum_(p < alen w) bigZ2R R (aget w p).2 * \sum_(j < d | nat_of_int (aget w p).1 == j) G j.
Proof.
rewrite (eq_bigr (fun j : 'I_d => \sum_(p < alen w | nat_of_int (aget w p).1 == j)
                                    bigZ2R R (aget w p).2 * G j)); last first.
  by move=> j _; rewrite mxE big_distrl.
rewrite (exchange_big_dep predT) //; apply: eq_bigr => p _.
by rewrite big_distrr; apply: eq_bigl => j /=.
Qed.

End VecBridge.

(* -------------------------------------------------------------------------- *)
(* Sorted [array int] <-> {set 'I_m}, and the [fold_alt] traversal            *)
(* -------------------------------------------------------------------------- *)

Section SetBridge.

Definition set_of_array m (a : array int) : {set 'I_m} :=
  [set i : 'I_m | [exists j : 'I_(alen a), nat_of_int (aget a j) == i]].

Lemma in_set_of_array m a (i : 'I_m) :
  reflect (exists j : 'I_(alen a), nat_of_int (aget a j) = i)
          (i \in set_of_array m a).
Proof.
rewrite inE; apply: (iffP existsP) => -[j h]; exists j; [exact/eqP | exact/eqP].
Qed.

Lemma card_set_of_array n (a : array int) : #|set_of_array n a| <= alen a.
Proof.
case: n => [|n]; first by apply: (leq_trans (max_card _)); rewrite card_ord.
pose g (j : 'I_(alen a)) : 'I_n.+1 := insubd ord0 (nat_of_int (aget a j)).
have hsub : set_of_array n.+1 a \subset g @: setT.
  apply/subsetP => i /in_set_of_array[j hj]; apply/imsetP; exists j; first exact: in_setT.
  by apply/val_inj; rewrite /g val_insubd hj /= ltn_ord.
apply: (leq_trans (subset_leq_card hsub)); apply: (leq_trans (leq_imset_card g setT)).
by rewrite cardsT card_ord.
Qed.

Lemma for_alli_alenP T (f : int -> T -> bool) (a : array T) :
  reflect (forall i : 'I_(alen a), f (int_of_nat i) (aget a i)) (L.for_alli f a).
Proof. by apply: for_alliP. Qed.

(* Strict sortedness: consecutive entries, for an arbitrary order. *)
Lemma isStrictlySorted_consecT T (ltT : T -> T -> bool) (a : array T) :
  L.isStrictlySorted ltT a ->
  forall (k k' : 'I_(alen a)), k' = k.+1 :> nat -> ltT (aget a k) (aget a k').
Proof.
rewrite /L.isStrictlySorted => /for_alli_alenP h k k' hk'.
have hk : k.+1 < alen a by rewrite -hk'.
have hkk : nat_of_int (int_of_nat k) = k by apply: (int_of_natK_le (i := length a)); exact: ltnW.
have := h k; rewrite /L.compareConsecutive /= leb_natE hkk.
rewrite sub1_natE; last by exact: leq_ltn_trans hk.
rewrite -[nat_of_int (length a)]/(alen a) leqNgt ltn_predRL hk (int_of_natS (ltnW hk)) /=.
by rewrite /aget hk'.
Qed.

Lemma consec_chain (T : Type) (R : T -> T -> Prop) (E : nat -> T) ln :
  (forall x y z, R x y -> R y z -> R x z) ->
  (forall k, k.+1 < ln -> R (E k) (E k.+1)) ->
  forall j1 j2, j1 < j2 -> j2 < ln -> R (E j1) (E j2).
Proof.
move=> tr hE j1 j2; elim: j2 => // j2 ih; rewrite ltnS leq_eqVlt => /orP[/eqP->|/ih h] hj2.
  exact: hE.
exact: tr (h (ltnW hj2)) (hE _ hj2).
Qed.

(* Lexicographic order on finite sequences, given as functions with their lengths. *)
Definition lexlt (E : nat -> nat) la (F : nat -> nat) lb :=
  exists p, (forall q, q < p -> E q = F q)
            /\ ([/\ p < la, p < lb & E p < F p] \/ (p = la /\ la < lb)).

Lemma lexlt_trans E la F lb G lc : lexlt E la F lb -> lexlt F lb G lc -> lexlt E la G lc.
Proof.
move=> [p [hpre hc]] [p' [hpre' hc']].
have hpa : p <= la by case: hc => [[h _ _]|[-> _]]; [exact: ltnW | exact: leqnn].
have hpb : p <= lb by case: hc => [[_ h _]|[-> h]]; exact: ltnW.
have hpc' : p' <= lc by case: hc' => [[_ h _]|[-> h]]; exact: ltnW.
have hpre2 : forall q, q < minn p p' -> E q = G q.
  by move=> q; rewrite leq_min => /andP[hq hq']; rewrite (hpre q hq) (hpre' q hq').
case hpp: (p < p').
  exists p; split.
    by move=> q hq; apply: hpre2; rewrite leq_min hq (ltn_trans hq hpp).
  case: hc => [[h1 h2 h3]|[h1 h2]].
    by left; split=> //; [exact: leq_trans hpp hpc' | rewrite -(hpre' p hpp)].
  by right; split=> //; rewrite -h1; exact: leq_trans hpp hpc'.
case hpp': (p' < p).
  case: hc' => [[h1 h2 h3]|[h1 h2]]; last by move: hpb; rewrite -h1 leqNgt hpp'.
  exists p'; split.
    by move=> q hq; apply: hpre2; rewrite leq_min hq (ltn_trans hq hpp').
  by left; split=> //; [exact: leq_trans hpp' hpa | rewrite (hpre p' hpp')].
have /eqP heq : p == p' by rewrite eqn_leq (leqNgt p p') (leqNgt p' p) hpp' hpp.
subst p'; exists p; split; first by move=> q hq; apply: hpre2; rewrite leq_min hq.
case: hc => [[h1 h2 h3]|[h1 h2]]; case: hc' => [[h1' h2' h3']|[h1' h2']].
- by left; split=> //; exact: ltn_trans h3 h3'.
- by move: h2; rewrite h1' ltnn.
- by right; split=> //; rewrite -h1.
- by move: h2; rewrite -h1' h1 ltnn.
Qed.

(* [ltbArray] on int arrays is the lexicographic order on their entries. *)
Lemma ltbArray_lexlt (a b : array int) :
  L.ltbArray Uint63.eqb Uint63.ltb a b ->
  lexlt (fun j => nat_of_int a.[int_of_nat j]) (alen a) (fun j => nat_of_int b.[int_of_nat j]) (alen b).
Proof.
rewrite /L.ltbArray /L.lex_cmp; cbv zeta; rewrite fold2_min_iotaE.
rewrite !ltb_natE -[nat_of_int (length a)]/(alen a) -[nat_of_int (length b)]/(alen b).
pose c0 j := if (a.[int_of_nat j] <? b.[int_of_nat j])%uint63 then Lt
             else if (b.[int_of_nat j] <? a.[int_of_nat j])%uint63 then Gt else Eq.
have hEq q : c0 q = Eq -> nat_of_int a.[int_of_nat q] = nat_of_int b.[int_of_nat q].
  rewrite /c0; case: ifP => // h1; case: ifP => // h2 _.
  by apply/eqP; rewrite eqn_leq leqNgt -ltb_natE h2 leqNgt -ltb_natE h1.
have hLt q : c0 q = Lt -> nat_of_int a.[int_of_nat q] < nat_of_int b.[int_of_nat q].
  by rewrite /c0; case: ifP => [h1 _|_]; [rewrite -ltb_natE | case: ifP].
set N := minn (alen a) (alen b).
(* The [exact: hf] below are conversions: the goal's anonymous fold function
   is convertible to [cstep c0] but not syntactically equal to it. *)
case hf: (foldl _ Eq (iota 0 N)) => //=.
- (* decided by the lengths *)
  have hf' : foldl (cstep c0) Eq (iota 0 N) = Eq by exact: hf.
  have hpre := foldl_cmp_Eq hf'.
  case: ifP => [hab _|_]; last by case: ifP => _ /=.
  have hN : N = alen a by rewrite /N /minn hab.
  exists (alen a); split; last by right.
  by move=> q hq; apply: hEq; apply: hpre; rewrite leq0n add0n hN.
- (* decided inside the common prefix *)
  move=> _; have hf' : foldl (cstep c0) Eq (iota 0 N) = Lt by exact: hf.
  have [p [_ hpN hpre hp]] := foldl_cmp_Lt hf'; rewrite add0n in hpN.
  have hpa : p < alen a := leq_trans hpN (geq_minl _ _).
  have hpb : p < alen b := leq_trans hpN (geq_minr _ _).
  exists p; split; last by left; split=> //; exact: hLt.
  by move=> q hq; apply: hEq; apply: hpre; rewrite leq0n.
Qed.

End SetBridge.

Section ForAllAlt.

Context {T : Type} (f_in f_notin : T -> bool) (s : array T) (notin : array int).

Let n := alen s.
Let ln := alen notin.
Let E (k : nat) := nat_of_int notin.[int_of_nat k].

Let P (j : nat) :=
  if [exists jj : 'I_ln, E jj == j] then f_in s.[int_of_nat j] else f_notin s.[int_of_nat j].

(* One step of [L.fold_alt], as produced by [ifoldE]. *)
Let step (acc : bool * int) (j : nat) : bool * int :=
  let i := int_of_nat j in
  if ((acc.2 <? length notin) ==> (i <? notin.[acc.2]))%uint63
  then (f_notin s.[i] && acc.1, acc.2)
  else (f_in s.[i] && acc.1, (acc.2 + 1)%uint63).

(* The cursor [c] splits [notin] into entries [< k] and entries [>= k]. *)
Let INV (k : nat) (c : int) :=
  nat_of_int c <= ln /\ forall j, j < ln -> (j < nat_of_int c) = (E j < k).

Hypothesis hsorted : forall j1 j2, j1 < j2 -> j2 < ln -> E j1 < E j2.

#[local] Lemma step_inv k c b : k < n -> INV k c ->
  (step (b, c) k).1 = P k && b /\ INV k.+1 (step (b, c) k).2.
Proof.
(* Only plain boolean case splits here ([case h: (a < b)]): eliminating
   [ltngtP]/[ltnP] (indexed variants) abstracts all comparison terms over this
   goal and ssreflect's matching then blows up. *)
move=> hk [hc hinv]; rewrite /step /P /=.
have hkk : nat_of_int (int_of_nat k) = k by apply: (int_of_natK_le (i := length s)); exact: ltnW.
have hnc : notin.[c] = notin.[int_of_nat (nat_of_int c)] by rewrite nat_of_intK.
rewrite ltb_natE; set c' := nat_of_int c.
case hcl: (c' < ln) => /=; last first.
  (* cursor exhausted: c' = ln, k is not in notin *)
  have hceq : c' = ln by apply/eqP; rewrite eqn_leq hc leqNgt hcl.
  have -> : [exists jj : 'I_ln, E jj == k] = false.
    apply/negbTE/existsP => -[jj /eqP hjj]; move: (hinv jj (ltn_ord jj)).
    by rewrite hjj ltnn -/c' hceq ltn_ord.
  split=> //; split=> // j hj; move: (hinv j hj).
  by rewrite -/c' hceq hj => /esym h; rewrite ltnS (ltnW h).
rewrite hnc ltb_natE hkk -[nat_of_int notin.[_]]/(E c').
have hEc : k <= E c' by rewrite leqNgt; move: (hinv c' hcl); rewrite -/c' ltnn => <-.
case hlt: (k < E c') => /=.
- (* k < E c' : k is not in notin *)
  have -> : [exists jj : 'I_ln, E jj == k] = false.
    apply/negbTE/existsP => -[jj /eqP hjj]; move: (hinv jj (ltn_ord jj)).
    rewrite hjj ltnn -/c'; case hj': (jj < c') => // _.
    have hj'' : c' <= jj by rewrite leqNgt hj'.
    have : E c' <= E jj.
      (* [done] on [E jj <= E jj] would try to evaluate it: use [leqnn]. *)
      move: hj''; rewrite leq_eqVlt => /orP[/eqP->|/hsorted h]; first by rewrite leqnn.
      exact: ltnW (h (ltn_ord jj)).
    by rewrite hjj leqNgt hlt.
  split=> //; split=> // j hj; case hj': (j < c').
    by move: (hinv j hj); rewrite -/c' hj' => /esym h; rewrite ltnS (ltnW h).
  have hj'' : c' <= j by rewrite leqNgt hj'.
  have hle : E c' <= E j.
    move: hj''; rewrite leq_eqVlt => /orP[/eqP->|/hsorted h]; first by rewrite leqnn.
    exact: ltnW (h hj).
  by rewrite ltnS leqNgt (leq_trans hlt hle).
- (* k = E c' : k is in notin *)
  have heq : k = E c' by apply/eqP; rewrite eqn_leq hEc leqNgt hlt.
  have -> : [exists jj : 'I_ln, E jj == k].
    by apply/existsP; exists (Ordinal hcl); rewrite /= heq eqxx.
  have hS : nat_of_int (c + 1)%uint63 = c'.+1.
    by apply: (add1_natE (j := length notin)); rewrite ltb_natE.
  split=> //; split; first by rewrite hS.
  move=> j hj; rewrite hS !ltnS; case hj': (j <= c').
    move: hj'; rewrite leq_eqVlt => /orP[/eqP->|hj2].
      by rewrite -heq !leqnn.
    by move: (hinv j hj); rewrite -/c' hj2 => /esym h; rewrite (ltnW h).
  have hj2 : c' < j by rewrite ltnNge hj'.
  by rewrite heq leqNgt (hsorted hj2 hj).
Qed.

#[local] Lemma foldl_step_inv m k b c : k + m <= n -> INV k c ->
  (foldl step (b, c) (iota k m)).1 = b && all P (iota k m).
Proof.
elim: m k b c => [|m ih] k b c hkm hinv; first by rewrite /= andbT.
have hk : k < n by rewrite (leq_trans _ hkm) // addnS ltnS leq_addr.
have [h1 h2] := step_inv b hk hinv.
rewrite -[iota k m.+1]/(k :: iota k.+1 m) -[foldl _ _ (_ :: _)]/(foldl step (step (b, c) k) (iota k.+1 m)).
rewrite -[all P (_ :: _)]/(P k && all P (iota k.+1 m)).
move: h1 h2; case: (step (b, c) k) => b' c' /= -> h2.
by rewrite (ih _ _ _ _ h2) ?addSnnS // andbAC andbC.
Qed.

Lemma for_all_altP :
  reflect (forall i : 'I_n,
             if i \in set_of_array n notin then f_in (aget s i) else f_notin (aget s i))
          (L.for_all_alt f_in f_notin s notin).
Proof.
have -> : L.for_all_alt f_in f_notin s notin = (foldl step (true, 0%uint63) (iota 0 n)).1.
  by rewrite /L.for_all_alt /L.fold_alt /L.foldi ifoldE.
have hinv0 : INV 0 0%uint63.
  by split; [rewrite nat_of_int0 leq0n | move=> j _; rewrite nat_of_int0 !ltn0].
rewrite (foldl_step_inv (m := n) (k := 0) (c := 0%uint63) true _ hinv0).
  by apply: (iffP (all_iotaP _ _)) => h i; move: (h i); rewrite /P inE.
by rewrite add0n leqnn.
Qed.

End ForAllAlt.

(* Corollaries of the iteration and set bridges, in the shape used by the     *)
(* certificate checks.                                                        *)

Lemma for_all_composeP A B (f : B -> bool) (g : A -> B) (a : array A) n :
  alen a = n ->
  reflect (forall i : 'I_n, f (g (aget a i))) (L.for_all_compose f g a).
Proof. move=> h; have h2 := for_allP (Basics.compose f g) h; exact: h2. Qed.

Lemma for_all_compose_alenP A B (f : B -> bool) (g : A -> B) (a : array A) :
  reflect (forall i : 'I_(alen a), f (g (aget a i))) (L.for_all_compose f g a).
Proof. by apply: for_all_composeP. Qed.

(* Entries of a family of arrays all within [0, n): the composed form used by
   the well-formedness checks. *)
Lemma allInRange_ordP T (g : T -> array int) (s : array T) (n : int) (k : 'I_(alen s)) :
  (0 < nat_of_int n)%N ->
  L.for_all_compose (L.allInRange Uint63.leb 0%uint63 (n - 1)%uint63) g s ->
  forall p : 'I_(alen (g (aget s k))), (nat_of_int (aget (g (aget s k)) p) < nat_of_int n)%N.
Proof.
move=> hn /for_all_compose_alenP/(_ k) hB p; move: hB.
rewrite /L.allInRange => /for_all_alenP/(_ p) h; exact: inRangeP hn h.
Qed.

Lemma isStrictlySorted_mono (a : array int) : L.isStrictlySorted Uint63.ltb a ->
  forall j1 j2, j1 < j2 -> j2 < alen a ->
    nat_of_int a.[int_of_nat j1] < nat_of_int a.[int_of_nat j2].
Proof.
move=> hs; apply: (consec_chain (R := fun x y : nat => (x < y)%N)
                                (E := fun k => nat_of_int a.[int_of_nat k])
                                (fun x y z => @ltn_trans y x z)).
move=> k hk; cbv beta; rewrite -ltb_natE.
have h := isStrictlySorted_consecT (k := Ordinal (ltnW hk)) (k' := Ordinal hk) hs erefl.
exact: h.
Qed.

(* A strictly sorted array with entries below [n] enumerates its set without repetition. *)
Lemma card_set_of_array_sorted n (a : array int) : L.isStrictlySorted Uint63.ltb a ->
  (forall j : 'I_(alen a), nat_of_int (aget a j) < n) -> #|set_of_array n a| = alen a.
Proof.
move=> hs hlt; pose g (j : 'I_(alen a)) : 'I_n := Ordinal (hlt j).
have hne (k1 k2 : 'I_(alen a)) : k1 < k2 -> nat_of_int (aget a k1) = nat_of_int (aget a k2) -> False.
  move=> hk hE; have := isStrictlySorted_mono hs hk (ltn_ord k2).
  by rewrite /aget in hE; rewrite hE ltnn.
have hg : injective g.
  move=> j1 j2 /(congr1 val) /= heq.
  apply/val_inj/eqP; rewrite eqn_leq (leqNgt j1 j2) (leqNgt j2 j1); apply/andP; split; apply/negP => h.
    exact: hne _ _ h (esym heq).
  exact: hne _ _ h heq.
have -> : set_of_array n a = g @: setT.
  apply/setP => i; apply/idP/idP => [/in_set_of_array[j hj]|/imsetP[j _ ->]].
    have -> : i = g j by apply/val_inj; rewrite /= hj.
    by apply: imset_f; rewrite in_setT.
  by apply/in_set_of_array; exists j.
by rewrite card_imset // cardsT card_ord.
Qed.

(* Two strictly sorted arrays in lexicographic order have different sets:
   look at the first position where they differ. *)
Lemma lexlt_sorted_neq n (a b : array int) :
  L.isStrictlySorted Uint63.ltb a -> L.isStrictlySorted Uint63.ltb b ->
  (forall j : 'I_(alen a), nat_of_int (aget a j) < n) ->
  (forall j : 'I_(alen b), nat_of_int (aget b j) < n) ->
  lexlt (fun j => nat_of_int a.[int_of_nat j]) (alen a) (fun j => nat_of_int b.[int_of_nat j]) (alen b) ->
  set_of_array n a <> set_of_array n b.
Proof.
move=> hsa hsb hra hrb [p [hpre0 hc]] heq.
have hpre : forall q, q < p -> nat_of_int a.[int_of_nat q] = nat_of_int b.[int_of_nat q] := hpre0.
have hma := isStrictlySorted_mono hsa; have hmb := isStrictlySorted_mono hsb.
case: hc => [[hpa' hpb' hlt0]|[hp hab]].
- have hlt : nat_of_int a.[int_of_nat p] < nat_of_int b.[int_of_nat p] := hlt0.
  have hi : nat_of_int a.[int_of_nat p] < n := hra (Ordinal hpa').
  have : Ordinal hi \in set_of_array n a by apply/in_set_of_array; exists (Ordinal hpa').
  rewrite heq => /in_set_of_array[q hq].
  have hq' : nat_of_int b.[int_of_nat q] = nat_of_int a.[int_of_nat p] := hq.
  case hqp: (q < p).
    by have := hma q p hqp hpa'; rewrite (hpre q hqp) hq' ltnn.
  case hpq: (p < q).
    by have := ltn_trans hlt (hmb p q hpq (ltn_ord q)); rewrite hq' ltnn.
  have /eqP hpq' : p == q by rewrite eqn_leq (leqNgt p q) (leqNgt q p) hqp hpq.
  by rewrite -hpq' in hq'; rewrite hq' ltnn in hlt.
- have hi : nat_of_int b.[int_of_nat (alen a)] < n := hrb (Ordinal hab).
  have : Ordinal hi \in set_of_array n b by apply/in_set_of_array; exists (Ordinal hab).
  rewrite -heq => /in_set_of_array[q hq].
  have hq' : nat_of_int a.[int_of_nat q] = nat_of_int b.[int_of_nat (alen a)] := hq.
  have hqp : q < p by rewrite hp.
  by have := hmb q (alen a) (ltn_ord q) hab; rewrite -(hpre q hqp) hq' ltnn.
Qed.

(* An array of strictly sorted int arrays, itself strictly increasing for
   [ltbArray], has pairwise distinct sets of entries. *)
Lemma sorted_sets_inj T (g : T -> array int) (s : array T) n :
  L.isStrictlySorted (fun x y => L.ltbArray Uint63.eqb Uint63.ltb (g x) (g y)) s ->
  (forall k : 'I_(alen s), L.isStrictlySorted Uint63.ltb (g (aget s k))) ->
  (forall (k : 'I_(alen s)) (j : 'I_(alen (g (aget s k)))), nat_of_int (aget (g (aget s k)) j) < n) ->
  injective (fun k : 'I_(alen s) => set_of_array n (g (aget s k))).
Proof.
move=> huniq hsort hrange.
suff hlt : forall k1 k2 : 'I_(alen s), k1 < k2 ->
    set_of_array n (g (aget s k1)) <> set_of_array n (g (aget s k2)).
  move=> k1 k2 heq; apply/val_inj/eqP; rewrite eqn_leq (leqNgt k1 k2) (leqNgt k2 k1).
  apply/andP; split; apply/negP => h.
    by move/hlt: h => h; apply: h; exact: esym heq.
  by move/hlt: h => h; apply: h.
move=> k1 k2 hk12 heq.
pose E (k : nat) := g (PArray.get s (int_of_nat k)).
pose Rl (x y : array int) :=
  lexlt (fun j => nat_of_int x.[int_of_nat j]) (alen x) (fun j => nat_of_int y.[int_of_nat j]) (alen y).
have hcons k : k.+1 < alen s -> Rl (E k) (E k.+1).
  move=> hk; have hk' : k < alen s := ltnW hk.
  have hl := isStrictlySorted_consecT (k := Ordinal hk') (k' := Ordinal hk) huniq erefl.
  cbv beta in hl; have hl2 := ltbArray_lexlt hl; exact: hl2.
have hR := consec_chain (R := Rl) (E := E) (fun x y z hxy hyz => lexlt_trans hxy hyz) hcons hk12 (ltn_ord k2).
exact: lexlt_sorted_neq (hsort k1) (hsort k2) (hrange k1) (hrange k2) hR heq.
Qed.

Lemma for_all_alt_alenP T (f_in f_notin : T -> bool) (s : array T) (notin : array int) n :
  alen s = n ->
  (forall j1 j2, j1 < j2 -> j2 < alen notin ->
     nat_of_int notin.[int_of_nat j1] < nat_of_int notin.[int_of_nat j2]) ->
  reflect (forall i : 'I_n,
             if i \in set_of_array n notin then f_in (aget s i) else f_notin (aget s i))
          (L.for_all_alt f_in f_notin s notin).
Proof. by move=> <- hs; apply: for_all_altP. Qed.

(* -------------------------------------------------------------------------- *)
(* The merge-based subset test [L.subset]                                     *)
(*                                                                            *)
(* Soundness only (true => set inclusion), which holds for arbitrary arrays:  *)
(* the cursor into [a] only advances on an exact match. The loop runs         *)
(* [alen a + alen b] steps; a "live" state strictly increases [i + j], so the  *)
(* loop has necessarily terminated by then.                                   *)
(* -------------------------------------------------------------------------- *)

Lemma max_length_small : (2 * to_Z PArray.max_length < wB)%Z.
Proof. by vm_compute. Qed.

(* Arithmetic on lengths goes through [alen] only: a raw [length a] from a
   library lemma carries a different universe instance than the one under
   [alen], and [lia] would see two different atoms. *)
Lemma alen_bound T (a : array T) : (Z.of_nat (alen a) <= to_Z PArray.max_length)%Z.
Proof. by rewrite /alen -to_Z_nat_of_int; apply/Uint63.lebP; exact: (leb_length _ _). Qed.

Lemma add_natE x y : (Z.of_nat (nat_of_int x) + Z.of_nat (nat_of_int y) < wB)%Z ->
  nat_of_int (x + y)%uint63 = nat_of_int x + nat_of_int y.
Proof.
move=> h; rewrite !nat_of_intE add_spec Z.mod_small.
  by rewrite Z2Nat.inj_add ?plusE //; [case: (to_Z_bounded x) | case: (to_Z_bounded y)].
by move: h; rewrite -!to_Z_nat_of_int; have := to_Z_bounded x; have := to_Z_bounded y; lia.
Qed.

Lemma alen_add T1 T2 (a : array T1) (b : array T2) :
  nat_of_int (alength a + alength b)%uint63 = alen a + alen b.
Proof.
rewrite add_natE //.
have := alen_bound (a := a); have := alen_bound (a := b); have := max_length_small.
by rewrite -[nat_of_int (alength a)]/(alen a) -[nat_of_int (alength b)]/(alen b); lia.
Qed.

Lemma ltb_alenE T (a : array T) i : (i <? alength a)%uint63 = (nat_of_int i < alen a).
Proof. by rewrite ltb_natE. Qed.

Lemma foldl_const (A B : Type) (g : A -> A) (x : A) (s : seq B) :
  foldl (fun acc _ => g acc) x s = iter (size s) g x.
Proof. by elim: s x => [|y s ih] x //=; rewrite ih -iterSr. Qed.

Section SubsetBridge.

Context (a b : array int).

Local Notation la := (alen a).
Local Notation lb := (alen b).

#[local] Definition sstep (st : int * int * bool) : int * int * bool :=
  let: (i, j, _) := st in
  if (i <? alength a)%uint63 then
    if (j <? alength b)%uint63 then
      if (a.[i] <? b.[j])%uint63 then (i, j, false)
      else if (b.[j] <? a.[i])%uint63 then (i, (j + 1)%uint63, true)
      else ((i + 1)%uint63, (j + 1)%uint63, true)
    else (i, j, false)
  else (i, j, true).

Lemma subsetE :
  L.subset Uint63.ltb a b = (iter (la + lb)%N sstep (0%uint63, 0%uint63, true)).2.
Proof.
rewrite /L.subset; cbv zeta; rewrite ifoldE; cbv beta.
by rewrite foldl_const size_iota -[length a]/(alength a) -[length b]/(alength b) alen_add.
Qed.

(* Every [a.[p]] already consumed occurs in [b]. *)
#[local] Definition sinv (st : int * int * bool) :=
  let: (i, j, _) := st in
  [/\ nat_of_int i <= la, nat_of_int j <= lb &
      forall p, p < nat_of_int i ->
        exists q, q < lb /\ b.[int_of_nat q] = a.[int_of_nat p]].

#[local] Definition live (st : int * int * bool) :=
  let: (i, j, _) := st in
  [&& nat_of_int i < la, nat_of_int j < lb & ~~ (a.[i] <? b.[j])%uint63].

#[local] Definition phi (st : int * int * bool) := let: (i, j, _) := st in (nat_of_int i + nat_of_int j)%N.

Lemma sstep_inv st : sinv st -> sinv (sstep st).
Proof.
case: st => [[i j] ok] [hi hj hpre]; rewrite /sstep.
case: ifP => [hia|_] /=; last by split.
case: ifP => [hjb|_] /=; last by split.
case: ifP => [_|hab] /=; first by split.
have hSj : nat_of_int (j + 1)%uint63 = (nat_of_int j).+1 by apply: (add1_natE (j := alength b)).
have hSi : nat_of_int (i + 1)%uint63 = (nat_of_int i).+1 by apply: (add1_natE (j := alength a)).
move: hia hjb; rewrite !ltb_alenE => hia hjb.
case: ifP => hba /=; first by split=> //; rewrite hSj.
split; rewrite ?hSi ?hSj // => p; rewrite ltnS leq_eqVlt => /orP[/eqP->|/hpre//].
exists (nat_of_int j); split=> //; rewrite !nat_of_intK.
apply: nat_of_int_inj; apply/eqP.
by rewrite eqn_leq leqNgt -ltb_natE hab leqNgt -ltb_natE hba.
Qed.

Lemma live_phi st : live st -> (phi st).+1 <= phi (sstep st).
Proof.
case: st => [[i j] ok] /and3P[hia hjb hab]; rewrite /phi /sstep.
have hSj : nat_of_int (j + 1)%uint63 = (nat_of_int j).+1.
  by apply: (add1_natE (j := alength b)); rewrite ltb_alenE.
have hSi : nat_of_int (i + 1)%uint63 = (nat_of_int i).+1.
  by apply: (add1_natE (j := alength a)); rewrite ltb_alenE.
rewrite !ltb_alenE hia hjb (negbTE hab) /=.
by case: ifP => _ /=; rewrite ?hSi hSj ?addSn addnS ?leqnn ?leqnSn.
Qed.

Lemma nlive_fix st : ~~ live st -> (sstep st).1 = st.1.
Proof.
case: st => [[i j] ok]; rewrite /live /sstep !ltb_alenE /=.
case hia: (nat_of_int i < la) => //=; case hjb: (nat_of_int j < lb) => //=.
by rewrite negbK => ->.
Qed.

Lemma live_step st : live (sstep st) -> live st.
Proof.
case hn: (live st) => // hl; move: (nlive_fix (negbT hn)) hl.
case: (sstep st) => [[i' j'] ok'] /=; case: st hn => [[i j] ok] /= hn [-> ->].
by rewrite /live in hn *; rewrite hn.
Qed.

Lemma live_iter k st : live (iter k sstep st) -> (phi st + k)%N <= phi (iter k sstep st).
Proof.
elim: k => [|k ih]; first by rewrite addn0.
rewrite iterS => hl; have hk := live_step hl.
by rewrite addnS (leq_trans _ (live_phi hk)) // ltnS ih.
Qed.

Lemma sstep_ok st : (sstep st).2 -> nat_of_int st.1.1 < la -> live st.
Proof.
case: st => [[i j] ok]; rewrite /sstep /live !ltb_alenE /= => h hia.
move: h; rewrite hia /=; case hjb: (nat_of_int j < lb) => //=.
by case hab: (a.[i] <? b.[j])%uint63 => //= _; rewrite hia hjb hab.
Qed.

Lemma subset_arr_all : L.subset Uint63.ltb a b ->
  forall p, p < la -> exists q, q < lb /\ b.[int_of_nat q] = a.[int_of_nat p].
Proof.
rewrite subsetE; set st0 := (0%uint63, 0%uint63, true).
have hinv k : sinv (iter k sstep st0).
  elim: k => [|k ih]; last by rewrite iterS; exact: sstep_inv.
  by split; rewrite ?nat_of_int0 // => p; rewrite ltn0.
case hN: (la + lb)%N => [|N].
  by move/eqP: hN; rewrite addn_eq0 => /andP[/eqP-> _] _ p; rewrite ltn0.
rewrite iterS; move: (hinv N); case E: (iter N sstep st0) => [[i j] ok] [hi _ hpre] hok p hp.
have hiN : nat_of_int i = la.
  apply/eqP; rewrite eqn_leq hi andTb leqNgt; apply/negP => hia.
  have hl := sstep_ok hok hia.
  have := live_iter (k := N) (st := st0); rewrite E => /(_ hl).
  rewrite /phi /st0 !nat_of_int0 add0n => hge.
  move: hl => /and3P[_ hjb _].
  have := leq_add hia hjb; rewrite hN addSn addnS !ltnS => hlt.
  by rewrite ltnNge hge in hlt.
by apply: hpre; rewrite hiN.
Qed.

Lemma subset_arr n : L.subset Uint63.ltb a b -> set_of_array n a \subset set_of_array n b.
Proof.
move/subset_arr_all => hsub; apply/subsetP => x /in_set_of_array [p hp].
have [q [hq hqp]] := hsub p (ltn_ord p).
by apply/in_set_of_array; exists (Ordinal hq); rewrite /aget hqp.
Qed.

End SubsetBridge.

(* -------------------------------------------------------------------------- *)
(* The merge-based difference [L.diff]; only its coverage is needed           *)
(* -------------------------------------------------------------------------- *)

Section DiffBridge.

Context (a b : array int).

Local Notation la := (alen a).
Local Notation lb := (alen b).

#[local] Definition dstep (st : int * int * seq int) : int * int * seq int :=
  let: (i, j, acc) := st in
  if (i <? alength a)%uint63 then
    if (j <? alength b)%uint63 then
      if (a.[i] <? b.[j])%uint63 then ((i + 1)%uint63, j, a.[i] :: acc)
      else if (b.[j] <? a.[i])%uint63 then (i, (j + 1)%uint63, acc)
      else ((i + 1)%uint63, (j + 1)%uint63, acc)
    else ((i + 1)%uint63, j, a.[i] :: acc)
  else (i, j, acc).

Lemma diffE :
  L.diff Uint63.ltb a b = (iter (la + lb)%N dstep (0%uint63, 0%uint63, [::])).2.
Proof.
rewrite /L.diff; cbv zeta; rewrite ifoldE; cbv beta.
by rewrite foldl_const size_iota -[length a]/(alength a) -[length b]/(alength b) alen_add.
Qed.

(* Every consumed entry of [a] has been output, or occurs in [b]. *)
#[local] Definition dinv (st : int * int * seq int) :=
  let: (i, j, acc) := st in
  [/\ nat_of_int i <= la, nat_of_int j <= lb &
      forall p, p < nat_of_int i ->
        nat_of_int a.[int_of_nat p] \in map nat_of_int acc
        \/ exists q, q < lb /\ b.[int_of_nat q] = a.[int_of_nat p]].

#[local] Definition dlive (st : int * int * seq int) := let: (i, _, _) := st in nat_of_int i < la.
#[local] Definition dphi (st : int * int * seq int) :=
  let: (i, j, _) := st in (nat_of_int i + nat_of_int j)%N.

Lemma dstep_inv st : dinv st -> dinv (dstep st).
Proof.
case: st => [[i j] acc] [hi hj hpre]; rewrite /dstep.
case: ifP => [hia|_] /=; last by split.
move: hia; rewrite ltb_alenE => hia.
have hSi : nat_of_int (i + 1)%uint63 = (nat_of_int i).+1.
  by apply: (add1_natE (j := alength a)); rewrite ltb_alenE.
have hout p : p < (nat_of_int i).+1 ->
    nat_of_int a.[int_of_nat p] \in map nat_of_int (a.[i] :: acc)
    \/ exists q, q < lb /\ b.[int_of_nat q] = a.[int_of_nat p].
  rewrite ltnS leq_eqVlt => /orP[/eqP->|/hpre [h|h]]; [left|left|by right].
    by rewrite nat_of_intK /= in_cons eqxx.
  by rewrite /= in_cons h orbT.
case: ifP => [hjb|_] /=; last by split; rewrite ?hSi.
move: hjb; rewrite ltb_alenE => hjb.
have hSj : nat_of_int (j + 1)%uint63 = (nat_of_int j).+1.
  by apply: (add1_natE (j := alength b)); rewrite ltb_alenE.
case: ifP => hab /=; first by split; rewrite ?hSi.
case: ifP => hba /=; first by split; rewrite ?hSj.
split; rewrite ?hSi ?hSj // => p; rewrite ltnS leq_eqVlt => /orP[/eqP->|/hpre//].
right; exists (nat_of_int j); split=> //; rewrite !nat_of_intK.
apply: nat_of_int_inj; apply/eqP.
by rewrite eqn_leq leqNgt -ltb_natE hab leqNgt -ltb_natE hba.
Qed.

Lemma dlive_phi st : dlive st -> (dphi st).+1 <= dphi (dstep st).
Proof.
case: st => [[i j] acc]; rewrite /dlive /dphi /dstep => hia.
have hia' : (i <? alength a)%uint63 by rewrite ltb_alenE.
have hSi : nat_of_int (i + 1)%uint63 = (nat_of_int i).+1 by apply: (add1_natE (j := alength a)).
rewrite hia'; case: ifP => [hjb|_] /=; last by rewrite hSi addSn leqnn.
have hSj : nat_of_int (j + 1)%uint63 = (nat_of_int j).+1 by apply: (add1_natE (j := alength b)).
case: ifP => _ /=; first by rewrite hSi addSn leqnn.
by case: ifP => _ /=; rewrite ?hSi ?hSj ?addSn ?addnS ?leqnn ?leqnSn.
Qed.

Lemma dnlive_fix st : ~~ dlive st -> dstep st = st.
Proof. by case: st => [[i j] acc]; rewrite /dlive /dstep ltb_alenE => /negbTE ->. Qed.

Lemma dlive_step st : dlive (dstep st) -> dlive st.
Proof. by case hn: (dlive st) => // hl; rewrite (dnlive_fix (negbT hn)) hn in hl. Qed.

Lemma dlive_iter k st : dlive (iter k dstep st) -> (dphi st + k)%N <= dphi (iter k dstep st).
Proof.
elim: k => [|k ih]; first by rewrite addn0.
rewrite iterS => hl; have hk := dlive_step hl.
by rewrite addnS (leq_trans _ (dlive_phi hk)) // ltnS ih.
Qed.

Lemma diff_arr_all : forall p, p < la ->
  nat_of_int a.[int_of_nat p] \in map nat_of_int (L.diff Uint63.ltb a b)
  \/ exists q, q < lb /\ b.[int_of_nat q] = a.[int_of_nat p].
Proof.
rewrite diffE; set st0 := (0%uint63, 0%uint63, [::] : seq int).
have hinv k : dinv (iter k dstep st0).
  elim: k => [|k ih]; last by rewrite iterS; exact: dstep_inv.
  by split; rewrite ?nat_of_int0 // => p; rewrite ltn0.
move: (hinv (la + lb)%N); case E: (iter _ dstep st0) => [[i j] acc] [hi hj hpre] p hp.
have hiN : nat_of_int i = la.
  apply/eqP; rewrite eqn_leq hi andTb leqNgt; apply/negP => hia.
  have := dlive_iter (k := (la + lb)%N) (st := st0); rewrite E => /(_ hia).
  rewrite /dphi /st0 !nat_of_int0 add0n => hge.
  have := leq_add hia hj; rewrite addSn => hlt.
  by rewrite ltnNge hge in hlt.
by apply: hpre; rewrite hiN.
Qed.

(* [isRidgeInFacet a b v]: [a] minus [v] is covered by [b]. *)
Lemma isRidgeInFacet_sub (v : int) : L.isRidgeInFacet a b v ->
  forall p, p < la -> nat_of_int a.[int_of_nat p] = nat_of_int v
    \/ exists q, q < lb /\ b.[int_of_nat q] = a.[int_of_nat p].
Proof.
rewrite /L.isRidgeInFacet => hr p hp; have [hin|hex] := diff_arr_all hp; last by right.
left; move: hr hin; case: (L.diff Uint63.ltb a b) => [|x [|y l]] //=.
by rewrite eqb_natE in_cons in_nil orbF => /eqP -> /eqP.
Qed.

End DiffBridge.

Lemma ridge_subset m (a b : array int) (v : int) (i : 'I_m) : nat_of_int v = i ->
  L.isRidgeInFacet a b v -> set_of_array m a :\ i \subset set_of_array m b.
Proof.
move=> hv hr; apply/subsetP => x /setD1P[hxi /in_set_of_array[p hp]].
have [heq|[q [hq hqp]]] := isRidgeInFacet_sub hr (ltn_ord p).
  have hxi' : x = i by apply/val_inj => /=; rewrite -hp -hv /aget.
  by rewrite hxi' eqxx in hxi.
by apply/in_set_of_array; exists (Ordinal hq); rewrite /aget hqp.
Qed.

(* Nested traversals, used by the root and full-dimension checks. *)

Lemma ifold_andP (P : int -> bool) M :
  reflect (forall i : 'I_(nat_of_int M), P (int_of_nat i))
          (L.ifold (fun i acc => acc && P i) M true).
Proof. by rewrite ifoldE; cbv beta; rewrite foldl_andb andTb; exact: all_iotaP. Qed.

Lemma for_alli_matrixP T (f : int -> int -> T -> bool) (a : array (array T)) :
  reflect (forall i : 'I_(alen a), forall j : 'I_(alen (aget a i)),
             f (int_of_nat i) (int_of_nat j) (aget (aget a i) j))
          (L.for_alli_matrix f a).
Proof.
rewrite /L.for_alli_matrix; apply: (iffP (for_alli_alenP _ _)) => h i; have := h i; cbv beta.
  by move/for_alli_alenP.
by move=> hi; apply/for_alli_alenP.
Qed.

Lemma ifor_all_range0P (f : int -> bool) n :
  reflect (forall i : 'I_(nat_of_int n), f (int_of_nat i)) (L.ifor_all_range0 f n).
Proof. exact: ifold_andP. Qed.
