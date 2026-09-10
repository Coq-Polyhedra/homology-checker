(* -------------------------------------------------------------------------- *)
(* Bridges between the vocabulary of the executable checker (LowLevelChecker) *)
(* and mathcomp: Uint63 <-> nat, iteration <-> folds and quantifiers,         *)
(* bigZ <-> a realFieldType, arrays <-> vectors, sorted int arrays <-> finite *)
(* sets, the merge-based subset/difference/lexicographic tests, the binary   *)
(* search [L.mem_sorted], the two-level [BigArray] tables holding the         *)
(* index-keyed certificate data, and the [IntList] tests on strictly          *)
(* decreasing sequences.                                                      *)
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
From Cert Require BigArray LowLevelChecker.

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

Lemma nat_of_int1 : nat_of_int 1%uint63 = 1%N.
Proof. by rewrite nat_of_intE. Qed.

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

Lemma isStrictlySorted_leq (a : array int) : L.isStrictlySorted Uint63.ltb a ->
  forall j1 j2, j1 <= j2 -> j2 < alen a ->
    nat_of_int a.[int_of_nat j1] <= nat_of_int a.[int_of_nat j2].
Proof.
move=> hs j1 j2; rewrite leq_eqVlt => /orP[/eqP->|hlt] hj2; first exact: leqnn.
exact: ltnW (isStrictlySorted_mono hs hlt hj2).
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

Lemma add1_alenE T (a : array T) (i : int) : (nat_of_int i < alen a)%N ->
  nat_of_int (i + 1)%uint63 = (nat_of_int i).+1.
Proof. by rewrite -ltb_alenE; exact: add1_natE. Qed.

Lemma alen_set T (a : array T) (i : int) (x : T) : alen a.[i <- x] = alen a.
Proof. by rewrite /alen /alength PArray.length_set. Qed.

Lemma alen_make T (k : int) (x : T) :
  (k <=? PArray.max_length)%uint63 -> alen (PArray.make k x) = nat_of_int k.
Proof. by move=> h; rewrite /alen /alength PArray.length_make h. Qed.

Lemma foldl_const (A B : Type) (g : A -> A) (x : A) (s : seq B) :
  foldl (fun acc _ => g acc) x s = iter (size s) g x.
Proof. by elim: s x => [|y s ih] x //=; rewrite ih -iterSr. Qed.

(* -------------------------------------------------------------------------- *)
(* Generic iteration corollaries: accumulating folds, and [Prop] invariants   *)
(* carried through [iter] and [L.fold]                                        *)
(* -------------------------------------------------------------------------- *)

Lemma foldl_cons_rev (I A : Type) (f : I -> A) acc0 (s : seq I) :
  foldl (fun acc x => f x :: acc) acc0 s = rev (map f s) ++ acc0.
Proof. by elim: s acc0 => [|x s ih] acc0 //=; rewrite ih rev_cons cat_rcons. Qed.

(* Position [n - j.+1] of the reversed [iota]-map is the image of [j]. *)
Lemma nth_rev_map_iota (A : Type) (f : nat -> A) x0 n (j : nat) : j < n ->
  nth x0 (rev [seq f i | i <- iota 0 n]) (n - j.+1) = f j.
Proof.
move=> hj; rewrite nth_rev size_map size_iota; last first.
  by rewrite ltn_subrL /=; exact: leq_ltn_trans (leq0n _) hj.
rewrite (subnSK hj) subKn ?(ltnW hj) //.
by rewrite (nth_map 0) ?size_iota // nth_iota // add0n.
Qed.

(* Accumulating [fold]: the results, most recent first. *)
Lemma fold_consE (T A : Type) (f : T -> A) (arr : array T) :
  L.fold (fun x acc => f x :: acc) arr [::]
  = rev [seq f arr.[int_of_nat j] | j <- iota 0 (alen arr)].
Proof.
rewrite /L.fold ifoldE; cbv beta.
by rewrite (foldl_cons_rev (fun j => f arr.[int_of_nat j])) cats0
   -[nat_of_int (length arr)]/(alen arr).
Qed.

Lemma iter_inv (T : Type) (P : T -> Prop) (f : T -> T) (x : T) :
  P x -> (forall y, P y -> P (f y)) -> forall k, P (iter k f x).
Proof. by move=> h0 hs; elim=> [|k ih] //=; apply: hs. Qed.

Lemma iter_ind (T : Type) (P : nat -> T -> Prop) (f : T -> T) (x : T) :
  P 0 x -> (forall k y, P k y -> P k.+1 (f y)) -> forall k, P k (iter k f x).
Proof. by move=> h0 hs; elim=> [|k ih] //=; apply: hs. Qed.

Lemma fold_invariantP (T A : Type) (P : A -> Prop) (f : T -> A -> A) (a : array T) (x : A) :
  P x -> (forall (i : 'I_(alen a)) (y : A), P y -> P (f (aget a i) y)) ->
  P (L.fold f a x).
Proof.
move=> h0 hs; rewrite /L.fold ifoldE; cbv beta.
rewrite -[nat_of_int (PArray.length a)]/(alen a).
have: forall j, j \in iota 0 (alen a) -> (j < alen a)%N.
  by move=> j; rewrite mem_iota add0n.
elim: (iota 0 (alen a)) x h0 => [|j js ih] x h0 hall //=.
apply: ih; last by move=> j' hj'; apply: hall; rewrite inE hj' orbT.
have hj : (j < alen a)%N by apply: hall; rewrite inE eqxx.
exact: (hs (Ordinal hj)).
Qed.

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
  by apply: (add1_alenE (a := b)).
have hSi : nat_of_int (i + 1)%uint63 = (nat_of_int i).+1.
  by apply: (add1_alenE (a := a)).
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
have h00 : sinv st0 by split; rewrite ?nat_of_int0 // => p; rewrite ltn0.
have hinv := iter_inv h00 sstep_inv.
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
(* The merge-based difference [L.diff]: coverage for arbitrary arrays, and,   *)
(* for strictly sorted inputs, exact membership and strictly decreasing       *)
(* output                                                                     *)
(* -------------------------------------------------------------------------- *)

(* The strictly decreasing order on naturals, the shape of [L.diff] outputs. *)
Local Notation gtns := (fun x y : nat => (y < x)%N).

Lemma gtns_trans : transitive gtns.
Proof. by move=> y x z hxy hyz; exact: ltn_trans hyz hxy. Qed.

Lemma gtns_head (x : int) (s : seq int) :
  sorted gtns (map nat_of_int (x :: s)) ->
  forall z, z \in map nat_of_int s -> (z < nat_of_int x)%N.
Proof.
move=> /= hs z hz.
have hall : all (gtns (nat_of_int x)) (map nat_of_int s).
  exact: order_path_min gtns_trans hs.
exact: (allP hall _ hz).
Qed.

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
  by apply: (add1_alenE (a := a)).
have hout p : p < (nat_of_int i).+1 ->
    nat_of_int a.[int_of_nat p] \in map nat_of_int (a.[i] :: acc)
    \/ exists q, q < lb /\ b.[int_of_nat q] = a.[int_of_nat p].
  rewrite ltnS leq_eqVlt => /orP[/eqP->|/hpre [h|h]]; [left|left|by right].
    by rewrite nat_of_intK /= in_cons eqxx.
  by rewrite /= in_cons h orbT.
case: ifP => [hjb|_] /=; last by split; rewrite ?hSi.
move: hjb; rewrite ltb_alenE => hjb.
have hSj : nat_of_int (j + 1)%uint63 = (nat_of_int j).+1.
  by apply: (add1_alenE (a := b)).
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
have h00 : dinv st0 by split; rewrite ?nat_of_int0 // => p; rewrite ltn0.
have hinv := iter_inv h00 dstep_inv.
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


(* With both inputs strictly sorted: every output entry is an entry of [a]
   absent from [b] ([diff_arr_mem]), the output is strictly decreasing
   ([diff_sorted]); coverage is [diff_arr_all] above. *)
#[local] Definition dinv2 (st : int * int * seq int) :=
  let: (i, j, acc) := st in
  [/\ nat_of_int i <= la, nat_of_int j <= lb &
      forall x, x \in map nat_of_int acc ->
        exists p, p < nat_of_int i /\ nat_of_int a.[int_of_nat p] = x]
  /\
  [/\ forall x, x \in map nat_of_int acc ->
        forall p, nat_of_int i <= p -> p < la -> x < nat_of_int a.[int_of_nat p],
      forall x, x \in map nat_of_int acc ->
        forall q, q < lb -> nat_of_int b.[int_of_nat q] <> x,
      (forall q, q < nat_of_int j ->
        forall p, nat_of_int i <= p -> p < la ->
          nat_of_int b.[int_of_nat q] < nat_of_int a.[int_of_nat p]) &
      sorted gtns (map nat_of_int acc)].

#[local] Lemma dstep_inv2 st :
  L.isStrictlySorted Uint63.ltb a -> L.isStrictlySorted Uint63.ltb b ->
  dinv2 st -> dinv2 (dstep st).
Proof.
move=> hsa hsb; have hma := isStrictlySorted_mono hsa; have hmb := isStrictlySorted_mono hsb.
case: st => [[i j] acc] [[hi hj hsrc] [hbelow hnotb hbcons hsorted]]; rewrite /dstep.
case: ifP => [hia|_] /=; last by split; [split | split].
move: hia; rewrite ltb_alenE => hia.
have hSi : nat_of_int (i + 1)%uint63 = (nat_of_int i).+1.
  by apply: (add1_alenE (a := a)).
(* [a.[i]], nat-indexed *)
have hEi : nat_of_int a.[int_of_nat (nat_of_int i)] = nat_of_int a.[i] by rewrite nat_of_intK.
have hai_lt : forall p, (nat_of_int i < p)%N -> p < la ->
    (nat_of_int a.[i] < nat_of_int a.[int_of_nat p])%N.
  by move=> p hip hpla; rewrite -hEi; exact: (hma _ _ hip hpla).
have hai_le : forall p, nat_of_int i <= p -> p < la ->
    nat_of_int a.[i] <= nat_of_int a.[int_of_nat p].
  move=> p hip hpla; rewrite -hEi.
  by have h := isStrictlySorted_leq hsa hip hpla; exact: h.
have hbi : forall q, q < nat_of_int j -> (nat_of_int b.[int_of_nat q] < nat_of_int a.[i])%N.
  by move=> q hq; rewrite -hEi; exact: (hbcons _ hq _ (leqnn _) hia).
(* obligations shared by the two pushing branches *)
have hsrc' : forall x, x \in map nat_of_int (a.[i] :: acc) ->
    exists p, p < (nat_of_int i).+1 /\ nat_of_int a.[int_of_nat p] = x.
  move=> x; rewrite /= in_cons => /orP[/eqP->|/hsrc [p [hp hpx]]].
    by exists (nat_of_int i); split; [exact: leqnn | exact: hEi].
  by exists p; split=> //; rewrite ltnS (ltnW hp).
have hbelow' : forall x, x \in map nat_of_int (a.[i] :: acc) ->
    forall p, (nat_of_int i).+1 <= p -> p < la -> (x < nat_of_int a.[int_of_nat p])%N.
  move=> x; rewrite /= in_cons => /orP[/eqP->|hx] p hip hpla.
    exact: (hai_lt _ hip hpla).
  exact: (hbelow _ hx _ (ltnW hip) hpla).
have hbcons' : forall q, q < nat_of_int j ->
    forall p, (nat_of_int i).+1 <= p -> p < la ->
      (nat_of_int b.[int_of_nat q] < nat_of_int a.[int_of_nat p])%N.
  by move=> q hq p hip hpla; exact: (hbcons _ hq _ (ltnW hip) hpla).
have hsort' : sorted gtns (map nat_of_int (a.[i] :: acc)).
  rewrite /=; move: hsorted; case hacc: (map nat_of_int acc) => [|h t] //= hsorted.
  have hh : h \in map nat_of_int acc by rewrite hacc mem_head.
  have hlt := hbelow _ hh _ (leqnn _) hia; rewrite hEi in hlt.
  by rewrite hsorted andbT.
case: ifP => [hjb|hjb'] /=; last first.
  (* b exhausted: push a.[i] *)
  have hjlb : lb <= nat_of_int j.
    by rewrite leqNgt; apply/negP => h; rewrite ltb_alenE h in hjb'.
  split; [split; rewrite ?hSi // | split; rewrite ?hSi //] => x hx q hq.
  move: hx; rewrite /= in_cons => /orP[/eqP->|hx]; last exact: (hnotb _ hx _ hq).
  by move=> he; have h2 := hbi _ (leq_trans hq hjlb); rewrite he ltnn in h2.
move: hjb; rewrite ltb_alenE => hjb.
have hSj : nat_of_int (j + 1)%uint63 = (nat_of_int j).+1.
  by apply: (add1_alenE (a := b)).
have hEj : nat_of_int b.[int_of_nat (nat_of_int j)] = nat_of_int b.[j] by rewrite nat_of_intK.
case: ifP => hab /=.
  (* a.[i] < b.[j]: push a.[i] *)
  move: (hab); rewrite ltb_natE => hab'.
  have hbj_le : forall q, nat_of_int j <= q -> q < lb ->
      nat_of_int b.[j] <= nat_of_int b.[int_of_nat q].
    move=> q hjq hqlb; rewrite -hEj.
    by have h := isStrictlySorted_leq hsb hjq hqlb; exact: h.
  split; [split; rewrite ?hSi // | split; rewrite ?hSi //] => x hx q hq.
  move: hx; rewrite /= in_cons => /orP[/eqP->|hx]; last exact: (hnotb _ hx _ hq).
  move=> he.
  case hqj: (q < nat_of_int j)%N.
    by have h2 := hbi _ hqj; rewrite he ltnn in h2.
  have hjq : nat_of_int j <= q by rewrite leqNgt hqj.
  by have h2 := leq_trans hab' (hbj_le _ hjq hq); rewrite he ltnn in h2.
case: ifP => hba /=.
  (* b.[j] < a.[i]: skip b.[j] *)
  move: (hba); rewrite ltb_natE => hba'.
  split; [split; rewrite ?hSj // | split=> //] => q; rewrite hSj ltnS leq_eqVlt.
  move=> /orP[/eqP->|hq] p hip hpla; last exact: (hbcons _ hq _ hip hpla).
  by rewrite hEj; exact: leq_trans hba' (hai_le _ hip hpla).
(* equal heads: skip both *)
have he : nat_of_int b.[j] = nat_of_int a.[i].
  by apply/eqP; rewrite eqn_leq leqNgt -ltb_natE hab leqNgt -ltb_natE hba.
split; [split; rewrite ?hSi ?hSj // | split; rewrite ?hSi ?hSj //].
- by move=> x /hsrc [p [hp hpx]]; exists p; split=> //; rewrite ltnS (ltnW hp).
- by move=> x hx p hip hpla; exact: (hbelow _ hx _ (ltnW hip) hpla).
move=> q; rewrite ltnS leq_eqVlt => /orP[/eqP->|hq] p hip hpla.
  by rewrite hEj he; exact: (hai_lt _ hip hpla).
exact: (hbcons _ hq _ (ltnW hip) hpla).
Qed.

#[local] Lemma dinv2_iter k :
  L.isStrictlySorted Uint63.ltb a -> L.isStrictlySorted Uint63.ltb b ->
  dinv2 (iter k dstep (0%uint63, 0%uint63, [::])).
Proof.
move=> hsa hsb.
have h00 : dinv2 (0%uint63, 0%uint63, [::]).
  split; first by split; rewrite ?nat_of_int0 //=.
  by split; rewrite ?nat_of_int0 ?ltn0 //=.
by have h := iter_inv h00 (fun st => dstep_inv2 (st := st) hsa hsb) k; exact: h.
Qed.

Lemma diff_arr_mem :
  L.isStrictlySorted Uint63.ltb a -> L.isStrictlySorted Uint63.ltb b ->
  forall x, x \in map nat_of_int (L.diff Uint63.ltb a b) ->
    (exists p, p < la /\ nat_of_int a.[int_of_nat p] = x) /\
    (forall q, q < lb -> nat_of_int b.[int_of_nat q] <> x).
Proof.
move=> hsa hsb; rewrite diffE.
move: (dinv2_iter (la + lb)%N hsa hsb).
case: (iter _ dstep _) => [[i j] acc] [[hi _ hsrc] [_ hnotb _ _]] x hx.
split; last exact: (hnotb _ hx).
have [p [hp hpx]] := hsrc x hx; exists p; split=> //; exact: leq_trans hp hi.
Qed.

Lemma diff_sorted :
  L.isStrictlySorted Uint63.ltb a -> L.isStrictlySorted Uint63.ltb b ->
  sorted gtns (map nat_of_int (L.diff Uint63.ltb a b)).
Proof.
move=> hsa hsb; rewrite diffE.
move: (dinv2_iter (la + lb)%N hsa hsb).
by case: (iter _ dstep _) => [[i j] acc] [_ [_ _ _ hsorted]].
Qed.

End DiffBridge.

(* -------------------------------------------------------------------------- *)
(* Ridges at the set level, and nested traversals                             *)
(* -------------------------------------------------------------------------- *)


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

Lemma for_all_range0P T (f : T -> bool) (a : array T) (n : int) :
  reflect (forall i : 'I_(nat_of_int n), f (aget a i)) (L.for_all_range0 f a n).
Proof. rewrite /L.for_all_range0; exact: ifor_all_range0P. Qed.

(* -------------------------------------------------------------------------- *)
(* The two-level arrays [BigArray.array]: the index-keyed tables              *)
(*                                                                            *)
(* The certificate stores every table whose length is a number of facets or   *)
(* of vertices ([facets], [graph], [vertices], [geom_graph], the geometric    *)
(* edge tables) as a [BigArray.array], since those can exceed                 *)
(* [PArray.max_length]. The checker iterates over them with the index-based   *)
(* [b*] combinators, which are [ifold]/[ifor_all_range0] over                 *)
(* [BigArray.length]/[BigArray.get]. Every bridge below therefore reduces to  *)
(* the corresponding [ifold] bridge above, and its statement mirrors the      *)
(* [PArray] one with [balen]/[baget] on the outer table. Inner rows stay      *)
(* [PArray] arrays, hence keep [alen]/[aget].                                 *)
(*                                                                            *)
(* [BigArray.array] lives at the single declared universe [barr], so the      *)
(* anchoring discipline behind [alength]/[alen] is not needed here; the same  *)
(* wrapper style is kept for uniformity (and so that lengths are read as      *)
(* naturals everywhere).                                                      *)
(* -------------------------------------------------------------------------- *)

Section BigArrayBridge.

Definition blength {T} (t : BigArray.array T) : int := BigArray.length t.
Arguments blength : simpl never.
Definition balen {T} (t : BigArray.array T) : nat := nat_of_int (blength t).
Arguments balen : simpl never.

(* Unlike [aget], indexed by naturals: the ordinal is recovered by the
   coercion at every use site ([baget t i] for [i : 'I_(balen t)]), and the
   [nat_of_int] spelling of a checker index stays readable. *)
Definition baget {T} (t : BigArray.array T) (i : nat) : T := BigArray.get t (int_of_nat i).

Lemma blengthE T (t : BigArray.array T) : BigArray.length t = blength t.
Proof. by []. Qed.

Lemma balenE T (t : BigArray.array T) : nat_of_int (BigArray.length t) = balen t.
Proof. by []. Qed.

Lemma bagetE T (t : BigArray.array T) (i : nat) : BigArray.get t (int_of_nat i) = baget t i.
Proof. by []. Qed.

Lemma baget_natE T (t : BigArray.array T) (x : int) : baget t (nat_of_int x) = BigArray.get t x.
Proof. by rewrite /baget nat_of_intK. Qed.

(* Arithmetic on big lengths, as for [alen] (bound: [2^43 - 2^21]). *)
Lemma balen_bound T (t : BigArray.array T) :
  (Z.of_nat (balen t) <= to_Z BigArray.max_length)%Z.
Proof. by rewrite /balen -to_Z_nat_of_int; apply/Uint63.lebP; exact: BigArray.leb_length. Qed.

Lemma ltb_balenE T (t : BigArray.array T) i : (i <? blength t)%uint63 = (nat_of_int i < balen t).
Proof. by rewrite ltb_natE. Qed.

Lemma add1_balenE T (t : BigArray.array T) (i : int) : (nat_of_int i < balen t)%N ->
  nat_of_int (i + 1)%uint63 = (nat_of_int i).+1.
Proof. by rewrite -ltb_balenE; exact: add1_natE. Qed.

(* Spelled with [BigArray.length] on the left: this is the form the checker's
   length conjuncts have. *)
Lemma eqb_balenE T1 T2 (t1 : BigArray.array T1) (t2 : BigArray.array T2) :
  (BigArray.length t1 =? BigArray.length t2)%uint63 = (balen t1 == balen t2).
Proof. by rewrite eqb_natE !balenE. Qed.

Lemma balen_set T (t : BigArray.array T) (i : int) (x : T) :
  balen (BigArray.set t i x) = balen t.
Proof. by rewrite /balen /blength BigArray.length_set. Qed.

Lemma balen_make T (k : int) (x : T) :
  (k <=? BigArray.max_length)%uint63 -> balen (BigArray.make k x) = nat_of_int k.
Proof. by move=> h; rewrite /balen /blength BigArray.length_make h. Qed.

(* Iteration bridges: the exact counterparts of [for_allP]/[for_alliP]. *)
Lemma bfor_allP T (f : T -> bool) (t : BigArray.array T) n : balen t = n ->
  reflect (forall i : 'I_n, f (baget t i)) (L.bfor_all f t).
Proof.
move=> <-; rewrite /balen /L.bfor_all /L.ifor_all_range0 ifoldE /= foldl_andb /=.
exact: all_iotaP.
Qed.

Lemma bfor_alliP T (f : int -> T -> bool) (t : BigArray.array T) n : balen t = n ->
  reflect (forall i : 'I_n, f (int_of_nat i) (baget t i)) (L.bfor_alli f t).
Proof.
move=> <-; rewrite /balen /L.bfor_alli /L.ifor_all_range0 ifoldE /= foldl_andb /=.
exact: all_iotaP.
Qed.

Lemma bfor_all_composeP A B (f : B -> bool) (g : A -> B) (t : BigArray.array A) n :
  balen t = n -> reflect (forall i : 'I_n, f (g (baget t i))) (L.bfor_all_compose f g t).
Proof. move=> h; have h2 := bfor_allP (Basics.compose f g) h; exact: h2. Qed.

(* Outer big, inner [PArray]: the inner quantification keeps [alen]/[aget]. *)
Lemma bfor_all_matrixP T (f : T -> bool) (t : BigArray.array (array T)) n : balen t = n ->
  reflect (forall (i : 'I_n) (j : 'I_(alen (baget t i))), f (aget (baget t i) j))
          (L.bfor_all_matrix f t).
Proof.
move=> hn; rewrite /L.bfor_all_matrix.
apply: (iffP (bfor_allP _ hn)) => h i; have := h i; cbv beta.
  by move/for_all_alenP.
by move=> hi; apply/for_all_alenP.
Qed.

Lemma bfor_alli_matrixP T (f : int -> int -> T -> bool) (t : BigArray.array (array T)) n :
  balen t = n ->
  reflect (forall (i : 'I_n) (j : 'I_(alen (baget t i))),
             f (int_of_nat i) (int_of_nat j) (aget (baget t i) j))
          (L.bfor_alli_matrix f t).
Proof.
move=> hn; rewrite /L.bfor_alli_matrix.
apply: (iffP (bfor_alliP _ hn)) => h i; have := h i; cbv beta.
  by move/for_alli_alenP.
by move=> hi; apply/for_alli_alenP.
Qed.

(* The same reflections with the length pre-instantiated to [balen t]. *)
Lemma bfor_all_balenP T (f : T -> bool) (t : BigArray.array T) :
  reflect (forall i : 'I_(balen t), f (baget t i)) (L.bfor_all f t).
Proof. by apply: bfor_allP. Qed.

Lemma bfor_alli_balenP T (f : int -> T -> bool) (t : BigArray.array T) :
  reflect (forall i : 'I_(balen t), f (int_of_nat i) (baget t i)) (L.bfor_alli f t).
Proof. by apply: bfor_alliP. Qed.

Lemma bfor_all_compose_balenP A B (f : B -> bool) (g : A -> B) (t : BigArray.array A) :
  reflect (forall i : 'I_(balen t), f (g (baget t i))) (L.bfor_all_compose f g t).
Proof. by apply: bfor_all_composeP. Qed.

Lemma bfor_all_matrix_balenP T (f : T -> bool) (t : BigArray.array (array T)) :
  reflect (forall (i : 'I_(balen t)) (j : 'I_(alen (baget t i))), f (aget (baget t i) j))
          (L.bfor_all_matrix f t).
Proof. by apply: bfor_all_matrixP. Qed.

Lemma bfor_alli_matrix_balenP T (f : int -> int -> T -> bool) (t : BigArray.array (array T)) :
  reflect (forall (i : 'I_(balen t)) (j : 'I_(alen (baget t i))),
             f (int_of_nat i) (int_of_nat j) (aget (baget t i) j))
          (L.bfor_alli_matrix f t).
Proof. by apply: bfor_alli_matrixP. Qed.

(* Folds and the counter, as [foldl]/[count] over [iota 0 (balen t)]. *)
Lemma bfoldE T A (f : T -> A -> A) (t : BigArray.array T) (x0 : A) :
  L.bfold f t x0 = foldl (fun acc j => f (baget t j) acc) x0 (iota 0 (balen t)).
Proof. by rewrite /L.bfold ifoldE. Qed.

Lemma bfoldiE T A (f : int -> T -> A -> A) (t : BigArray.array T) (x0 : A) :
  L.bfoldi f t x0 = foldl (fun acc j => f (int_of_nat j) (baget t j) acc) x0 (iota 0 (balen t)).
Proof. by rewrite /L.bfoldi ifoldE. Qed.

(* The running maximum [L.int_max]: the fold's result is one of the inputs and
   bounds all of them. *)
Lemma int_max_ge (d acc : int) :
  (nat_of_int acc <= nat_of_int (L.int_max d acc))
  /\ (nat_of_int d <= nat_of_int (L.int_max d acc)).
Proof.
rewrite /L.int_max; case: ifP; rewrite ltb_natE => h.
- by split; [exact: ltnW | exact: leqnn].
- by split; [exact: leqnn | rewrite leqNgt h].
Qed.

Lemma int_max_in (d acc : int) :
  nat_of_int (L.int_max d acc) \in [:: nat_of_int d; nat_of_int acc].
Proof. by rewrite /L.int_max; case: ifP => _; rewrite !inE eqxx ?orbT. Qed.

(* Stated on the natural values: [int] carries no [eqType] here. *)
Lemma foldl_int_max (s : seq int) (x0 : int) :
  let r := foldl (fun acc d => L.int_max d acc) x0 s in
  nat_of_int r \in map nat_of_int (x0 :: s)
  /\ forall y, y \in map nat_of_int (x0 :: s) -> y <= nat_of_int r.
Proof.
elim: s x0 => [|d s ih] x0 /=.
  by split=> [|y]; rewrite inE // => /eqP ->.
have [hin hge] := ih (L.int_max d x0); split.
  move: hin; rewrite inE => /orP[/eqP ->|hs].
    by have := int_max_in d x0; rewrite !inE => /orP[] /eqP ->; rewrite eqxx ?orbT.
  by rewrite !inE hs !orbT.
move=> y; rewrite !inE => /or3P[/eqP ->|/eqP ->|hs].
- by apply: (leq_trans (proj1 (int_max_ge d x0))); apply: hge; rewrite inE eqxx.
- by apply: (leq_trans (proj2 (int_max_ge d x0))); apply: hge; rewrite inE eqxx.
- by apply: hge; rewrite inE hs orbT.
Qed.

(* The running maximum over a big table of ints. *)
Lemma bfold_int_max_ge (t : BigArray.array int) (v : 'I_(balen t)) :
  nat_of_int (baget t v) <= nat_of_int (L.bfold L.int_max t 0%uint63).
Proof.
rewrite bfoldE -(foldl_map (baget t) (fun acc d => L.int_max d acc)).
have [_ hge] := foldl_int_max (map (baget t) (iota 0 (balen t))) 0%uint63.
apply: hge; rewrite map_cons -map_comp inE; apply/orP; right.
by apply/mapP; exists (nat_of_ord v); last by []; rewrite mem_iota add0n ltn_ord.
Qed.

Lemma bfold_int_max_in (t : BigArray.array int) :
  nat_of_int (L.bfold L.int_max t 0%uint63) = 0
  \/ exists v : 'I_(balen t), nat_of_int (baget t v) = nat_of_int (L.bfold L.int_max t 0%uint63).
Proof.
rewrite bfoldE -(foldl_map (baget t) (fun acc d => L.int_max d acc)).
have [hin _] := foldl_int_max (map (baget t) (iota 0 (balen t))) 0%uint63.
move: hin; rewrite map_cons -map_comp inE => /orP[/eqP ->|/mapP[j hj ->]].
  by left; rewrite nat_of_int0.
move: hj; rewrite mem_iota add0n => /andP[_ hj].
by right; exists (Ordinal hj).
Qed.

Lemma bcountiE T (P : int -> T -> bool) (t : BigArray.array T) :
  nat_of_int (L.bcounti P t)
  = count (fun j => P (int_of_nat j) (baget t j)) (iota 0 (balen t)).
Proof.
rewrite /L.bcounti bfoldiE (@foldl_count_int _ _ _ (blength t)) ?nat_of_int0 ?add0n //.
by rewrite size_iota -[nat_of_int (blength t)]/(balen t) leqnn.
Qed.

(* Strict sortedness of a big table, consecutive entries first. *)
Lemma bisStrictlySorted_consecT T (ltT : T -> T -> bool) (t : BigArray.array T) :
  L.bisStrictlySorted ltT t ->
  forall (k k' : 'I_(balen t)), k' = k.+1 :> nat -> ltT (baget t k) (baget t k').
Proof.
rewrite /L.bisStrictlySorted => /bfor_alli_balenP h k k' hk'.
have hk : k.+1 < balen t by rewrite -hk'; exact: ltn_ord.
have hkk : nat_of_int (int_of_nat k) = k.
  by apply: (int_of_natK_le (i := blength t)); exact: ltnW.
have := h k; cbv beta; rewrite /L.bcompareConsecutive leb_natE hkk.
rewrite sub1_natE; last by exact: leq_ltn_trans hk.
rewrite balenE leqNgt ltn_predRL hk /= (int_of_natS (ltnW hk)).
by rewrite /baget hk'.
Qed.

Lemma bisStrictlySorted_mono (t : BigArray.array int) : L.bisStrictlySorted Uint63.ltb t ->
  forall j1 j2, j1 < j2 -> j2 < balen t ->
    nat_of_int (baget t j1) < nat_of_int (baget t j2).
Proof.
move=> hs; apply: (consec_chain (R := fun x y : nat => (x < y)%N)
                                (E := fun k => nat_of_int (baget t k))
                                (fun x y z => @ltn_trans y x z)).
move=> k hk; cbv beta; rewrite -ltb_natE.
have h := bisStrictlySorted_consecT (k := Ordinal (ltnW hk)) (k' := Ordinal hk) hs erefl.
exact: h.
Qed.

Lemma bisStrictlySorted_leq (t : BigArray.array int) : L.bisStrictlySorted Uint63.ltb t ->
  forall j1 j2, j1 <= j2 -> j2 < balen t ->
    nat_of_int (baget t j1) <= nat_of_int (baget t j2).
Proof.
move=> hs j1 j2; rewrite leq_eqVlt => /orP[/eqP->|hlt] hj2; first exact: leqnn.
exact: ltnW (bisStrictlySorted_mono hs hlt hj2).
Qed.

(* The big counterpart of [sorted_sets_inj]: a big table of records whose
   [PArray] descriptions are strictly sorted and lexicographically increasing
   has pairwise distinct sets of entries. *)
Lemma bsorted_sets_inj T (g : T -> array int) (s : BigArray.array T) n :
  L.bisStrictlySorted (fun x y => L.ltbArray Uint63.eqb Uint63.ltb (g x) (g y)) s ->
  (forall k : 'I_(balen s), L.isStrictlySorted Uint63.ltb (g (baget s k))) ->
  (forall (k : 'I_(balen s)) (j : 'I_(alen (g (baget s k)))),
     nat_of_int (aget (g (baget s k)) j) < n) ->
  injective (fun k : 'I_(balen s) => set_of_array n (g (baget s k))).
Proof.
move=> huniq hsort hrange.
suff hlt : forall k1 k2 : 'I_(balen s), k1 < k2 ->
    set_of_array n (g (baget s k1)) <> set_of_array n (g (baget s k2)).
  move=> k1 k2 heq; apply/val_inj/eqP; rewrite eqn_leq (leqNgt k1 k2) (leqNgt k2 k1).
  apply/andP; split; apply/negP => h.
    by move/hlt: h => h; apply: h; exact: esym heq.
  by move/hlt: h => h; apply: h.
move=> k1 k2 hk12 heq.
pose E (k : nat) := g (baget s k).
pose Rl (x y : array int) :=
  lexlt (fun j => nat_of_int x.[int_of_nat j]) (alen x) (fun j => nat_of_int y.[int_of_nat j]) (alen y).
have hcons k : k.+1 < balen s -> Rl (E k) (E k.+1).
  move=> hk; have hk' : k < balen s := ltnW hk.
  have hl := bisStrictlySorted_consecT (k := Ordinal hk') (k' := Ordinal hk) huniq erefl.
  cbv beta in hl; have hl2 := ltbArray_lexlt hl; exact: hl2.
have hR := consec_chain (R := Rl) (E := E) (fun x y z hxy hyz => lexlt_trans hxy hyz)
             hcons hk12 (ltn_ord k2).
exact: lexlt_sorted_neq (hsort k1) (hsort k2) (hrange k1) (hrange k2) hR heq.
Qed.

(* Entries of a family of [PArray] rows hanging under a big table, all within
   [0, n): the big counterpart of [allInRange_ordP]. *)
Lemma ballInRange_ordP T (g : T -> array int) (s : BigArray.array T) (n : int)
    (k : 'I_(balen s)) :
  (0 < nat_of_int n)%N ->
  L.bfor_all_compose (L.allInRange Uint63.leb 0%uint63 (n - 1)%uint63) g s ->
  forall p : 'I_(alen (g (baget s k))), (nat_of_int (aget (g (baget s k)) p) < nat_of_int n)%N.
Proof.
move=> hn /bfor_all_compose_balenP/(_ k) hB p; move: hB.
rewrite /L.allInRange => /for_all_alenP/(_ p) h; exact: inRangeP hn h.
Qed.

(* -------------------------------------------------------------------------- *)
(* The big-graph predicates                                                   *)
(* -------------------------------------------------------------------------- *)

Lemma bisValidIndexP T (t : BigArray.array T) (x : int) :
  (0 < balen t)%N -> L.bisValidIndex t x -> (nat_of_int x < balen t)%N.
Proof. by move=> h0 h; have h2 := inRangeP (n := blength t) h0 h; exact: h2. Qed.

Lemma bisVertexP (g : L.BGraph) (x : int) :
  (0 < balen g)%N -> L.bisVertex g x -> (nat_of_int x < balen g)%N.
Proof. exact: bisValidIndexP. Qed.

(* Every neighbour listed in a row of a big graph is a vertex index. *)
Lemma bvertex_matrixP (g : L.BGraph) n : balen g = n -> (0 < n)%N ->
  L.bfor_all_matrix (L.bisVertex g) g ->
  forall (i : 'I_n) (j : 'I_(alen (baget g i))), (nat_of_int (aget (baget g i) j) < n)%N.
Proof.
move=> hn h0 /(bfor_all_matrixP _ hn) hv i j.
have hb : (0 < balen g)%N by rewrite hn.
by have h2 := bisVertexP hb (hv i j); rewrite hn in h2.
Qed.

(* The predicate is passed by name: leaving it to higher-order unification
   makes the [reflect] statement's [?f (int_of_nat i) (baget g i)] pattern
   ambiguous against the row occurrences inside the graph predicates. *)
Lemma bhasNoLoopsP (g : L.BGraph) n : balen g = n ->
  reflect (forall i : 'I_n, L.bhasLocallyNoLoop g (int_of_nat i)) (L.bhasNoLoops g).
Proof.
move=> hn; rewrite /L.bhasNoLoops.
have h := bfor_alliP (fun (i : int) (_ : array int) => L.bhasLocallyNoLoop g i) hn.
exact: h.
Qed.

Lemma bisUndirectedP (g : L.BGraph) n : balen g = n ->
  reflect (forall i : 'I_n, L.bisLocallyUndirected g (int_of_nat i)) (L.bisUndirected g).
Proof.
move=> hn; rewrite /L.bisUndirected.
have h := bfor_alliP (fun (i : int) (_ : array int) => L.bisLocallyUndirected g i) hn.
exact: h.
Qed.

(* Simple edges: every adjacency row of a big graph is strictly sorted, hence
   (with [bisStrictlySorted_mono] on the row) repetition-free. *)
Lemma bhasSimpleEdgesP (g : L.BGraph) n : balen g = n ->
  reflect (forall i : 'I_n, L.isStrictlySorted Uint63.ltb (baget g i))
          (L.bhasSimpleEdges g).
Proof.
move=> hn; rewrite /L.bhasSimpleEdges.
have h := bfor_allP (L.isStrictlySorted Uint63.ltb) hn.
exact: h.
Qed.

Lemma bhasSimpleEdges_balenP (g : L.BGraph) :
  reflect (forall i : 'I_(balen g), L.isStrictlySorted Uint63.ltb (baget g i))
          (L.bhasSimpleEdges g).
Proof. by apply: bhasSimpleEdgesP. Qed.

(* [L.bisSimpleGraph], as its two conjuncts. *)
Lemma bisSimpleGraph_edges (g : L.BGraph) :
  L.bisSimpleGraph g -> L.bhasSimpleEdges g.
Proof. by case/andP. Qed.

Lemma bisSimpleGraph_loops (g : L.BGraph) :
  L.bisSimpleGraph g -> L.bhasNoLoops g.
Proof. by case/andP. Qed.

End BigArrayBridge.

(* -------------------------------------------------------------------------- *)
(* The binary search [L.mem_sorted]; only its soundness is needed             *)
(* -------------------------------------------------------------------------- *)

Section MemSortedBridge.

Context (a : array int) (x : int).

#[local] Definition mstep (st : int * int * bool) : int * int * bool :=
  let: (lo, hi, found) := st in
  if found then (lo, hi, found)
  else if (lo <? hi)%uint63 then
    let mid := (lo + (hi - lo) / 2)%uint63 in
    let y := a.[mid] in
    if (x <? y)%uint63 then (lo, mid, false)
    else if (y <? x)%uint63 then ((mid + 1)%uint63, hi, false)
    else (lo, hi, true)
  else (lo, hi, found).

Lemma mem_sortedE :
  L.mem_sorted Uint63.ltb a x
  = (iter (alen a) mstep (0%uint63, alength a, false)).2.
Proof.
rewrite /L.mem_sorted; cbv zeta.
rewrite ifold_from_until_absorbE.
- by rewrite nat_of_int0 subn0 foldl_const size_iota.
- move=> j [[lo hi] fnd] hstop j'.
  case: fnd hstop => hstop; first by [].
  case/orP: hstop => // hstop.
  by rewrite /= (negbTE hstop).
- by rewrite nat_of_int0.
Qed.

#[local] Definition minv (st : int * int * bool) :=
  let: (lo, hi, found) := st in
  nat_of_int hi <= alen a /\
  (found -> exists p, p < alen a /\ nat_of_int a.[int_of_nat p] = nat_of_int x).

Lemma mid_lt (lo hi : int) : (lo <? hi)%uint63 ->
  (nat_of_int (lo + (hi - lo) / 2)%uint63 < nat_of_int hi)%N.
Proof.
move=> /Uint63.ltbP hlt.
have [hlo0 hloB] := to_Z_bounded lo; have [hhi0 hhiB] := to_Z_bounded hi.
have hsub : to_Z (hi - lo)%uint63 = (to_Z hi - to_Z lo)%Z.
  by rewrite sub_spec Z.mod_small //; lia.
have h2 : to_Z 2%uint63 = 2%Z by [].
have hdiv : to_Z ((hi - lo) / 2)%uint63 = ((to_Z hi - to_Z lo) / 2)%Z.
  by rewrite div_spec hsub h2.
have hq0 : (0 <= (to_Z hi - to_Z lo) / 2 < to_Z hi - to_Z lo)%Z.
  by split; [apply: Z.div_pos; lia | apply: Z.div_lt_upper_bound; lia].
have hmid : to_Z (lo + (hi - lo) / 2)%uint63 = (to_Z lo + (to_Z hi - to_Z lo) / 2)%Z.
  by rewrite add_spec hdiv Z.mod_small //; lia.
apply/ssrnat.ltP.
have e1 := to_Z_nat_of_int (lo + (hi - lo) / 2)%uint63.
have e2 := to_Z_nat_of_int hi.
lia.
Qed.

Lemma mstep_inv st : minv st -> minv (mstep st).
Proof.
case: st => [[lo hi] fnd] [hhi hfnd]; rewrite /mstep.
case: fnd hfnd => hfnd; first by split.
case hlh: (lo <? hi)%uint63; last by split.
have hmid := mid_lt hlh.
have hmlt : nat_of_int (lo + (hi - lo) / 2)%uint63 < alen a := leq_trans hmid hhi.
case hxa: (x <? a.[(lo + (hi - lo) / 2)%uint63])%uint63.
  by split; [exact: ltnW hmlt | ].
case hax: (a.[(lo + (hi - lo) / 2)%uint63] <? x)%uint63.
  by split; [exact: hhi | ].
split; [exact: hhi | move=> _].
exists (nat_of_int (lo + (hi - lo) / 2)%uint63); split; first exact: hmlt.
rewrite nat_of_intK.
by apply/eqP; rewrite eqn_leq leqNgt -ltb_natE hxa leqNgt -ltb_natE hax.
Qed.

Lemma mem_sorted_sound :
  L.mem_sorted Uint63.ltb a x ->
  exists p, p < alen a /\ nat_of_int a.[int_of_nat p] = nat_of_int x.
Proof.
rewrite mem_sortedE.
have h00 : minv (0%uint63, alength a, false) by split; [exact: leqnn | ].
move: (iter_inv h00 mstep_inv (alen a)).
by case: (iter _ _ _) => [[lo hi] fnd] [_ h2] hfnd; exact: h2 hfnd.
Qed.

Lemma mid_ge (lo hi : int) : (lo <? hi)%uint63 ->
  (nat_of_int lo <= nat_of_int (lo + (hi - lo) / 2)%uint63)%N.
Proof.
move=> /Uint63.ltbP hlt.
have [hlo0 hloB] := to_Z_bounded lo; have [hhi0 hhiB] := to_Z_bounded hi.
have hsub : to_Z (hi - lo)%uint63 = (to_Z hi - to_Z lo)%Z.
  by rewrite sub_spec Z.mod_small //; lia.
have h2 : to_Z 2%uint63 = 2%Z by [].
have hdiv : to_Z ((hi - lo) / 2)%uint63 = ((to_Z hi - to_Z lo) / 2)%Z.
  by rewrite div_spec hsub h2.
have hq0 : (0 <= (to_Z hi - to_Z lo) / 2 < to_Z hi - to_Z lo)%Z.
  by split; [apply: Z.div_pos; lia | apply: Z.div_lt_upper_bound; lia].
have hmid : to_Z (lo + (hi - lo) / 2)%uint63
            = (to_Z lo + (to_Z hi - to_Z lo) / 2)%Z.
  by rewrite add_spec hdiv Z.mod_small //; lia.
apply/ssrnat.leP.
have e1 := to_Z_nat_of_int (lo + (hi - lo) / 2)%uint63.
have e2 := to_Z_nat_of_int lo.
lia.
Qed.

(* Completeness of the binary search on a strictly sorted array: the target
   position stays inside [lo, hi), and that interval shrinks at every step,
   so [alen a] iterations end on [found]. *)
Lemma mem_sorted_complete :
  L.isStrictlySorted Uint63.ltb a ->
  forall p, (p < alen a)%N -> nat_of_int a.[int_of_nat p] = nat_of_int x ->
  L.mem_sorted Uint63.ltb a x.
Proof.
move=> hs p hp hpx; rewrite mem_sortedE.
pose Q := fun (k : nat) (st : int * int * bool) =>
  let: (lo, hi, fnd) := st in
  fnd || [&& nat_of_int lo <= p, p < nat_of_int hi, nat_of_int hi <= alen a
          & nat_of_int hi + k <= alen a + nat_of_int lo].
have hQ : forall k, Q k (iter k mstep (0%uint63, alength a, false)).
  apply: (iter_ind (P := Q)).
    apply/orP; right; apply/and4P; split.
    - by rewrite nat_of_int0 leq0n.
    - exact: hp.
    - exact: leqnn.
    - by rewrite nat_of_int0 !addn0; exact: leqnn.
  move=> k [[lo hi] fnd]; case: fnd => //= /and4P[h1 h2 h3 h4].
  rewrite /mstep.
  have hlh : (lo <? hi)%uint63.
    by rewrite ltb_natE; exact: leq_ltn_trans h1 h2.
  rewrite hlh.
  have hmlt := mid_lt hlh; have hmge := mid_ge hlh.
  have hmal : (nat_of_int (lo + (hi - lo) / 2)%uint63 < alen a)%N.
    exact: leq_trans hmlt h3.
  set mid := (lo + (hi - lo) / 2)%uint63.
  have hmidE : nat_of_int a.[int_of_nat (nat_of_int mid)] = nat_of_int a.[mid].
    by rewrite nat_of_intK.
  case hxa : (x <? a.[mid])%uint63.
    (* the target is strictly below [a.[mid]]: it lies in [lo, mid) *)
    apply/orP; right; apply/and4P.
    have hpm : (p < nat_of_int mid)%N.
      rewrite ltnNge; apply/negP => hmp.
      have h := isStrictlySorted_leq hs hmp hp.
      rewrite hmidE hpx in h.
      by move: hxa; rewrite ltb_natE ltnNge h.
    split.
    - exact: h1.
    - exact: hpm.
    - exact: ltnW hmal.
    - rewrite addnS -addSn; apply: (leq_trans _ h4).
      by rewrite leq_add2r.
  case hax : (a.[mid] <? x)%uint63.
    (* the target is strictly above [a.[mid]]: it lies in [mid+1, hi) *)
    apply/orP; right; apply/and4P.
    have hmp : (nat_of_int mid < p)%N.
      rewrite ltnNge; apply/negP => hpm.
      have h := isStrictlySorted_leq hs hpm hmal.
      rewrite hmidE hpx in h.
      by move: hax; rewrite ltb_natE ltnNge h.
    have hS : nat_of_int (mid + 1)%uint63 = (nat_of_int mid).+1.
      exact: (add1_alenE (a := a) hmal).
    split.
    - by rewrite hS.
    - exact: h2.
    - exact: h3.
    - rewrite hS addnS !addnS ltnS.
      apply: (leq_trans h4); rewrite leq_add2l.
      exact: hmge.
  by [].
move: (hQ (alen a)).
case: (iter _ _ _) => [[lo hi] fnd] /=.
case: fnd => //= /and4P[h1 h2 h3 h4].
have hle : (nat_of_int hi <= nat_of_int lo)%N.
  by rewrite -(leq_add2l (alen a)) addnC.
by move: (leq_ltn_trans h1 h2); rewrite ltnNge hle.
Qed.

End MemSortedBridge.

(* -------------------------------------------------------------------------- *)
(* The [IntList] tests, on strictly decreasing sequences (the shape of        *)
(* [L.diff] outputs)                                                          *)
(* -------------------------------------------------------------------------- *)

(* Membership in a strictly decreasing list, as an equation; the early exit
   on [y < x] is only sound on such lists. *)
Lemma mem_intlistE (x : int) (l : seq int) :
  sorted gtns (map nat_of_int l) ->
  L.mem_intlist x l = (nat_of_int x \in map nat_of_int l).
Proof.
elim: l => [|y l ih] //= hs.
case hyx : (y <? x)%uint63.
  move: hyx; rewrite ltb_natE => hyx.
  rewrite in_cons; symmetry; apply/negbTE; rewrite negb_or.
  apply/andP; split; first by rewrite (gtn_eqF hyx).
  apply/negP => hin.
  by have := gtns_head hs hin; rewrite ltnNge (ltnW hyx).
case hxy : (x =? y)%uint63.
  move: hxy; rewrite eqb_natE => /eqP hxy.
  by rewrite in_cons hxy eqxx.
rewrite eqb_natE in hxy.
rewrite ih; last by move: hs => /=; exact: path_sorted.
by rewrite in_cons hxy.
Qed.

Lemma not_subset_sound (s t : seq int) :
  sorted gtns (map nat_of_int s) -> sorted gtns (map nat_of_int t) ->
  L.not_subset s t ->
  exists x, x \in map nat_of_int s /\ x \notin map nat_of_int t.
Proof.
elim: t s => [|y t iht] [|x s] hs ht //=.
  (* t = [::]: the head of s is missing from t *)
  by move=> _; exists (nat_of_int x); rewrite /= mem_head.
case: ifP => [hxy|hxy].
  (* equal heads: recurse on both tails *)
  move=> hrec.
  have hs' : sorted gtns (map nat_of_int s) by move: hs => /=; exact: path_sorted.
  have ht' : sorted gtns (map nat_of_int t) by move: ht => /=; exact: path_sorted.
  have [z [hzs hzt]] := iht _ hs' ht' hrec.
  have hxy' : nat_of_int x = nat_of_int y by apply/eqP; rewrite -eqb_natE.
  have hzx : (z < nat_of_int x)%N := gtns_head hs hzs.
  exists z; rewrite /= !in_cons hzs orbT negb_or hzt andbT; split=> //.
  by rewrite -hxy' ltn_eqF.
case: ifP => [hlt|hlt] hrec; last first.
  (* x > y: x is missing from t *)
  have hyx : (nat_of_int y < nat_of_int x)%N.
    rewrite ltn_neqAle; apply/andP; split.
      by apply/eqP => he; move: hxy; rewrite eqb_natE he eqxx.
    by rewrite leqNgt -ltb_natE hlt.
  exists (nat_of_int x); rewrite /= mem_head in_cons negb_or; split=> //.
  apply/andP; split; first by rewrite gtn_eqF.
  apply/negP => hxt; have := gtns_head ht hxt.
  by rewrite ltnNge (ltnW hyx).
(* x < y: drop the head of t *)
have ht' : sorted gtns (map nat_of_int t) by move: ht => /=; exact: path_sorted.
have [z [hzs hzt]] := iht _ hs ht' hrec.
have hxy' : (nat_of_int x < nat_of_int y)%N by rewrite -ltb_natE.
have hzx : z <= nat_of_int x.
  move: hzs; rewrite /= in_cons => /orP[/eqP->//|hz].
  exact: ltnW (gtns_head hs hz).
exists z; rewrite /= in_cons negb_or hzt andbT; split=> //.
by rewrite ltn_eqF // (leq_ltn_trans hzx hxy').
Qed.

Lemma incomparable_sound (s t : seq int) :
  sorted gtns (map nat_of_int s) -> sorted gtns (map nat_of_int t) ->
  L.incomparable s t ->
  (exists x, x \in map nat_of_int s /\ x \notin map nat_of_int t) /\
  (exists y, y \in map nat_of_int t /\ y \notin map nat_of_int s).
Proof.
move=> hs ht /andP[h1 h2].
by split; [exact: not_subset_sound hs ht h1 | exact: not_subset_sound ht hs h2].
Qed.

Lemma incomparable_with_allE d ds :
  L.incomparable_with_all d ds = all (L.incomparable d) ds.
Proof. by elim: ds => //= e ds ->. Qed.

Lemma pairwise_incomparableE ds :
  L.pairwise_incomparable ds = pairwise L.incomparable ds.
Proof. by elim: ds => //= d ds ->; rewrite incomparable_with_allE. Qed.

Lemma incomparable_with_all_nth d ds k :
  L.incomparable_with_all d ds -> k < size ds -> L.incomparable d (nth [::] ds k).
Proof. by rewrite incomparable_with_allE => /all_nthP; apply. Qed.

Lemma pairwise_incomparable_nth ds k1 k2 :
  L.pairwise_incomparable ds -> k1 < k2 -> k2 < size ds ->
  L.incomparable (nth [::] ds k1) (nth [::] ds k2).
Proof.
rewrite pairwise_incomparableE => /(pairwiseP [::]) h hk12 hk2.
by apply: h => //=; exact: ltn_trans hk12 hk2.
Qed.

