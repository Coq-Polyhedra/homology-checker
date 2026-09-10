(* -------------------------------------------------------------------------- *)
(* BigArray: persistent arrays beyond [PArray.max_length]                     *)
(*                                                                            *)
(* A two-level chunked array with the same interface and specification as     *)
(* [PArray]: [make], [get], [set], [default], [length], [copy], [max_length]  *)
(* and the corresponding lemmas, unconditional thanks to a shape invariant    *)
(* bundled inside the [array] record (a [Prop], erased by extraction and      *)
(* inert under [vm_compute]).                                                 *)
(*                                                                            *)
(* Chunks have size 2^21 -- a power of two strictly below [PArray.max_length] *)
(* = 2^22 - 1, so the index split is a shift and a mask -- and the capacity   *)
(* is [max_length] = 2^21 * (2^22 - 1) = 2^43 - 2^21.  The shape invariant:   *)
(* ceil(n / 2^21) chunks; every chunk full except the last; every chunk's     *)
(* default is the element default; the outer default is the empty chunk, so   *)
(* out-of-bounds reads fall through to the element default, as in [PArray].   *)
(*                                                                            *)
(* [make] materializes a distinct chunk per slot on purpose: sharing one full *)
(* chunk between slots would alias persistent arrays, and interleaved reads   *)
(* and writes across aliased lineages degrade OCaml persistent arrays.       *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import ZArith Lia Bool Uint63 PArray.

Local Open Scope Z_scope.

(* A single named universe for every [array] instance in this file: separate
   definitions would otherwise each minimize their own rigid universe for the
   primitive [PArray.array], and unification refuses to identify them. *)
Universe barr.

(* -------------------------------------------------------------------------- *)
(* Constants                                                                  *)
(* -------------------------------------------------------------------------- *)

Definition chunk_bits : int := 21%uint63.
Definition chunk_size : int := 2097152%uint63.           (* 2^21 *)
Definition chunk_mask : int := 2097151%uint63.           (* 2^21 - 1 *)
Definition max_length : int := 8796090925056%uint63.     (* 2^21 * (2^22 - 1) *)

Lemma to_Z_chunk_bits : to_Z chunk_bits = 21.
Proof. reflexivity. Qed.

Lemma to_Z_chunk_size : to_Z chunk_size = 2097152.
Proof. reflexivity. Qed.

Lemma to_Z_chunk_mask : to_Z chunk_mask = 2097151.
Proof. reflexivity. Qed.

Lemma to_Z_max_length : to_Z max_length = 8796090925056.
Proof. reflexivity. Qed.

Lemma to_Z_zero : to_Z 0%uint63 = 0.
Proof. reflexivity. Qed.

Lemma to_Z_one : to_Z 1%uint63 = 1.
Proof. reflexivity. Qed.

(* [wB] unfolds to [2 ^ size] with [size] opaque to [lia]: use the literal. *)
Lemma to_Z_bounded' (x : int) : 0 <= to_Z x < 9223372036854775808.
Proof.
pose proof (Uint63.to_Z_bounded x) as h.
change wB with 9223372036854775808 in h; exact h.
Qed.

(* -------------------------------------------------------------------------- *)
(* The index split: chunk index and offset                                    *)
(* -------------------------------------------------------------------------- *)

Definition chunk_of (i : int) : int := (i >> chunk_bits)%uint63.
Definition offset_of (i : int) : int := (i land chunk_mask)%uint63.

Lemma chunk_of_spec (i : int) : to_Z (chunk_of i) = to_Z i / 2097152.
Proof.
unfold chunk_of; rewrite Uint63.lsr_spec, to_Z_chunk_bits.
now replace (2 ^ 21) with 2097152 by reflexivity.
Qed.

Lemma offset_of_spec (i : int) : to_Z (offset_of i) = to_Z i mod 2097152.
Proof.
unfold offset_of; rewrite Uint63.land_spec', to_Z_chunk_mask.
replace 2097151 with (Z.ones 21) by reflexivity.
rewrite Z.land_ones by lia.
now replace (2 ^ 21) with 2097152 by reflexivity.
Qed.

Lemma split_spec (i : int) :
  to_Z i = 2097152 * to_Z (chunk_of i) + to_Z (offset_of i)
  /\ 0 <= to_Z (offset_of i) < 2097152.
Proof.
rewrite chunk_of_spec, offset_of_spec.
split; [apply Z.div_mod; lia | apply Z.mod_pos_bound; lia].
Qed.

Lemma index_inj (i j : int) :
  to_Z (chunk_of i) = to_Z (chunk_of j) ->
  to_Z (offset_of i) = to_Z (offset_of j) -> i = j.
Proof.
intros hc ho; apply Uint63.to_Z_inj.
destruct (split_spec i) as [hi _]; destruct (split_spec j) as [hj _]; lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Chunk-count arithmetic: ceil(n / 2^21)                                     *)
(* -------------------------------------------------------------------------- *)

Definition zk (n : Z) : Z := (n + 2097151) / 2097152.

Lemma zk_bounds (n : Z) : 0 <= n -> n <= 2097152 * zk n <= n + 2097151.
Proof.
intros hn; unfold zk.
pose proof (Z.div_mod (n + 2097151) 2097152 ltac:(lia)) as hdm.
pose proof (Z.mod_pos_bound (n + 2097151) 2097152 ltac:(lia)) as hmb.
lia.
Qed.

Lemma zk_le_max (n : Z) : 0 <= n <= to_Z max_length -> zk n <= 4194303.
Proof.
intros hn; unfold zk.
apply Z.le_trans with ((to_Z max_length + 2097151) / 2097152).
- apply Z.div_le_mono; [lia | rewrite to_Z_max_length in *; lia].
- now rewrite to_Z_max_length.
Qed.

Lemma chunk_of_in_range (n i : int) :
  to_Z i < to_Z n -> to_Z (chunk_of i) < zk (to_Z n).
Proof.
intros hlt.
pose proof (to_Z_bounded' i) as hbi.
pose proof (to_Z_bounded' n) as hbn.
destruct (split_spec i) as [heq hoff].
pose proof (zk_bounds (to_Z n) ltac:(lia)) as hzk.
nia.
Qed.

Lemma offset_in_row (n i : int) :
  to_Z i < to_Z n ->
  to_Z (offset_of i) < Z.min 2097152 (to_Z n - to_Z (chunk_of i) * 2097152).
Proof.
intros hlt.
destruct (split_spec i) as [heq hoff].
apply Z.min_glb_lt; lia.
Qed.

Lemma offset_oob (n i : int) :
  to_Z n <= to_Z i ->
  Z.min 2097152 (to_Z n - to_Z (chunk_of i) * 2097152) <= to_Z (offset_of i).
Proof.
intros hge.
destruct (split_spec i) as [heq hoff].
pose proof (Z.le_min_r 2097152 (to_Z n - to_Z (chunk_of i) * 2097152)).
lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* An indexed iteration on [int], structural on a binary counter              *)
(* -------------------------------------------------------------------------- *)

Definition iter_up {A : Type@{barr}} (n : int) (f : int -> A -> A) (x : A) : A :=
  snd (N.iter (Z.to_N (to_Z n))
        (fun st : int * A => ((fst st + 1)%uint63, f (fst st) (snd st)))
        (0%uint63, x)).

Lemma iter_up_ind {A : Type@{barr}} (P : Z -> A -> Prop) (n : int)
    (f : int -> A -> A) (x : A) :
  P 0 x ->
  (forall (i : int) (acc : A),
     0 <= to_Z i < to_Z n -> P (to_Z i) acc -> P (to_Z i + 1) (f i acc)) ->
  P (to_Z n) (iter_up n f x).
Proof.
intros h0 hstep; unfold iter_up.
pose proof (to_Z_bounded' n) as hbn.
set (step := fun st : int * A => ((fst st + 1)%uint63, f (fst st) (snd st))).
assert (main : forall m : N, Z.of_N m <= to_Z n ->
    to_Z (fst (N.iter m step (0%uint63, x))) = Z.of_N m
    /\ P (Z.of_N m) (snd (N.iter m step (0%uint63, x)))).
{ intros m; induction m using N.peano_ind; intros hm.
  - simpl; split; [reflexivity | exact h0].
  - rewrite N.iter_succ.
    destruct IHm as [hfst hP]; [lia |].
    set (st := N.iter m step (0%uint63, x)) in *.
    unfold step; cbn [fst snd].
    rewrite N2Z.inj_succ in *.
    pose proof (N2Z.is_nonneg m) as hmn.
    assert (hlt : Z.of_N m < to_Z n) by lia.
    split.
    + rewrite Uint63.add_spec, hfst, to_Z_one.
      rewrite Z.mod_small; [lia | change wB with 9223372036854775808; lia].
    + replace (Z.succ (Z.of_N m)) with (to_Z (fst st) + 1) by lia.
      apply hstep; [lia | now rewrite hfst]. }
specialize (main (Z.to_N (to_Z n))).
rewrite Z2N.id in main by lia.
destruct (main (Z.le_refl _)) as [_ hP]; exact hP.
Qed.

(* -------------------------------------------------------------------------- *)
(* The raw two-level representation and its shape invariant                   *)
(* -------------------------------------------------------------------------- *)

Definition norm (n : int) : int :=
  if (n <=? max_length)%uint63 then n else max_length.

Lemma norm_le (n : int) : to_Z (norm n) <= to_Z max_length.
Proof.
unfold norm; destruct (n <=? max_length)%uint63 eqn:h.
- rewrite Uint63.leb_spec in h; exact h.
- lia.
Qed.

Definition nchunks (n : int) : int := ((n + chunk_mask) >> chunk_bits)%uint63.

Definition chunk_len (n ci : int) : int :=
  let rem := (n - (ci << chunk_bits))%uint63 in
  if (chunk_size <? rem)%uint63 then chunk_size else rem.

Definition rget {A : Type@{barr}} (cs : PArray.array (PArray.array A)) (i : int) : A :=
  PArray.get (PArray.get cs (chunk_of i)) (offset_of i).

Definition rset {A : Type@{barr}} (cs : PArray.array (PArray.array A))
    (i : int) (a : A) : PArray.array (PArray.array A) :=
  let ci := chunk_of i in
  PArray.set cs ci (PArray.set (PArray.get cs ci) (offset_of i) a).

Definition rmake {A : Type@{barr}} (n : int) (a : A)
    : PArray.array (PArray.array A) :=
  let k := nchunks n in
  iter_up k (fun ci cs => PArray.set cs ci (PArray.make (chunk_len n ci) a))
    (PArray.make k (PArray.make 0%uint63 a)).

Record wf {A : Type@{barr}} (cs : PArray.array (PArray.array A)) (n : int) : Prop
  := WfShape {
  wf_cap   : to_Z n <= to_Z max_length;
  wf_count : to_Z (PArray.length cs) = zk (to_Z n);
  wf_rows  : forall ci : int, to_Z ci < to_Z (PArray.length cs) ->
               to_Z (PArray.length (PArray.get cs ci))
               = Z.min 2097152 (to_Z n - to_Z ci * 2097152);
  wf_rdef  : forall ci : int, to_Z ci < to_Z (PArray.length cs) ->
               PArray.default (PArray.get cs ci)
               = PArray.default (PArray.default cs);
  wf_odef  : PArray.length (PArray.default cs) = 0%uint63
}.

Arguments wf_cap {A cs n}.
Arguments wf_count {A cs n}.
Arguments wf_rows {A cs n}.
Arguments wf_rdef {A cs n}.
Arguments wf_odef {A cs n}.

(* -------------------------------------------------------------------------- *)
(* Small [PArray] complements                                                 *)
(* -------------------------------------------------------------------------- *)

Lemma pdefault_make {A : Type@{barr}} (n : int) (a : A) :
  PArray.default (PArray.make n a) = a.
Proof.
transitivity (PArray.get (PArray.make n a) PArray.max_length).
- symmetry; apply PArray.get_out_of_bounds.
  apply not_true_is_false; rewrite Uint63.ltb_spec.
  assert (hle : (PArray.length (PArray.make n a) <=? PArray.max_length)%uint63
                = true) by apply PArray.leb_length.
  rewrite Uint63.leb_spec in hle; lia.
- apply PArray.get_make.
Qed.

Lemma pget_oob_Z {A : Type@{barr}} (t : PArray.array A) (i : int) :
  to_Z (PArray.length t) <= to_Z i -> PArray.get t i = PArray.default t.
Proof.
intros hge; apply PArray.get_out_of_bounds.
apply not_true_is_false; rewrite Uint63.ltb_spec; lia.
Qed.

Lemma pget_set_same_Z {A : Type@{barr}} (t : PArray.array A) (i : int) (a : A) :
  to_Z i < to_Z (PArray.length t) ->
  PArray.get (PArray.set t i a) i = a.
Proof.
intros hlt; apply PArray.get_set_same; rewrite Uint63.ltb_spec; exact hlt.
Qed.

Lemma pget_set_neq_Z {A : Type@{barr}} (t : PArray.array A) (i j : int) (a : A) :
  to_Z i <> to_Z j ->
  PArray.get (PArray.set t i a) j = PArray.get t j.
Proof.
intros hne; apply PArray.get_set_other.
intros heq; apply hne; now rewrite heq.
Qed.

(* -------------------------------------------------------------------------- *)
(* [nchunks] and [chunk_len] compute the intended quantities                  *)
(* -------------------------------------------------------------------------- *)

Lemma nchunks_spec (n : int) :
  to_Z n <= to_Z max_length -> to_Z (nchunks n) = zk (to_Z n).
Proof.
intros hn; unfold nchunks, zk.
pose proof (to_Z_bounded' n) as hbn.
rewrite Uint63.lsr_spec, Uint63.add_spec, to_Z_chunk_mask, to_Z_chunk_bits.
rewrite Z.mod_small.
- now replace (2 ^ 21) with 2097152 by reflexivity.
- rewrite to_Z_max_length in hn.
  change wB with 9223372036854775808; lia.
Qed.

Lemma chunk_len_spec (n ci : int) :
  to_Z n <= to_Z max_length -> to_Z ci < zk (to_Z n) ->
  to_Z (chunk_len n ci) = Z.min 2097152 (to_Z n - to_Z ci * 2097152).
Proof.
intros hn hci; unfold chunk_len.
pose proof (to_Z_bounded' n) as hbn.
pose proof (to_Z_bounded' ci) as hbci.
pose proof (zk_bounds (to_Z n) ltac:(lia)) as hzkb.
pose proof (zk_le_max (to_Z n) ltac:(lia)) as hkm.
assert (hbase : to_Z (ci << chunk_bits)%uint63 = to_Z ci * 2097152).
{ rewrite Uint63.lsl_spec, to_Z_chunk_bits.
  replace (2 ^ 21) with 2097152 by reflexivity.
  rewrite Z.mod_small; [reflexivity |].
  change wB with 9223372036854775808; lia. }
assert (hlow : to_Z ci * 2097152 < to_Z n \/ to_Z n = 0 /\ to_Z ci = 0) by lia.
assert (hrem : to_Z (n - (ci << chunk_bits))%uint63
               = to_Z n - to_Z ci * 2097152).
{ rewrite Uint63.sub_spec, hbase, Z.mod_small; [reflexivity |].
  change wB with 9223372036854775808; lia. }
destruct ((chunk_size <? (n - (ci << chunk_bits))%uint63)%uint63) eqn:hcmp.
- rewrite Uint63.ltb_spec, to_Z_chunk_size, hrem in hcmp.
  rewrite to_Z_chunk_size; lia.
- assert (hcmp' : ~ (to_Z chunk_size
                     < to_Z (n - (ci << chunk_bits))%uint63)).
  { intros hx; rewrite <- Uint63.ltb_spec in hx; congruence. }
  rewrite to_Z_chunk_size, hrem in hcmp'.
  rewrite hrem; lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* [rmake] builds the invariant shape                                         *)
(* -------------------------------------------------------------------------- *)

Lemma rmake_spec {A : Type@{barr}} (n : int) (a : A) :
  to_Z n <= to_Z max_length ->
  PArray.length (rmake n a) = nchunks n
  /\ PArray.default (rmake n a) = PArray.make 0%uint63 a
  /\ (forall ci : int, to_Z ci < to_Z (nchunks n) ->
        PArray.get (rmake n a) ci = PArray.make (chunk_len n ci) a).
Proof.
intros hn; unfold rmake.
pose proof (to_Z_bounded' n) as hbn.
assert (hk : to_Z (nchunks n) = zk (to_Z n)) by (apply nchunks_spec; exact hn).
assert (hkmax : (nchunks n <=? PArray.max_length)%uint63 = true).
{ rewrite Uint63.leb_spec, hk.
  change (to_Z PArray.max_length) with 4194303.
  apply zk_le_max; lia. }
assert (hklen : PArray.length (PArray.make (nchunks n) (PArray.make 0%uint63 a))
                = nchunks n).
{ now rewrite PArray.length_make, hkmax. }
apply (iter_up_ind (fun j cs =>
    PArray.length cs = nchunks n
    /\ PArray.default cs = PArray.make 0%uint63 a
    /\ forall ci : int, to_Z ci < j ->
         PArray.get cs ci = PArray.make (chunk_len n ci) a)).
- split; [exact hklen |].
  split; [apply pdefault_make |].
  intros ci hci; exfalso; pose proof (to_Z_bounded' ci); lia.
- intros i acc hi [hlen [hdef hrows]].
  split; [now rewrite PArray.length_set |].
  split; [now rewrite PArray.default_set |].
  intros ci hci.
  destruct (Z.eq_dec (to_Z ci) (to_Z i)) as [heq | hne].
  + assert (hci' : ci = i) by (apply Uint63.to_Z_inj; exact heq); subst ci.
    apply pget_set_same_Z; rewrite hlen; lia.
  + rewrite pget_set_neq_Z by lia.
    apply hrows; lia.
Qed.

Lemma wf_rmake {A : Type@{barr}} (n : int) (a : A) :
  to_Z n <= to_Z max_length -> wf (rmake n a) n.
Proof.
intros hn.
destruct (rmake_spec n a hn) as [hlen [hdef hrows]].
assert (hk : to_Z (nchunks n) = zk (to_Z n)) by (apply nchunks_spec; exact hn).
assert (hclen : forall ci : int, to_Z ci < zk (to_Z n) ->
    (chunk_len n ci <=? PArray.max_length)%uint63 = true).
{ intros ci hci; rewrite Uint63.leb_spec, (chunk_len_spec n ci hn hci).
  change (to_Z PArray.max_length) with 4194303; lia. }
constructor.
- exact hn.
- now rewrite hlen.
- intros ci hci; rewrite hlen, hk in hci.
  rewrite (hrows ci) by lia.
  rewrite PArray.length_make, (hclen ci hci).
  now apply chunk_len_spec.
- intros ci hci; rewrite hlen, hk in hci.
  rewrite (hrows ci) by lia.
  now rewrite hdef, !pdefault_make.
- rewrite hdef, PArray.length_make.
  now change ((0 <=? PArray.max_length)%uint63) with true.
Qed.

(* -------------------------------------------------------------------------- *)
(* [rset] preserves the invariant                                             *)
(* -------------------------------------------------------------------------- *)

Lemma wf_rset {A : Type@{barr}} (cs : PArray.array (PArray.array A))
    (n i : int) (a : A) : wf cs n -> wf (rset cs i a) n.
Proof.
intros hwf; unfold rset.
constructor.
- exact (wf_cap hwf).
- rewrite PArray.length_set; exact (wf_count hwf).
- intros ci; rewrite PArray.length_set; intros hci.
  destruct (Z.eq_dec (to_Z ci) (to_Z (chunk_of i))) as [heq | hne].
  + assert (hci' : ci = chunk_of i) by (apply Uint63.to_Z_inj; exact heq).
    subst ci.
    rewrite pget_set_same_Z by lia.
    rewrite PArray.length_set.
    now apply (wf_rows hwf).
  + rewrite pget_set_neq_Z by lia.
    now apply (wf_rows hwf).
- intros ci; rewrite PArray.length_set; intros hci.
  rewrite PArray.default_set.
  destruct (Z.eq_dec (to_Z ci) (to_Z (chunk_of i))) as [heq | hne].
  + assert (hci' : ci = chunk_of i) by (apply Uint63.to_Z_inj; exact heq).
    subst ci.
    rewrite pget_set_same_Z by lia.
    rewrite PArray.default_set.
    now apply (wf_rdef hwf).
  + rewrite pget_set_neq_Z by lia.
    now apply (wf_rdef hwf).
- rewrite PArray.default_set; exact (wf_odef hwf).
Qed.

(* -------------------------------------------------------------------------- *)
(* The packaged type and the [PArray] interface                               *)
(* -------------------------------------------------------------------------- *)

Record array (A : Type@{barr}) : Type := Mk {
  chunks : PArray.array (PArray.array A);
  blen : int;
  wf_ok : wf chunks blen
}.

Arguments Mk {A} _ _ _.
Arguments chunks {A} _.
Arguments blen {A} _.
Arguments wf_ok {A} _.

Definition length {A : Type@{barr}} (t : array A) : int := blen t.

Definition get {A : Type@{barr}} (t : array A) (i : int) : A := rget (chunks t) i.

Definition default {A : Type@{barr}} (t : array A) : A :=
  PArray.default (PArray.default (chunks t)).

Definition set {A : Type@{barr}} (t : array A) (i : int) (a : A) : array A :=
  Mk (rset (chunks t) i a) (blen t) (wf_rset (chunks t) (blen t) i a (wf_ok t)).

Definition make {A : Type@{barr}} (n : int) (a : A) : array A :=
  Mk (rmake (norm n) a) (norm n) (wf_rmake (norm n) a (norm_le n)).

Definition copy {A : Type@{barr}} (t : array A) : array A := t.

Declare Scope bigarray_scope.
Delimit Scope bigarray_scope with bigarray.
Notation "t .[ i ]" := (get t i)
  (at level 2, left associativity, format "t .[ i ]") : bigarray_scope.
Notation "t .[ i <- a ]" := (set t i a)
  (at level 2, left associativity, format "t .[ i <- a ]") : bigarray_scope.

(* -------------------------------------------------------------------------- *)
(* The [PArray] specification, mirrored                                       *)
(* -------------------------------------------------------------------------- *)

Lemma length_make {A : Type@{barr}} (n : int) (a : A) :
  length (make n a) = if (n <=? max_length)%uint63 then n else max_length.
Proof. reflexivity. Qed.

Lemma length_set {A : Type@{barr}} (t : array A) (i : int) (a : A) :
  length (set t i a) = length t.
Proof. reflexivity. Qed.

Lemma leb_length {A : Type@{barr}} (t : array A) :
  ((length t <=? max_length)%uint63) = true.
Proof.
rewrite Uint63.leb_spec; exact (wf_cap (wf_ok t)).
Qed.

Lemma default_set {A : Type@{barr}} (t : array A) (i : int) (a : A) :
  default (set t i a) = default t.
Proof.
unfold default, set, rset; cbn [chunks].
now rewrite PArray.default_set.
Qed.

Lemma default_make {A : Type@{barr}} (n : int) (a : A) : default (make n a) = a.
Proof.
unfold default, make; cbn [chunks].
destruct (rmake_spec (norm n) a (norm_le n)) as [_ [hdef _]].
now rewrite hdef, pdefault_make.
Qed.

Lemma get_make {A : Type@{barr}} (n : int) (a : A) (i : int) : get (make n a) i = a.
Proof.
unfold get, make, rget; cbn [chunks].
destruct (rmake_spec (norm n) a (norm_le n)) as [hlen [hdef hrows]].
destruct (Z_lt_le_dec (to_Z (chunk_of i)) (to_Z (nchunks (norm n))))
  as [hin | hout].
- rewrite (hrows _ hin); apply PArray.get_make.
- rewrite (pget_oob_Z (rmake (norm n) a) (chunk_of i))
    by (rewrite hlen; lia).
  rewrite hdef; apply PArray.get_make.
Qed.

Lemma get_out_of_bounds {A : Type@{barr}} (t : array A) (i : int) :
  ((i <? length t)%uint63) = false -> get t i = default t.
Proof.
intros hoob.
assert (hge : to_Z (length t) <= to_Z i).
{ assert (h : ~ (to_Z i < to_Z (length t))).
  { intros hx; rewrite <- Uint63.ltb_spec in hx; congruence. }
  lia. }
unfold get, rget, default.
pose proof (wf_ok t) as hwf.
destruct (Z_lt_le_dec (to_Z (chunk_of i)) (to_Z (PArray.length (chunks t))))
  as [hin | hout].
- (* the chunk exists: the offset is past its end *)
  rewrite pget_oob_Z.
  + now apply (wf_rdef hwf).
  + rewrite (wf_rows hwf _ hin).
    exact (offset_oob (blen t) i hge).
- (* past the last chunk: the outer default is the empty chunk *)
  rewrite (pget_oob_Z (chunks t) (chunk_of i) hout).
  apply pget_oob_Z.
  rewrite (wf_odef hwf), to_Z_zero.
  pose proof (to_Z_bounded' (offset_of i)); lia.
Qed.

Lemma get_set_same {A : Type@{barr}} (t : array A) (i : int) (a : A) :
  ((i <? length t)%uint63) = true -> get (set t i a) i = a.
Proof.
intros hin; rewrite Uint63.ltb_spec in hin.
unfold get, set, rset, rget; cbn [chunks].
pose proof (wf_ok t) as hwf.
assert (hci : to_Z (chunk_of i) < to_Z (PArray.length (chunks t))).
{ rewrite (wf_count hwf); exact (chunk_of_in_range (blen t) i hin). }
rewrite pget_set_same_Z by exact hci.
apply pget_set_same_Z.
rewrite (wf_rows hwf _ hci).
exact (offset_in_row (blen t) i hin).
Qed.

Lemma get_set_other {A : Type@{barr}} (t : array A) (i j : int) (a : A) :
  i <> j -> get (set t i a) j = get t j.
Proof.
intros hne.
unfold get, set, rset, rget; cbn [chunks].
destruct (Z.eq_dec (to_Z (chunk_of i)) (to_Z (chunk_of j))) as [hceq | hcne].
- (* same chunk, hence distinct offsets *)
  assert (hoff : to_Z (offset_of i) <> to_Z (offset_of j)).
  { intros ho; apply hne; exact (index_inj i j hceq ho). }
  assert (hcij : chunk_of i = chunk_of j)
    by (apply Uint63.to_Z_inj; exact hceq).
  rewrite <- hcij.
  destruct (Z_lt_le_dec (to_Z (chunk_of i))
              (to_Z (PArray.length (chunks t)))) as [hin | hout].
  + rewrite pget_set_same_Z by exact hin.
    now apply pget_set_neq_Z.
  + (* the chunk index is out of range: both sides read the outer default *)
    assert (hout' : to_Z (PArray.length
        (PArray.set (chunks t) (chunk_of i)
           (PArray.set (PArray.get (chunks t) (chunk_of i)) (offset_of i) a)))
        <= to_Z (chunk_of i))
      by (rewrite PArray.length_set; exact hout).
    rewrite (pget_oob_Z _ _ hout'), (pget_oob_Z _ _ hout).
    now rewrite PArray.default_set.
- now rewrite pget_set_neq_Z.
Qed.

Lemma get_copy {A : Type@{barr}} (t : array A) (i : int) : get (copy t) i = get t i.
Proof. reflexivity. Qed.

Lemma length_copy {A : Type@{barr}} (t : array A) : length (copy t) = length t.
Proof. reflexivity. Qed.

Lemma default_copy {A : Type@{barr}} (t : array A) : default (copy t) = default t.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Sanity checks (crossing [PArray.max_length])                               *)
(* -------------------------------------------------------------------------- *)

Example sanity_get_set :
  get (set (make 5000000%uint63 0%uint63) 4600000%uint63 42%uint63)
      4600000%uint63 = 42%uint63.
Proof. vm_compute; reflexivity. Qed.

Example sanity_get_other :
  get (set (make 5000000%uint63 0%uint63) 4600000%uint63 42%uint63)
      4599999%uint63 = 0%uint63.
Proof. vm_compute; reflexivity. Qed.

Example sanity_length :
  length (make 5000000%uint63 7%uint63) = 5000000%uint63.
Proof. vm_compute; reflexivity. Qed.

Example sanity_oob :
  get (make 5000000%uint63 7%uint63) 6000000%uint63 = 7%uint63.
Proof. vm_compute; reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* The interface, as a checked module type                                    *)
(*                                                                            *)
(* [ARRAY] is the common signature of [PArray] and this file.  The two        *)
(* transparent ascriptions below make the "same interface" claim a checked    *)
(* fact rather than a comment; [<:] keeps every definition transparent, so    *)
(* computation by [vm_compute] / [native_compute] is unaffected (an opaque    *)
(* ascription [:] would seal the bodies and stop them from reducing).         *)
(* -------------------------------------------------------------------------- *)

Module Type ARRAY.
  Parameter array : Type@{barr} -> Type.
  Parameter max_length : int.
  Parameter make : forall A : Type@{barr}, int -> A -> array A.
  Parameter get : forall A : Type@{barr}, array A -> int -> A.
  Parameter set : forall A : Type@{barr}, array A -> int -> A -> array A.
  Parameter default : forall A : Type@{barr}, array A -> A.
  Parameter length : forall A : Type@{barr}, array A -> int.
  Parameter copy : forall A : Type@{barr}, array A -> array A.

  Axiom get_out_of_bounds : forall (A : Type@{barr}) (t : array A) (i : int),
    ((i <? length A t)%uint63) = false -> get A t i = default A t.
  Axiom get_set_same : forall (A : Type@{barr}) (t : array A) (i : int) (a : A),
    ((i <? length A t)%uint63) = true -> get A (set A t i a) i = a.
  Axiom get_set_other : forall (A : Type@{barr}) (t : array A) (i j : int) (a : A),
    i <> j -> get A (set A t i a) j = get A t j.
  Axiom get_make : forall (A : Type@{barr}) (n : int) (a : A) (i : int),
    get A (make A n a) i = a.
  Axiom default_set : forall (A : Type@{barr}) (t : array A) (i : int) (a : A),
    default A (set A t i a) = default A t.
  Axiom default_make : forall (A : Type@{barr}) (n : int) (a : A),
    default A (make A n a) = a.
  Axiom length_make : forall (A : Type@{barr}) (n : int) (a : A),
    length A (make A n a) = if (n <=? max_length)%uint63 then n else max_length.
  Axiom length_set : forall (A : Type@{barr}) (t : array A) (i : int) (a : A),
    length A (set A t i a) = length A t.
  Axiom leb_length : forall (A : Type@{barr}) (t : array A),
    ((length A t <=? max_length)%uint63) = true.
  Axiom get_copy : forall (A : Type@{barr}) (t : array A) (i : int),
    get A (copy A t) i = get A t i.
  Axiom length_copy : forall (A : Type@{barr}) (t : array A),
    length A (copy A t) = length A t.
  Axiom default_copy : forall (A : Type@{barr}) (t : array A),
    default A (copy A t) = default A t.
End ARRAY.

(* This file implements [ARRAY]. *)
Module BigArrayModel <: ARRAY.
  Definition array := array.
  Definition max_length := max_length.
  Definition make := @make.
  Definition get := @get.
  Definition set := @set.
  Definition default := @default.
  Definition length := @length.
  Definition copy := @copy.
  Definition get_out_of_bounds := @get_out_of_bounds.
  Definition get_set_same := @get_set_same.
  Definition get_set_other := @get_set_other.
  Definition get_make := @get_make.
  Definition default_set := @default_set.
  Definition default_make := @default_make.
  Definition length_make := @length_make.
  Definition length_set := @length_set.
  Definition leb_length := @leb_length.
  Definition get_copy := @get_copy.
  Definition length_copy := @length_copy.
  Definition default_copy := @default_copy.
End BigArrayModel.

(* And [PArray] implements it too: the interfaces coincide. *)
Module PArrayModel <: ARRAY.
  Definition array (A : Type@{barr}) : Type := PArray.array A.
  Definition max_length := PArray.max_length.
  Definition make (A : Type@{barr}) (n : int) (a : A) := PArray.make n a.
  Definition get (A : Type@{barr}) (t : array A) (i : int) := PArray.get t i.
  Definition set (A : Type@{barr}) (t : array A) (i : int) (a : A) :=
    PArray.set t i a.
  Definition default (A : Type@{barr}) (t : array A) := PArray.default t.
  Definition length (A : Type@{barr}) (t : array A) := PArray.length t.
  Definition copy (A : Type@{barr}) (t : array A) := PArray.copy t.
  Definition get_out_of_bounds (A : Type@{barr}) (t : array A) (i : int) :=
    @PArray.get_out_of_bounds A t i.
  Definition get_set_same (A : Type@{barr}) (t : array A) (i : int) (a : A) :=
    @PArray.get_set_same A t i a.
  Definition get_set_other (A : Type@{barr}) (t : array A) (i j : int) (a : A) :=
    @PArray.get_set_other A t i j a.
  Definition get_make (A : Type@{barr}) (n : int) (a : A) (i : int) :=
    @PArray.get_make A a n i.
  Definition default_set (A : Type@{barr}) (t : array A) (i : int) (a : A) :=
    @PArray.default_set A t i a.
  Definition default_make (A : Type@{barr}) (n : int) (a : A) :=
    @pdefault_make A n a.
  Definition length_make (A : Type@{barr}) (n : int) (a : A) :=
    @PArray.length_make A n a.
  Definition length_set (A : Type@{barr}) (t : array A) (i : int) (a : A) :=
    @PArray.length_set A t i a.
  Definition leb_length (A : Type@{barr}) (t : array A) :=
    @PArray.leb_length A t.
  Definition get_copy (A : Type@{barr}) (t : array A) (i : int) :=
    @PArray.get_copy A t i.
  Definition length_copy (A : Type@{barr}) (t : array A) :=
    @PArray.length_copy A t.
  Lemma default_copy (A : Type@{barr}) (t : array A) :
    PArray.default (PArray.copy t) = PArray.default t.
  Proof.
  transitivity (PArray.get (PArray.copy t) PArray.max_length).
  - symmetry; apply pget_oob_Z.
    assert (hle : (PArray.length (PArray.copy t) <=? PArray.max_length)%uint63
                  = true) by apply PArray.leb_length.
    rewrite Uint63.leb_spec in hle; lia.
  - rewrite PArray.get_copy; apply pget_oob_Z.
    assert (hle : (PArray.length t <=? PArray.max_length)%uint63 = true)
      by apply PArray.leb_length.
    rewrite Uint63.leb_spec in hle; lia.
  Qed.
End PArrayModel.
