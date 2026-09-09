From mathcomp Require Import finmap all_ssreflect all_algebra.
Import GRing.Theory Num.Theory Order.Theory.
From Polyhedra Require Import hpolyhedron row_submx inner_product polyhedron poly_base affine vector_order barycenter lrel.
From PolyhedraHirsch Require Import high_graph.
Import HPolyhedron.
Open Scope polyh_scope.
From Cert Require Import OddCoveringTheorem.

Section HPolyBase.

Context (d : nat) (R : realFieldType).

Definition base_hpoly (hp : 'hpoly[R]_d) : base_t[R,d] :=
  [fset BaseElt (trmx (row i hp.`A), hp.`b i ord0) | i : 'I_(hp.`c)]%fset.

Lemma base_hpolyP (hP : 'hpoly[R]_d) : '[hP] = 'P(base_hpoly hP)%PH.
Proof.
    apply/poly_eqP => x. apply/idP/idP.
    - intro HxInHP. rewrite/base_hpoly. rewrite in_poly_of_base.
    apply/forallP. intro x0. rewrite polyhedron.in_hs.
    have Hx0 := valP x0. move/imfsetP in Hx0. case:Hx0 => i Hi Hx0.
    simpl in Hi. rewrite Hx0. simpl. rewrite mem_mk_poly in HxInHP.
    rewrite in_hpolyE in HxInHP. rewrite/lev in HxInHP.
    move/forallP in HxInHP. have HxInHPi := HxInHP i.
    rewrite row_vdot. exact HxInHPi.
    - intro HxInPb. rewrite/base_hpoly in HxInPb. rewrite in_poly_of_base 
    in HxInPb. move/forallP in HxInPb. rewrite mem_mk_poly. rewrite in_hpolyE.
    rewrite/lev. apply/forallP. intro i. 
    have Hi : [< ((row i hP.`A)^T)%R, hP.`b i ord0 >] \in [fset [< ((row j hP.`A)^T)%R, 
    hP.`b j ord0 >] | j in 'I_hP.`c].
    apply/imfsetP. exists i. simpl. rewrite inE. trivial. reflexivity.
    have Hhs := HxInPb (Sub [< ((row i hP.`A)^T)%R, hP.`b i ord0 >] Hi).
    rewrite polyhedron.in_hs in Hhs. simpl in Hhs. rewrite -row_vdot. exact Hhs.
Qed.

End HPolyBase.

Section ActiveConstraints.

Context (d : nat) (R : realFieldType).

Notation "'[ u , v ]" := (vdot u v).

Definition normalVector (polytope : 'hpoly[R]_d) (i : 'I_(polytope.`c)) :=
  trmx (row i polytope.`A).

Definition active_constraints (P : 'hpoly[R]_d) (x : 'cV[R]_d) :=
  [set i : 'I_(P.`c) | '[normalVector P i, x] == P.`b i 0%R].

Lemma in_active_constraintsE (P : 'hpoly[R]_d) (x : 'cV[R]_d) (i : 'I_(P.`c)) : 
  i \in active_constraints P x = ('[normalVector P i, x] == P.`b i 0%R).
Proof. by rewrite inE. Qed.

Lemma in_active_constraintsP (P : 'hpoly[R]_d) (x : 'cV[R]_d) (i : 'I_(P.`c)) :
  reflect ('[normalVector P i, x] = P.`b i 0%R) (i \in active_constraints P x).
Proof.
  rewrite in_active_constraintsE. 
  by apply:(iffP eqP).
Qed.

Lemma notin_active_constraintsE (P : 'hpoly[R]_d) (x : 'cV[R]_d) (i : 'I_(P.`c)) : 
  i \notin active_constraints P x = ~~ ('[normalVector P i, x] == P.`b i 0%R).
Proof. by rewrite inE. Qed.

Lemma notin_active_constraintsP (P : 'hpoly[R]_d) (x : 'cV[R]_d) (i : 'I_(P.`c)) :
  x \in P -> reflect (('[normalVector P i, x] > P.`b i 0%R)%R) (i \notin active_constraints P x).
Proof.
  move=>Hx.
  apply:(iffP idP).
  have HinP : ('[ normalVector P i, x] >= P.`b i 0)%R.
    rewrite in_hpolyE in Hx. move/forallP in Hx. have Hxi := Hx i.
    by rewrite -row_vdot in Hxi. 
  - move=> Hnotin. rewrite notin_active_constraintsE in Hnotin. 
    rewrite lt_neqAle. apply/andP. split=>//. by rewrite eq_sym in Hnotin.
  - move=> Hlt. rewrite notin_active_constraintsE. apply/negP.
    have Hnlt := (lt_eqF Hlt). apply/negP. rewrite eq_sym.
    rewrite/negb. by rewrite Hnlt.
Qed.

End ActiveConstraints.

Section NormalCones.

Notation "'[ u , v ]" := (vdot u v).

Context (d : nat) (R : realFieldType).

Local Notation normalVector := (normalVector d R).
Local Notation active_constraints := (active_constraints d R).

Definition normalCone (P : 'hpoly[R]_d) (x : 'cV[R]_d) :=
  coneOf P.`c d R (normalVector P) (active_constraints P x).

Lemma in_normalConeP (P : 'hpoly[R]_d) (x c : 'cV[R]_d) :
  (x \in P) -> reflect (x \in argmin '[P] c) (c \in (normalCone P x)).
Proof.
    move => HxInP. apply: (iffP idP).
    - move => HcInC. rewrite in_argmin. 
      apply/andP. split.
      - rewrite mem_mk_poly. exact HxInP.
      - rewrite poly_subset_mono. apply/poly_subsetP.
        move=> y Hy. rewrite in_hs. simpl. move/in_coneOfP in HcInC.
        case: HcInC => [w [HwInPt Hcomb]].
        rewrite combineE in Hcomb. rewrite Hcomb.
        rewrite vdot_sumDl. rewrite vdot_sumDl. 
        apply: ler_sum. intros i Huseless. destruct Huseless.
        rewrite vdotZl. rewrite vdotZl. case: i => ai Hai. simpl. 
        rewrite ler_pmul2l.
        move/fsubsetP in HwInPt.
        move/HwInPt in Hai. move/in_normalsOfP in Hai.
        case: Hai => [i [Hi Hai]]. rewrite inE in Hi. move/eqP in Hi.
        rewrite Hai. rewrite Hi.
        rewrite in_hpolyE in Hy. rewrite/lev in Hy.
        move/forallP in Hy. have HyInPi := Hy i.
        rewrite row_vdot. exact HyInPi.
        have Hwcon : conic w. exact (valP w).
        have Hwaipos : ai \in finsupp w = (0 < w ai)%R.
        apply: conic_finsuppE. exact Hwcon.
        rewrite Hwaipos in Hai. exact Hai.
    - intro HxInMin. rewrite/normalCone. simpl. 
      apply/in_coneP.
      have Hbound : polyhedron.bounded 'P(base_hpoly d R P)%PH c.
      - rewrite -base_hpolyP. apply/boundedP. exists x. rewrite mem_mk_poly.
        exact HxInP. apply/poly_subsetP. rewrite in_argmin in HxInMin. move/andP in HxInMin.
        case:HxInMin => _ HPSubHs. move=> y Hy. rewrite -mem_polyE in Hy.
        rewrite in_hs. simpl. move/poly_subsetP in HPSubHs. have HyInHS := 
        (HPSubHs y) Hy. rewrite -mem_polyE in HyInHS. rewrite (snd (polyhedron.in_hs)) in 
        HyInHS. exact HyInHS.
      have Hdual := dual_opt_sol Hbound. case:Hdual => w HwSubBase HCombine.
      have HNonEmpt : ([ poly0 ] `<` 'P^=(base_hpoly d R P; finsupp w))%PH.
      have HxInPEq : (x \in 'P^=(base_hpoly d R P; finsupp w))%PH.
      - rewrite -mem_mk_poly in HxInP. rewrite base_hpolyP in HxInP.
        apply/(compl_slack_cond HwSubBase HxInP). 
        have HArgSub := argmin_opt_value Hbound. move/poly_subsetP in HArgSub.
        rewrite -HCombine in HArgSub. rewrite base_hpolyP in HxInMin.
        rewrite mem_polyE in HxInMin. have HxInComb := (HArgSub x HxInMin).
        rewrite -mem_polyE in HxInComb. rewrite (affE x) in HxInComb. exact HxInComb.
      apply/proper0P. exists x. exact HxInPEq.
      have HArgEq := (dual_sol_argmin HwSubBase HNonEmpt).
      rewrite base_hpolyP in HxInMin. rewrite HCombine in HArgEq.
      simpl in HArgEq. rewrite HArgEq in HxInMin.
      pose p : lrel -> 'cV[R]_d := 
        fun e => let: BaseElt y := e in y.1.
      pose S0 : {fset 'cV[R]_d} :=
        [fset p e | e in finsupp w].
      pose w0_fun : {fsfun 'cV[R]_d ~> R} :=
        [fsfun a in S0 => \big[+%R/0%R]_(e <- enum_fset (finsupp w) 
        | p e == a) (val w e)].
      have Hw0con : conic w0_fun.
      - apply/conicP. intros x0 Hx0Inw0. rewrite /w0_fun in Hx0Inw0.
        have HfinSub : (finsupp [fsfun a in S0 => (\sum_(e <- finsupp w | 
        p e == a) val w e)%R] `<=`S0)%fset.
        - intro useless. apply/finsupp_sub.
        have HfinSubb := HfinSub 0%R. move/fsubsetP in HfinSubb. 
        have Hx0InS0 := (HfinSubb x0 Hx0Inw0). rewrite/w0_fun. simpl. 
        rewrite fsfunE. rewrite Hx0InS0. rewrite big_seq_cond. 
        rewrite sumr_ge0. trivial. intros i Hi. move/andP in Hi.
        case: Hi => HiInFs _. have Hwconic := valP w. simpl in Hwconic.
        move/conicP in Hwconic. have HiInCon := (Hwconic i HiInFs). exact HiInCon.
      pose w0 : {conic 'cV[R]_d ~> R} := Sub w0_fun Hw0con. exists w0.
      rewrite /w0. simpl. rewrite /w0_fun. apply/fsubsetP. move=> x0 Hx0Inw0.
      apply/imfsetP. have HfinSub : (finsupp [fsfun a in S0 => (\sum_(e <- finsupp w | 
      p e == a) val w e)%R] `<=`S0)%fset.
      - intro useless. apply/finsupp_sub.
      have HfinSubb := HfinSub 0%R. move/fsubsetP in HfinSubb. have Hx0InS0 := (HfinSubb 
      x0 Hx0Inw0). simpl. rewrite /S0 in Hx0InS0. move/imfsetP in Hx0InS0.
      case: Hx0InS0 => y Hy Hx0y. simpl in Hy. move/fsubsetP in HwSubBase.
      have HyInBase := (HwSubBase y Hy). rewrite/base_hpoly in HyInBase.
      move/imfsetP in HyInBase. case: HyInBase => i Hi Hyi. exists i.
      rewrite inE. simpl in Hi. rewrite in_polyEq in HxInMin. move/andP in HxInMin.
      case: HxInMin => HxInHp HxInBase. move/forallP in HxInHp. 
      have Hxy := HxInHp (Sub y Hy). simpl in Hxy. rewrite Hyi in Hxy.
      rewrite (snd in_hp) in Hxy. exact Hxy.
      rewrite Hyi in Hx0y. rewrite /p in Hx0y. simpl in Hx0y. exact Hx0y.
      rewrite /w0. rewrite /w0_fun. simpl. simpl in HCombine. 
      have HcComb : c = (combine w).1. rewrite HCombine. simpl. reflexivity.
      rewrite HcComb. rewrite (combineb1E HwSubBase). rewrite /combine.
      rewrite -(@big_seq_fsetE _ _ _ _ (base_hpoly d R P) predT (fun e => (w e *: e.1)%R)).
      simpl. change ((\sum_(i <- base_hpoly d R P) w i *: i.1)%R = 
      (\sum_(x0 : finsupp w0) w0 (val x0) *: val x0)%R).
      rewrite -(@big_seq_fsetE _ _ _ _ (finsupp w0) predT (fun a => (w0 a *: a)%R)).
      simpl. have Hleft : (\sum_(i <- base_hpoly d R P) w i *: i.1)%R =
      (\sum_(i <- finsupp w) w i *: i.1)%R. symmetry. apply/big_fset_incl.
      exact HwSubBase. intros x0 Hx0InBase Hx0NotInSupp. rewrite fsfun_dflt.
      rewrite scale0r. reflexivity. exact Hx0NotInSupp. rewrite Hleft.
      have Hw0Sub : (finsupp w0_fun `<=` S0)%fset. apply finsupp_sub.
      have Hw0Sum : (\sum_(i <- finsupp w0_fun) w0_fun i *: i)%R =
      (\sum_(i <- S0) w0_fun i *: i)%R. apply big_fset_incl. exact Hw0Sub.
      intros x0 Hx0InS0 Hx0NotInSupp. rewrite fsfun_dflt. rewrite scale0r. reflexivity.
      exact Hx0NotInSupp. rewrite Hw0Sum. rewrite /w0_fun.
      rewrite (@partition_big_imfset _ _ _ _ _ p _ _). simpl.
      rewrite -/S0. apply: eq_fbigr => a Ha. intro useless. 
      rewrite fsfunE Ha. rewrite scaler_suml. apply: eq_fbigr => i Hi /eqP Hpi.
      rewrite -Hpi. rewrite /p. case i. by move => p0.
Qed.

Lemma normal_cones_are_pointed (P : 'hpoly[R]_d) :
    (\pdim '[P] = d.+1) -> (forall x : 'cV[R]_d, (x \in P) -> polyhedron.pointed(normalCone P x)).
Proof.
    move=> HfullD x HxInP. destruct (polyhedron.pointed(normalCone P x)) eqn:Hpointed.
        - trivial.
        - move/eqP in Hpointed. rewrite eqbF_neg in Hpointed.
          move/pointedPn in Hpointed. case: Hpointed => x0 Hpointed.
          case: Hpointed => d0 Hd0null Hd0InP.
          have Hmin : forall z : 'cV[R]_d, forall t : R, (z \in P)
          -> ('[x0 + t*:d0, z] >= '[x0 + t*:d0, x])%R.
            - intros z t HzInP. have Hd0InPt := Hd0InP t.
              move/in_coneOfP in Hd0InPt.
              case: Hd0InPt => [w [HwInPt Hcomb]].
              rewrite combineE in Hcomb. rewrite Hcomb.
              rewrite vdot_sumDl. rewrite vdot_sumDl.
              apply: ler_sum. intros i Huseless. destruct Huseless.
              rewrite vdotZl. rewrite vdotZl. case: i => ai Hai. simpl. 
              rewrite ler_pmul2l.
              move/fsubsetP in HwInPt.
              move/HwInPt in Hai. move/in_normalsOfP in Hai.
              case: Hai => [i [Hi Hai]]. move/in_active_constraintsP in Hi. 
              rewrite Hai. rewrite Hi.
              rewrite in_hpolyE in HzInP. rewrite/lev in HzInP.
              move/forallP in HzInP. have HzInPi := HzInP i.
              rewrite row_vdot. exact HzInPi.
              have Hwcon : conic w. exact (valP w).
              have Hwaipos : ai \in finsupp w = (0 < w ai)%R.
              apply: conic_finsuppE. exact Hwcon.
              rewrite Hwaipos in Hai. exact Hai.
          have Hnull : forall z, (z \in P) -> '[d0, z - x] == 0%R.
            intros z HzInP.
            have Hminz := Hmin z. 
            destruct ('[d0, z - x] == 0%R) eqn:HzDd0.
            - trivial.
            - have Hminzt :=  Hminz (('[x0,z-x] + 1)/'[d0,x - z])%R HzInP.
              rewrite vdotDl in Hminzt. rewrite vdotDl in Hminzt. 
              rewrite <- ler_subl_addr in Hminzt.
              rewrite vdotZl in Hminzt. rewrite vdotZl in Hminzt.
              rewrite <- addrA in Hminzt. rewrite -mulrBr in Hminzt.
              rewrite -vdotBr in Hminzt. rewrite divrK in Hminzt.
              rewrite -ler_subr_addl in Hminzt. rewrite -vdotBr in Hminzt.
              rewrite ger_addl in Hminzt. have H01 : (0 <= 1 :>R)%R.
              exact ler01. have H00 : (1 == 0 :> R)%R. rewrite eq_le. 
              apply/andP. split. exact Hminzt. exact H01. rewrite oner_eq0 in H00.
              exact H00. rewrite unitfE. move/eqP in HzDd0. apply/eqP.
              rewrite -opprB. rewrite vdotNr. apply/eqP. rewrite oppr_eq0.
              apply/eqP. exact HzDd0.
              have HpInHP : ('[P] `<=` [ hp [<d0, '[ d0, x]>] ]%:PH)%PH.
              - apply/poly_leP. move=> z HzInP. rewrite (polyhedron.in_hp.1.2).
                simpl. rewrite mem_mk_poly in HzInP. have Hnullz := (Hnull z) HzInP. rewrite vdotBr in Hnullz.
                rewrite subr_eq0 in Hnullz. exact Hnullz.
              have HdimHP : adim [hp [<d0, '[d0, x]>]] = d.
              - have HadimHP := (@adim_hp R d [<d0, '[d0, x]>]).
                simpl in HadimHP. rewrite -eqbF_neg in Hd0null.
                move/eqP in Hd0null. rewrite Hd0null in HadimHP. simpl in HadimHP.
                have Haff0 : ([ affine0 ] `<` [ hp [<d0, '[ d0, x]>] ])%PH.
                - apply/affine_proper0P. exists x. rewrite (snd in_hp).
                  by apply/eqP.
                have HadimH := HadimHP Haff0. rewrite add0n in HadimH. exact HadimH.
              have HaffS : (adim (hull '[P]) <= adim [hp [<d0, '[d0, x]>]])%N.
              - have HhullP := (hullP '[P] [ hp [<d0, '[ d0, x]>] ]).
                rewrite HhullP in HpInHP. by apply/adimS.
              rewrite HdimHP in HaffS.
              rewrite HfullD in HaffS. by rewrite ltnn in HaffS.
Qed.

End NormalCones.

Section CoveringCriterion.

Context (d : nat) (R : realFieldType).

Variable (P : 'hpoly[R]_d) (V : {fset 'cV[R]_d}).

Local Notation normalCone := (normalCone d R P).
Local Notation in_normalConeP := (in_normalConeP d R P).

Theorem covering_criterion :
  {subset V <= P} -> (forall z : 'cV[R]_d, exists x : 'cV[R]_d, 
  (x \in V)/\ (z \in normalCone x)) -> ((vertex_set '[P]) `<=` V)%fset.
Proof.
  move=> Hsub Hcover.
  apply/fsubsetP => v Hv.
  have Hopt : exists c, argmin '[P] c = [pt v]%:PH.
    rewrite in_vertex_setP in Hv.
    have Hemp : [pt v]%:PH `>` ([poly0]).
    apply/proper0P. exists v. apply: in_pt_self.
    have Hexists := face_argmin Hv Hemp.
    move: Hexists => [c [Hbound Heq]].
    by exists c.
  move: Hopt => [c Hopt].
  have Hcoverc := Hcover c.
  move: Hcoverc => [z [Hz Hcz]].
  move/(in_normalConeP z c (Hsub z Hz)) in Hcz.
  rewrite Hopt in Hcz.
  rewrite (polyhedron.in_pt v z) in Hcz. move/eqP in Hcz.
  by rewrite Hcz in Hz.
Qed.

End CoveringCriterion.