From mathcomp Require Import finmap all_ssreflect all_algebra.
Import GRing.Theory Num.Theory Order.Theory.
From Polyhedra Require Import hpolyhedron row_submx inner_product polyhedron poly_base affine vector_order barycenter lrel.
From PolyhedraHirsch Require Import high_graph.
Import HPolyhedron.
Open Scope polyh_scope.
From Cert Require Import CoveringCriterion OddCoveringTheorem.

Section VertexCriterion.

Context (d : nat) (R : realFieldType).

Variable (P : 'hpoly[R]_d).

Local Notation m := P.`c.
Local Notation active_constraints := (active_constraints d R P).
Local Notation normalVector := (normalVector d R).
Local Notation coneOf := (coneOf m d R (normalVector P)).
Local Notation normalsOf := ((normalsOf m d R (normalVector P))).

Theorem vertex_criterion : 
  compact '[P] -> forall v, v \in P -> (exists I : {set 'I_m}, I \subset (active_constraints v) 
  /\ (\dim <<(normalsOf I)>> = d)%VS) -> v \in vertex_set '[P].
Proof.
  move=> Hcomp v HvP [I [HI HdimI]].
  pose c := (\sum_(i in I) (normalVector P i))%R.
  have Hvmax : v \in argmin '[P] c.
    rewrite in_argmin. 
    apply/andP. split=>//.
    by rewrite mem_mk_poly.
    apply/poly_subset_hsP. move=> x Hx.
    simpl. rewrite vdot_sumDl. rewrite vdot_sumDl.
    apply: ler_sum=> i HiI.
    move/subsetP in HI. have Hi := HI i HiI.
    move/in_active_constraintsP in Hi. rewrite Hi.
    rewrite mem_mk_poly in_hpolyE in Hx.
    move/forallP in Hx. have Hxi := Hx i.
    rewrite/normalVector. by rewrite -row_vdot in Hxi.
  have HmaxUn : forall x, x \in argmin '[P] c -> x = v.
    move=> x Hx.
    rewrite in_argmin in Hx. move/andP : Hx => [HxP /poly_subset_hsP Hhs].
    have Heq : ('[ c, x] = '[ c, v])%R.
    apply/eqP. rewrite eq_le. apply/andP; split=>//.
    rewrite -mem_mk_poly in HvP.
    - by have Hhsv := Hhs v HvP; simpl in Hhsv.
    - rewrite in_argmin in Hvmax. move/andP : Hvmax => [_ /poly_subset_hsP Hhsv].
      by have Hhsx := Hhsv x HxP; simpl in Hhsx.
    have Hpos : forall i, i \in I -> (0 <= '[ normalVector P i, x - v])%R.
      move=>i HiI. rewrite vdotBr subr_ge0.
      move/subsetP in HI. have Hi := HI i HiI.
      move/in_active_constraintsP in Hi. rewrite Hi.
      rewrite mem_mk_poly in_hpolyE in HxP.
      move/forallP in HxP. have Hxi := HxP i.
      rewrite/normalVector. by rewrite -row_vdot in Hxi.
    have HeqT : forall i, i \in I -> '[normalVector P i, x - v]%R = 0%R.
      move=> i HiI.
      have HeqTB := (@psumr_eq0P R [finType of 'I_m] [pred i | i \in I] (fun i =>
      ('[normalVector P i, x - v])%R)).
      apply: HeqTB. move=> j HjI. by apply: Hpos j HjI.
      rewrite vdot_sumDl in Heq. rewrite vdot_sumDl in Heq.
      change ((\sum_(i0 | i0 \in I) '[ normalVector P i0, x - v])%R = 0%R).
      move/eqP in Heq. rewrite -subr_eq0 in Heq. move/eqP in Heq.
      have Heq' : 0 %R = (\sum_(i in I) ('[normalVector P i, x] -'[normalVector P i, v]))%R.
        symmetry. rewrite big_split. simpl. by rewrite sumrN.
      rewrite [RHS]Heq'. apply: eq_bigr => k Hk. by rewrite vdotBr. 
      by apply: HiI.
    have Horth : (x - v)%R \in (<<normalsOf I>>^OC)%VS.
        apply/orthvP. move=>y Hy.
        pose X := in_tuple (enum_fset (normalsOf I)).
        have Hy' : y \in <<X>>%VS. exact: Hy.
        have Hycoord := @coord_span R _ _ X y Hy.
        rewrite Hycoord. rewrite vdot_sumDl. apply: big1 => k Hk.
        have HXk : (X`_k \in normalsOf I)%R.
          rewrite /X. apply: mem_nth. apply: ltn_ord k. 
        rewrite vdotZl. move/in_normalsOfP: HXk => [j [HjI HXj]].
        rewrite HXj. rewrite (HeqT j HjI). by rewrite mulr0.
    have Hdim : \dim (<<normalsOf I>>^OC)%VS = 0.
        rewrite dim_orthv. rewrite HdimI. apply: subnn. 
    move/eqP in Hdim. rewrite dimv_eq0 in Hdim. move/eqP in Hdim.
    rewrite Hdim in Horth. rewrite memv0 in Horth.
    rewrite subr_eq0 in Horth. by move/eqP in Horth.
    rewrite in_vertex_setP.
    have Hemp : [ poly0 ] `<` '[P].
      apply/proper0P. exists v. by rewrite -mem_mk_poly in HvP.
    have Hopt : argmin '[P] c \in face_set '[P].
      move/compactP in Hcomp. have Hbound := Hcomp Hemp c.
      by apply argmin_in_face_set.
    have Hsing : (argmin '[P] c) = [pt v]%:PH.
      apply:le_anti. apply/andP. split.
      apply/poly_subsetP. move=> x Hx. rewrite -mem_polyE in Hx.
      rewrite -mem_polyE. rewrite (snd (polyhedron.in_pt v x)). apply/eqP.
      by exact: HmaxUn x Hx.
      by rewrite pt_subset.
    by rewrite -Hsing.
Qed.

End VertexCriterion.
