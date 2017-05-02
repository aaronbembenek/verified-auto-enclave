Require Import Bool Arith List Omega ListSet.
Require Import Recdef Morphisms.
Require Import Program.Tactics.
Require Import Relation_Operators.
Require FMapList.
Require FMapFacts.
Require Import Classical.
Require Import Coq.Classes.RelationClasses.
Require Import OrderedType OrderedTypeEx DecidableType.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Sorting.Permutation.
Require Import Coq.Sets.Ensembles.
Import ListNotations.
Require Import Common.
Require Import ImpE.
Require Import ImpE2.
Require Import ImpE2Helpers.
Require Import ImpE2Adequacy.

Ltac unfold_cfgs :=
  unfold ccfg_update_reg2 in *;
  unfold ccfg_to_ecfg2 in *;
  unfold ccfg_reg in *;
  unfold ccfg_mem in *;
  unfold ccfg_com in *;
  unfold ccfg_reg2 in *;
  unfold ccfg_mem2 in *;
  unfold ccfg_com2 in *;
  unfold ecfg_exp2 in *;
  unfold ecfg_reg2 in *;
  unfold ecfg_update_exp2 in *;
  unfold ccfg_update_com2 in *;
  unfold ccfg_update_mem2 in *;
  unfold ccfg_update_mem in *;
  unfold ccfg_update_reg in *;
  unfold ccfg_update_com in *;
  unfold ccfg_to_ecfg in *;
  unfold project_ccfg.

Section Value_Preservation.
  Lemma impe2_value_type_preservation : forall md G d e bt sl r m v,
    exp_type md G d e (Typ bt sl) ->
    estep2 md d (e,r,m) v ->
    val_type md G d (project_value v true) (Typ bt sl) /\
    val_type md G d (project_value v false) (Typ bt sl).
  Proof.
    intros md G d e bt sl r m v Hetyp Hestep. pose Hetyp as Hetyp'.
    generalize dependent v.
    induction Hetyp'; intros; inversion Hestep; try discriminate; unfold_cfgs; subst.
    - unfold project_value. split; constructor.
    - inversion H0; subst.
      split; destruct t.
      eapply (VTvar md g d x0 (project_reg r true) b s
                    (project_value (r x0) true)); eauto.
      eapply (VTvar md g d x0 (project_reg r false) b s
                    (project_value (r x0) false)); eauto.
    - unfold project_value. inversion H1; subst.
      split; constructor; auto.
    - inversion H0; subst.
      assert (val_type md g d (project_value (VSingle (Vloc l)) true)
                       (Typ (Tref (Typ s p) md' rt) q) /\
              val_type md g d (project_value (VSingle (Vloc l)) false)
                       (Typ (Tref (Typ s p) md' rt) q))
        as IHe0 by now eapply IHHetyp'; eauto. destruct_pairs.
      unfold project_value in H2, H4.
      split.
      eapply (VTmem md g d md' p rt q (project_mem m0 true) l
                    (project_value (m0 l) true) s); eauto.
      eapply (VTmem md g d md' p rt q (project_mem m0 false) l
                    (project_value (m0 l) false) s); eauto.
    - inversion H0; subst. split; constructor; auto.
    - inversion H; subst.
      assert (val_type md g d (project_value v1 true) (Typ Tnat p)
              /\ val_type md g d (project_value v1 false) (Typ Tnat p))
        as VTe1 by now eapply IHHetyp'1; eauto.
      assert (val_type md g d (project_value v2 true) (Typ Tnat q)
              /\ val_type md g d (project_value v2 false) (Typ Tnat q))
        as VTe2 by now eapply IHHetyp'2; eauto.
      destruct_pairs.
      destruct v1, v2; simpl;
      destruct v, v0; unfold contains_nat in *;
        destruct H2 as [SingNat | PairNat];
        destruct H7 as [SingNat2 | PairNat2];
        try destruct SingNat as [n1 SingNat];
        try destruct SingNat2 as [n'1 SingNat2];
        try destruct PairNat as [n1 [n2 PairNat]];
        try destruct PairNat2 as [n'1 [n'2 PairNat2]];
        try discriminate; simpl in *;
          try inversion SingNat; try inversion SingNat2;
            try inversion PairNat; try inversion PairNat2; subst.
      -- split; constructor; auto.
      -- unfold project_value in *. split; constructor; auto.
      -- unfold project_value in *.
         split; constructor; auto.
      -- unfold project_value in *. split; constructor; auto.
  Qed.
End Value_Preservation.
  
Section Typing_Helpers.
  (* XXX I feel like this should be provable from something... but our typing *)
  (* system seems to be lacking something *)
  Lemma call_fxn_typ : forall pc md G d e r m Gm p Gp q c Gout,
    com_type pc md G d (Ccall e) Gout ->
    estep md d (e,r,m) (Vlambda md c) ->
    exp_type md G d e (Typ (Tlambda Gm p md Gp) q) -> com_type p md Gm d c Gp.
  Proof.
    intros.
    pose (merge_reg r r) as merger.
    pose (merge_mem m m) as mergem.
    pose (project_merge_inv_reg r r true) as projTr.
    pose (project_merge_inv_reg r r false) as projFr.
    pose (project_merge_inv_mem m m true) as projTm.
    pose (project_merge_inv_mem m m false) as projFm; simpl in *.
    assert (H0' := H0).
    rewrite <- projTm, <- projTr in H0.
    rewrite <- projFm, <- projFr in H0'.
    pose (impe2_exp_complete md d e merger mergem (Vlambda md c) (Vlambda md c) H0 H0') as tmp.
    destruct tmp; destruct_pairs; auto.
    assert (val_type md G d (Vlambda md c) (Typ (Tlambda Gm p md Gp) q)).
    pose (impe2_value_type_preservation md G d e
                                        (Tlambda Gm p md Gp) q
                                        merger mergem x H1 H2).
    destruct_pairs. rewrite H3 in *; auto.
    rewrite VlambdaWT_iff_ComWT; eauto. (*GRRRRRR*)
  Qed.

  Lemma ref_type : forall md md' d e r m G bt s p p0 q l rt,
    estep md d (e, r, m) (Vloc l) ->
    exp_type md G d e (Typ (Tref (Typ s p) md' Mut) q) ->
    Loc_Contxt l = Some (Typ bt p0, rt) ->
    s = bt /\ p = p0.
  Proof.
    intros.
    assert (val_type md G d (Vloc l) (Typ (Tref (Typ s p) md' Mut) q)).
    assert (estep2 md d (e, merge_reg r r, merge_mem m m) (VSingle (Vloc l))) as Hestep2.
    pose (impe2_exp_complete md d e (merge_reg r r) (merge_mem m m) (Vloc l) (Vloc l)).
    rewrite project_merge_inv_reg in *. rewrite project_merge_inv_mem in *.
    rewrite project_merge_inv_reg in *. rewrite project_merge_inv_mem in *.
    pose (e0 H H); destruct e1; destruct_pairs.
    assert (x = VSingle (Vloc l)).
    destruct x; unfold project_value in *; subst; auto.
    remember (VPair (Vloc l) (Vloc l)) as v.
    rewrite pair_distinct in Heqv. assert ((Vloc l) = (Vloc l)) by auto. contradiction.
    subst; auto.
    pose (impe2_value_type_preservation
            md G d e (Tref (Typ s p) md' Mut) q (merge_reg r r) (merge_mem m m) (VSingle (Vloc l))
            H0 Hestep2); destruct_pairs; unfold project_value in *; auto.
    rewrite VlocWT_iff_LocContxt in H2. rewrite H2 in H1. inversion H1; subst; auto.
  Qed.
End Typing_Helpers.

Section Security.
  Lemma loc_in_exp_deref : forall e md G d typ r m l,
      is_escape_hatch e ->
      exp_type md G d (Ederef e) typ ->
      estep2 md d (e,r,m) (VSingle (Vloc l)) ->
      loc_in_exp e l.
  Proof.
    intros. remember (e, r, m) as ecfg.
    generalize dependent e. generalize dependent r. generalize dependent m.
    generalize dependent l. generalize dependent typ.
    unfold is_escape_hatch in *; destruct_pairs.
    induction e; intros; unfold_cfgs; subst; unfold loc_in_exp; auto;
      inversion Heqecfg; subst.
    -- inversion H1; try discriminate.
    -- unfold exp_novars in H; simpl in *. omega.
    -- inversion H0; try discriminate; subst.
       inversion H3.
    -- inversion H1; try discriminate; subst; unfold_cfgs.
       now inversion H6.
    -- inversion H1; try discriminate; subst; unfold_cfgs. inversion H2; subst.
       pose (No_Loc_Mem m l0); destruct_pairs.
       pose (H6 l). intuition. apply n in H4. omega.
    -- inversion H0; try discriminate; subst.
       inversion H3.
  Qed.
  
  Lemma same_mem_locs_evals_same_value : forall e r m md d G typ vfin,
      exp_type md G d e typ ->
      estep2 md d (e,r,m) vfin ->
      is_escape_hatch e ->
      (forall l, loc_in_exp e l -> exists v, m l = VSingle v) ->
      exists v, vfin = (VSingle v).
  Proof.
    intros e r m md d G typ vfin Hwt Hestep Heh Helocs. unfold is_escape_hatch in *; destruct_pairs.
    generalize dependent typ. generalize dependent vfin.
    induction e; intros; inversion Hestep; try discriminate; unfold_cfgs. subst.
    - exists (Vnat n0); auto.
    - unfold exp_novars in *; simpl in *; omega.
    - inversion H1; subst.
      inversion Hwt; try discriminate; subst.

      assert (exp_novars e0 /\ exp_novars e3).
      unfold exp_novars in *. now inversion H.

      assert (exp_locs_immutable e0 /\ exp_locs_immutable e3).
      inversion H0. unfold exp_locs_immutable in *; auto.

      assert (forall l : location, loc_in_exp e0 l -> exists v, m l = VSingle v).
      intros. pose (Helocs l) as nolocs. unfold loc_in_exp in nolocs. destruct nolocs.
      left; auto.
      exists x. destruct H3; auto.
      assert (forall l : location, loc_in_exp e3 l -> exists v, m l = VSingle v).
      intros. pose (Helocs l) as nolocs. unfold loc_in_exp in nolocs. destruct nolocs.
      right; auto.
      exists x. destruct H3; auto. 
      destruct_pairs.
      
      pose (IHe1 H5 H6 H7 _ H2 _ H10) as He1; destruct He1 as [x He1].
      pose (IHe2 H11 H9 H8 _ H3 _ H12) as He2; destruct He2 as [y He2].
      unfold contains_nat in *.
      destruct H4 as [[n0 H41']|[n0 [n1 blah]]]; destruct H13 as [[n4 H11']|[n2 [n3 blah']]];
        subst; try discriminate.
      exists (Vnat (n0 + n4)). now unfold apply_op.
    - exists (Vloc l0); auto.
    - inversion H1; subst. 
      assert (loc_in_exp e0 l).
      eapply loc_in_exp_deref; eauto.
      unfold is_escape_hatch. split; [inversion H | inversion H0]; auto.
      assert (loc_in_exp (Ederef e0) l).
      unfold loc_in_exp in *; auto.
      destruct (Helocs l H5). exists x. auto. 
    - subst. exists (Vlambda md c0); auto.
  Qed.


  Definition assign_in (x: var) tr: Prop :=
    exists v r, List.In (Assign r x v) tr.

  Lemma assign_in_dec : forall x tr,
      {assign_in x tr} + {~assign_in x tr}.
  Proof.
    intros.
    induction tr.
    right; auto. unfold assign_in. intuition. destruct H. destruct H; apply in_nil in H. auto.
    destruct IHtr.
    left; unfold assign_in in *; destruct a0; destruct H;
      exists x0; exists x1; now apply in_cons.
    destruct a.
    1-4, 6-8: right; unfold assign_in in *; intuition; destruct H; destruct H;
      apply in_inv in H; destruct H; try discriminate;
        assert (exists v r, List.In (Assign r x v) tr)
        by now exists x0; exists x1.
   1-8: try apply n in H0; auto.
   destruct (eq_nat_dec x v); subst.
   left; unfold assign_in. exists v0; exists r. apply in_eq.
   right. unfold assign_in in *. intuition. destruct H as [v1 [r0 H]].
   apply in_inv in H; destruct H.
   inversion H; omega.
   assert (exists v r, List.In (Assign r x v) tr)
     by now exists v1; exists r0.
   apply n in H0; auto.
  Qed.

  
  Lemma assign_in_app : forall tr tr' x,
      assign_in x (tr ++ tr') <-> assign_in x tr \/ assign_in x tr'.
  Proof.
    unfold assign_in. split; intros. destruct H as [v [r H]]. apply in_app_or in H.
    destruct H; [left | right]; exists v; exists r; auto.
    destruct H; destruct H as [v [r H]]; exists v; exists r; apply in_or_app;
      [now left | now right].
  Qed.
      
  Lemma no_assign_cstep_protected_reg_context_constant : forall md d c r m r' m' tr x pc
                                                                G G',
      cstep md d (c,r,m) (r', m') tr ->
      com_type pc md G d c G' ->
      protected pc ->
      ~assign_in x tr ->
      r x = r' x /\ G x = G' x.
  Proof.
    intros md d c r m r' m' tr x pc G G' Hcstep Hctyp Hprot Hnoassign.   
    remember (c,r,m) as ccfg;
      remember (r',m') as cterm;
    generalize dependent x; generalize dependent r; generalize dependent m;
      generalize dependent c; generalize dependent pc;
        generalize dependent G; generalize dependent G';
          generalize dependent r'; generalize dependent m'; generalize dependent md;
            generalize dependent d.
    intros d md Hcstep. pose Hcstep as Hcstep'.
    induction Hcstep'; intros.
    all: inversion Heqcterm; subst; unfold_cfgs; subst.
    all: inversion Hctyp; try discriminate; auto; subst.
    - destruct (eq_nat_dec x0 x); subst.
      unfold assign_in in *; unfold project_trace in *; simpl in *; unfold not in *. 
      assert (exists (v0 : val) (r0 : reg),
                 Assign r x v
                 = Assign r0 x v0 \/ False) as tmp.
      exists v. exists r; auto.
      apply Hnoassign in tmp; omega.
      unfold_cfgs. apply Nat.eqb_neq in n. now rewrite n.
    - inversion Hprot.
    - assert (com_type pc md G d c G') as ctyp.
      assert (com_type p md Gm d c Gp).
      eapply call_fxn_typ; eauto. unfold_cfgs.
      eapply subsumption; eauto. now apply sec_level_join_le_l in H2.
      pose IHHcstep' as tmp; unfold_cfgs. eapply (tmp Hcstep' m'0 r'0); eauto.
    - inversion H; subst.
      eapply IHHcstep'; eauto.
    - unfold_cfgs.
      rewrite assign_in_app in Hnoassign.
      apply not_or_and in Hnoassign; destruct_pairs.
      assert (r0 x = r x /\ G x = g' x) as hdtmp.
      eapply IHHcstep'1; eauto.
      assert (r x = r'0 x /\ g' x = G' x) as tltmp.
      eapply IHHcstep'2; eauto.
      destruct_pairs.
      rewrite <- H1; rewrite <- H2; split; auto.
    - unfold_cfgs. assert (protected pc') as P.
      apply sec_level_join_le_l in H11. inversion Hprot; subst. 
      unfold sec_level_le in H11; destruct pc'; try omega; auto.
      assert ((r'0, m'0) = (r'0, m'0)) as Hr by auto.
      apply (IHHcstep' Hcstep' m'0 r'0 Hr G' G pc' P c1 H3 m r); eauto.
    - unfold_cfgs. assert (protected pc') as P.
      apply sec_level_join_le_l in H11. inversion Hprot; subst. 
      unfold sec_level_le in H11; destruct pc'; try omega; auto.
      assert ((r'0, m'0) = (r'0, m'0)) as Hr by auto.
      eapply (IHHcstep' Hcstep' m'0 r'0 Hr G' G pc' P c2); eauto.
    - unfold_cfgs. 
      rewrite assign_in_app in Hnoassign.
      apply not_or_and in Hnoassign; destruct_pairs.
      assert (protected pc') as P.
      apply sec_level_join_le_l in H8. inversion Hprot; subst. 
      unfold sec_level_le in H8; destruct pc'; try omega; auto.
      assert (r0 x = r x /\ G' x = G' x) as hdtmp.
      assert ((r,m) = (r,m)) as Hr by auto.
      eapply (IHHcstep'1 Hcstep'1 m r Hr G' G' pc' P c); eauto.
      assert (r x = r'0 x /\ G' x = G' x) as tltmp.
      assert ((r'0,m'0) = (r'0,m'0)) as Hr by auto.
      eapply (IHHcstep'2 Hcstep'2 m'0 r'0 Hr G' G' pc Hprot (Cwhile e c)); eauto.
      destruct_pairs.
      rewrite <- H4; auto.
  Qed.
  
  Lemma context_never_shrinks : forall pc md d c G G' x bt q r m r' m' tr,
      com_type pc md G d c G' ->
      cstep md d (c,r,m) (r',m') tr ->
      G x = Some (Typ bt q) ->
      exists bt' q', G' x = Some (Typ bt' q').
  Proof.
    intros pc md d c G G' x bt q r m r' m' tr Hctyp Hcstep Hctx.
    remember (c,r,m) as ccfg; remember (r',m') as cterm.
    generalize dependent x; generalize dependent r; generalize dependent m;
      generalize dependent c; generalize dependent pc;
        generalize dependent G; generalize dependent G';
          generalize dependent bt; generalize dependent q;
          generalize dependent r'; generalize dependent m'; generalize dependent md;
            generalize dependent d.
    intros d md Hcstep. pose Hcstep as Hcstep'.
    induction Hcstep'; intros; unfold assign_in in *;
      rewrite Heqccfg in *;  rewrite Heqcterm in *; unfold_cfgs; subst;
        inversion Hctyp; try discriminate; subst.
    - exists bt. exists q. auto.
    - destruct (eq_nat_dec x0 x).
      -- subst. rewrite <- (beq_nat_refl x) in *. exists s. exists (sec_level_join p pc). auto.
      -- apply Nat.eqb_neq in n. rewrite n. exists bt. exists q. auto.
    - destruct (eq_nat_dec x0 x).
      -- subst. rewrite <- (beq_nat_refl x) in *. exists s. exists L. auto.
      -- apply Nat.eqb_neq in n. rewrite n. exists bt. exists q. auto.
    - exists bt. exists q. auto.
    - exists bt. exists q. auto.
    - assert (com_type p md Gm d c Gp) as ctyp.
      eapply call_fxn_typ; eauto.
      assert (com_type pc md G d c G') as ctyp2.
      eapply subsumption; eauto. now apply sec_level_join_le_l in H2.
      eapply IHHcstep'; eauto.
    - unfold_cfgs. inversion H; subst. eapply IHHcstep'; eauto.
    - exists bt. exists q. auto.
    - assert (exists bt' q', g' x = Some (Typ bt' q')) as Hg'.
      eapply IHHcstep'1; eauto.
      destruct Hg' as [bt' [q' Hg']].
      eapply IHHcstep'2; eauto.
    - unfold_cfgs. refine (IHHcstep' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
      apply Hcstep'. assert ((r'0, m'0) = (r'0, m'0)) by auto. apply H.
      apply H3. assert ( (c1, r, m)  = (c1, r, m)) by auto; apply H.
      apply Hctx.
    - unfold_cfgs. refine (IHHcstep' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
      apply Hcstep'. assert ((r'0, m'0) = (r'0, m'0)) by auto. apply H.
      apply H4. assert ( (c2, r, m)  = (c2, r, m)) by auto; apply H.
      apply Hctx.
    - unfold_cfgs. exists bt. exists q. auto.
    - exists bt. exists q. auto.
  Qed.
  
  Lemma assign_in_cntxt :  forall pc md d c G G' x r m r' m' tr,
      com_type pc md G d c G' ->
      cstep md d (c,r,m) (r',m') tr ->
      assign_in x tr ->
      exists bt q, G' x = Some (Typ bt q).
  Proof.
    intros pc md d c G G' x r m r' m' tr Hctyp Hcstep Hassn.
    remember (c,r,m) as ccfg; remember (r',m') as cterm.
    generalize dependent x; generalize dependent r; generalize dependent m;
      generalize dependent c; generalize dependent pc;
          generalize dependent G; generalize dependent G';
          generalize dependent r'; generalize dependent m'; generalize dependent md;
            generalize dependent d.
    intros d md Hcstep. pose Hcstep as Hcstep'.
    induction Hcstep'; intros; unfold assign_in in *; destruct Hassn as [va [ra Hassn]];
      rewrite Heqccfg in *;  rewrite Heqcterm in *; unfold_cfgs; subst.
    - inversion Hassn.
    - inversion Hctyp; try discriminate; subst.
      destruct (eq_nat_dec x0 x); subst.
      unfold assign_in in *; unfold project_trace in *; simpl in *; unfold not in *.
      destruct Hassn; try omega.
      rewrite <- (beq_nat_refl x). exists s; exists (sec_level_join p pc); auto.
      inversion Hassn. inversion H. omega. inversion H.
    - inversion Hassn; try discriminate; subst. inversion H.
    - inversion Hassn; try discriminate; subst. inversion H.
    - inversion Hassn; try discriminate; subst.
      inversion H; try discriminate; subst.
      inversion H2.
    - unfold_cfgs. inversion Hctyp; try discriminate; subst.
      assert (com_type p md Gm d c Gp) as ctyp.
      eapply call_fxn_typ; eauto.
      assert (com_type pc md G d c G') as ctyp2.
      eapply subsumption; eauto. now apply sec_level_join_le_l in H2.
      eapply IHHcstep'; eauto.
    - inversion Hctyp; try discriminate; subst.
      inversion H; subst.
      eapply IHHcstep'; eauto.
    - inversion Hassn.
    - unfold_cfgs; inversion Hctyp; try discriminate; subst.
      apply in_app_or in Hassn; destruct Hassn as [Hassn1 | Hassn2].
      assert (exists bt' q', g' x = Some (Typ bt' q')) as Hg'.
      eapply IHHcstep'1; eauto.
      destruct Hg' as [bt' [q' Hg']].
      eapply context_never_shrinks; eauto.
      eapply IHHcstep'2; eauto.
    - unfold_cfgs; inversion Hctyp; try discriminate; subst.
      eapply (IHHcstep' Hcstep' m'0 r'0). auto. apply H3.
      assert ((c1,r,m) = (c1,r,m)) as tmp by auto; apply tmp.
      exists va; exists ra; auto.
    - unfold_cfgs; inversion Hctyp; try discriminate; subst.
      eapply (IHHcstep' Hcstep' m'0 r'0). auto. apply H4.
      assert ((c2,r,m) = (c2,r,m)) as tmp by auto; apply tmp.
      exists va; exists ra; auto.
    - unfold_cfgs; inversion Hctyp; try discriminate; subst.
      apply in_app_or in Hassn; destruct Hassn as [Hassn1 | Hassn2].
      eapply IHHcstep'1; eauto.
      eapply (IHHcstep'2 Hcstep'2 m'0 r'0); auto. apply Hctyp.
      exists va; exists ra; auto.
    - inversion Hassn.
  Qed.
  
  Lemma assignment_more_secure : forall md d c G G' x bt q r m r' m' tr,
      com_type H md G d c G' ->
      cstep md d (c,r,m) (r',m') tr ->
      assign_in x tr ->
      G' x = Some (Typ bt q) ->
      sec_level_le H q.
  Proof.
    intros md d c G G' x bt q r m r' m' tr Hctyp Hcstep Hassn Hctx.
    remember (c,r,m) as ccfg; remember (r',m') as cterm.
    generalize dependent x; generalize dependent r; generalize dependent m;
      generalize dependent c; generalize dependent G; generalize dependent G';
          generalize dependent bt; generalize dependent q;
          generalize dependent r'; generalize dependent m'; generalize dependent md;
            generalize dependent d.
    intros d md Hcstep. pose Hcstep as Hcstep'.
    induction Hcstep'; intros; unfold assign_in in *; destruct Hassn as [va [ra Hassn]];
      rewrite Heqccfg in *;  rewrite Heqcterm in *; unfold_cfgs; subst.
    - inversion Hassn.
    - inversion Hctyp; try discriminate; subst.
      destruct (eq_nat_dec x0 x); subst.
      unfold assign_in in *; unfold project_trace in *; simpl in *; unfold not in *.
      destruct Hassn; try omega.
      rewrite <- (beq_nat_refl x) in Hctx. inversion Hctx; subst.
      unfold sec_level_join; destruct p; auto.
      inversion Hassn. inversion H. omega. inversion H.
    - inversion Hassn; try discriminate; subst. inversion H.
    - inversion Hassn; try discriminate; subst. inversion H.
    - inversion Hassn; try discriminate; subst.
      inversion H; try discriminate; subst.
      inversion H2.
    - unfold_cfgs. inversion Hctyp; try discriminate; subst.
      assert (com_type p md Gm d c Gp) as ctyp.
      eapply call_fxn_typ; eauto.
      assert (com_type H md G d c G') as ctyp2.
      eapply subsumption; eauto.
      eapply IHHcstep'; eauto.
    - inversion Hctyp; try discriminate; subst.
      inversion H; subst.
      eapply IHHcstep'; eauto.
    - inversion Hassn.
    - unfold_cfgs; inversion Hctyp; try discriminate; subst.
      apply in_app_or in Hassn; destruct Hassn as [Hassn1 | Hassn2].
      assert (exists bt' q', g' x = Some (Typ bt' q')) as Hg'.
      eapply assign_in_cntxt; eauto. unfold assign_in. exists va; exists ra; auto.
      destruct Hg' as [bt' [q' Hg']].
      destruct (assign_in_dec x tr').
      -- eapply IHHcstep'2; eauto.
      -- assert (g' x = G' x) as geq.
         eapply no_assign_cstep_protected_reg_context_constant; eauto.
         unfold protected; auto.
         rewrite <- geq, Hg' in Hctx. inversion Hctx; subst.
         eapply (IHHcstep'1 Hcstep'1 m r). auto. apply H5.
         assert ((hd, r0, m0) = (hd, r0, m0)) as tmp by auto; apply tmp.
         exists va; exists ra; apply Hassn1. apply Hg'.
      -- eapply IHHcstep'2; eauto.
    - unfold_cfgs. inversion Hctyp; try discriminate; subst.
      assert (com_type H md G d c1 G'). eapply subsumption; eauto.
      apply sec_level_join_le_l in H11; auto. 1-2: apply context_le_refl.
      eapply IHHcstep'; eauto.
    - unfold_cfgs. inversion Hctyp; try discriminate; subst.
      assert (com_type H md G d c2 G'). eapply subsumption; eauto.
      apply sec_level_join_le_l in H11; auto. 1-2: apply context_le_refl.
      eapply IHHcstep'; eauto.
    - unfold_cfgs; inversion Hctyp; try discriminate; subst.
      apply in_app_or in Hassn; destruct Hassn as [Hassn1 | Hassn2].
      assert (pc' = H) as PH. apply sec_level_join_le_l in H8;
                                destruct pc'; unfold sec_level_le in *; try omega; auto.
      rewrite PH in *.
      eapply (IHHcstep'1 Hcstep'1 m r). auto. apply H3.
      assert ((c, r0, m0) = (c, r0, m0)) as tmp by auto; apply tmp.
      exists va; exists ra; apply Hassn1. apply Hctx.
      eapply IHHcstep'2; eauto.
    - inversion Hassn.
  Qed.

  (* Same thing as assignments for updates *)
  Definition update_in (l: location) tr: Prop :=
    exists v m, List.In (Update m l v) tr.

  Lemma update_in_dec : forall x tr,
      {update_in x tr} + {~update_in x tr}.
  Proof.
    intros.
    induction tr.
    right; auto. unfold update_in. intuition. destruct H. destruct H; apply in_nil in H. auto.
    destruct IHtr.
    left; unfold update_in in *; destruct u; destruct H;
      exists x0; exists x1; now apply in_cons.
    destruct a.
    1-3, 5-8: right; unfold update_in in *; intuition; destruct H; destruct H;
      apply in_inv in H; destruct H; try discriminate;
        assert (exists v m, List.In (Update m x v) tr)
        by now exists x0; exists x1.
   1-8: try apply n in H0; auto.
   destruct (eq_nat_dec x l); subst.
   left; unfold update_in. exists v; exists m. apply in_eq.
   right. unfold update_in in *. intuition. destruct H as [v1 [m0 H]].
   apply in_inv in H; destruct H.
   inversion H; omega.
   assert (exists v m, List.In (Update m x v) tr)
     by now exists v1; exists m0.
   apply n in H0; auto.
  Qed.
   
  Lemma update_more_secure : forall md d c G G' x bt q rt r m r' m' tr,
      com_type H md G d c G' ->
      cstep md d (c,r,m) (r',m') tr ->
      update_in x tr ->
      Loc_Contxt x = Some (Typ bt q, rt) ->
      sec_level_le H q.
  Proof.
    intros md d c G G' x bt q rt r m r' m' tr Hctyp Hcstep Hupdate Hctx.
    remember (c,r,m) as ccfg; remember (r',m') as cterm.
    generalize dependent x; generalize dependent r; generalize dependent m;
      generalize dependent c; generalize dependent G; generalize dependent G';
          generalize dependent bt; generalize dependent q;
          generalize dependent r'; generalize dependent m'; generalize dependent md;
            generalize dependent d.
    intros d md Hcstep. pose Hcstep as Hcstep'.
    induction Hcstep'; intros; unfold assign_in in *; destruct Hupdate as [va [ra Hupdate]];
      rewrite Heqccfg in *;  rewrite Heqcterm in *; unfold_cfgs; subst.
    - inversion Hupdate.
    - inversion Hupdate; subst; inversion H. 
    - inversion Hupdate; subst; inversion H.
    - inversion Hctyp; try discriminate; subst.
      destruct (eq_nat_dec l x); subst.
      unfold update_in in *; unfold project_trace in *; simpl in *; unfold not in *.
      destruct Hupdate; try omega.
      assert (s = bt /\ p = q).
      eapply ref_type; eauto. destruct_pairs; subst.
      apply sec_level_join_le_r in H9. unfold sec_level_join in *; destruct q; auto.
      inversion Hupdate. inversion H. omega. inversion H.
    - inversion Hupdate; try discriminate; subst; inversion H; inversion H2.
    - unfold_cfgs. inversion Hctyp; try discriminate; subst.
      assert (com_type p md Gm d c Gp) as ctyp.
      eapply call_fxn_typ; eauto.
      assert (com_type H md G d c G') as ctyp2.
      eapply subsumption; eauto.
      eapply IHHcstep'; eauto.
      unfold update_in; exists va; exists ra; auto.
    - inversion Hctyp; try discriminate; subst.
      inversion H; subst.
      eapply IHHcstep'; eauto.
      unfold update_in; exists va; exists ra; auto.
    - inversion Hupdate.
    - unfold_cfgs; inversion Hctyp; try discriminate; subst.
      apply in_app_or in Hupdate; destruct Hupdate as [Hupdate1 | Hupdate2].
      eapply (IHHcstep'1 Hcstep'1 m r). auto. apply H5.
      assert ((hd, r0, m0) = (hd, r0, m0)) as tmp by auto; apply tmp.
      exists va; exists ra; apply Hupdate1. apply Hctx.
      eapply IHHcstep'2; eauto.
      unfold update_in; exists va; exists ra; auto.
    - unfold_cfgs. inversion Hctyp; try discriminate; subst.
      assert (com_type H md G d c1 G'). eapply subsumption; eauto.
      apply sec_level_join_le_l in H11; auto. 1-2: apply context_le_refl.
      eapply IHHcstep'; eauto.
      unfold update_in; exists va; exists ra; auto.
    - unfold_cfgs. inversion Hctyp; try discriminate; subst.
      assert (com_type H md G d c2 G'). eapply subsumption; eauto.
      apply sec_level_join_le_l in H11; auto. 1-2: apply context_le_refl.
      eapply IHHcstep'; eauto.
      unfold update_in; exists va; exists ra; auto.
    - unfold_cfgs; inversion Hctyp; try discriminate; subst.
      apply in_app_or in Hupdate; destruct Hupdate as [Hupdate1 | Hupdate2].
      assert (pc' = H) as PH. apply sec_level_join_le_l in H8;
                                destruct pc'; unfold sec_level_le in *; try omega; auto.
      rewrite PH in *.
      eapply (IHHcstep'1 Hcstep'1 m r). auto. apply H3.
      assert ((c, r0, m0) = (c, r0, m0)) as tmp by auto; apply tmp.
      exists va; exists ra; apply Hupdate1. apply Hctx.
      eapply IHHcstep'2; eauto.
      unfold update_in; exists va; exists ra; auto.
    - inversion Hupdate.
  Qed.

  Lemma update_in_app : forall tr tr' x,
      update_in x (tr ++ tr') <-> update_in x tr \/ update_in x tr'.
  Proof.
    unfold update_in. split; intros. destruct H as [v [r H]]. apply in_app_or in H.
    destruct H; [left | right]; exists v; exists r; auto.
    destruct H; destruct H as [v [r H]]; exists v; exists r; apply in_or_app;
      [now left | now right].
  Qed.

  Lemma no_update_cstep_protected_mem_constant : forall md d c r m r' m' tr x pc G G',
      cstep md d (c,r,m) (r', m') tr ->
      com_type pc md G d c G' ->
      ~update_in x tr ->
      m x = m' x.
  Proof.
    intros md d c r m r' m' tr x pc G G' Hcstep Hctyp Hnoupdate.   
    remember (c,r,m) as ccfg;
      remember (r',m') as cterm;
    generalize dependent x; generalize dependent r; generalize dependent m;
      generalize dependent c; generalize dependent pc;
        generalize dependent G; generalize dependent G';
          generalize dependent r'; generalize dependent m'; generalize dependent md;
            generalize dependent d.
    intros d md Hcstep. pose Hcstep as Hcstep'.
    induction Hcstep'; intros.
    all: inversion Heqcterm; subst; unfold_cfgs; subst.
    all: inversion Hctyp; try discriminate; auto; subst.
    - destruct (eq_nat_dec x l); subst.
      unfold update_in in *; unfold project_trace in *; simpl in *; unfold not in *. 
      assert (exists (v0 : val) (m0 : mem),
                 Update m l v
                 = Update m0 l v0 \/ False) as tmp.
      exists v. exists m; auto.
      apply Hnoupdate in tmp; omega.
      unfold_cfgs. apply Nat.eqb_neq in n. now rewrite n.
    - assert (com_type pc md G d c G') as ctyp.
      assert (com_type p md Gm d c Gp).
      eapply call_fxn_typ; eauto. unfold_cfgs.
      eapply subsumption; eauto. now apply sec_level_join_le_l in H2.
      pose IHHcstep' as tmp; unfold_cfgs. eapply (tmp Hcstep' m'0 r'0); eauto.
    - inversion H; subst.
      eapply IHHcstep'; eauto.
    - unfold_cfgs.
      rewrite update_in_app in Hnoupdate.
      apply not_or_and in Hnoupdate; destruct_pairs.
      assert (m0 x = m x) as hdtmp.
      assert ((r,m) = (r,m)) as Hr by auto.
      eapply (IHHcstep'1 Hcstep'1 m r Hr g' G pc hd H5 m0 r0); eauto.
      assert (m x = m'0 x) as tltmp.
      assert ((r'0,m'0) = (r'0,m'0)) as Hr by auto.
      eapply (IHHcstep'2 Hcstep'2 m'0 r'0 Hr G' g' pc (Cseq tl) H7 m r); eauto.
      destruct_pairs.
      rewrite hdtmp, <- tltmp; auto.
    - unfold_cfgs.
      assert ((r'0, m'0) = (r'0, m'0)) as Hr by auto.
      apply (IHHcstep' Hcstep' m'0 r'0 Hr G' G pc' c1 H3 m r); eauto.
    - unfold_cfgs. 
      assert ((r'0, m'0) = (r'0, m'0)) as Hr by auto.
      eapply (IHHcstep' Hcstep' m'0 r'0 Hr G' G pc' c2); eauto.
    - unfold_cfgs. 
      rewrite update_in_app in Hnoupdate.
      apply not_or_and in Hnoupdate; destruct_pairs.
      assert (m0 x = m x) as hdtmp.
      assert ((r,m) = (r,m)) as Hr by auto.
      eapply (IHHcstep'1 Hcstep'1 m r Hr G' G' pc' c H3 m0 r0); eauto.
      assert (m x = m'0 x) as tltmp.
      assert ((r'0,m'0) = (r'0,m'0)) as Hr' by auto.
      eapply (IHHcstep'2 Hcstep'2 m'0 r'0 Hr' G' G' pc (Cwhile e c)); eauto.
      destruct_pairs.
      rewrite <- tltmp; auto.
  Qed.

  
  Lemma tobs_sec_level_app (sl: sec_level) (l l': trace) :
    tobs_sec_level sl l ++ tobs_sec_level sl l' = tobs_sec_level sl (l ++ l').
  Proof.
    unfold tobs_sec_level. now rewrite (filter_app _ l l').
  Qed.

  Lemma econfig2_pair_protected : forall md G d e p r m v v1 v2 bt,
      v = VPair v1 v2 ->
      exp_type md G d e (Typ bt p) ->
      estep2 md d (e,r,m) v ->
      cterm2_ok G d r m ->
      protected p.
  Proof.
    intros.
    remember (e,r,m) as ecfg.
    generalize dependent e.
    generalize dependent v1.
    generalize dependent v2.
    generalize dependent p.
    pose H1 as Hestep2.
    induction Hestep2; intros; subst; try discriminate; unfold_cfgs;
      unfold cterm2_ok in *; destruct_pairs; subst.
     - inversion H4; subst.
       apply (H0 x v1 v2 bt p); split; auto.
     - rewrite H3 in *.
       assert (exists v' v'', v1 = VPair v' v'' \/ v2 = VPair v' v'').
       pose (apply_op_pair (fun x y => x + y) v1 v2) as Hop_pair.
       destruct Hop_pair as [Hop1 Hop2].
       assert (contains_nat v1 /\ contains_nat v2 /\
               (exists v3 v4 : val, apply_op (fun x y => x + y) v1 v2 = VPair v3 v4)).
       split; auto. split; auto. exists v3. exists v0.  auto.
       apply Hop1 in H. destruct H. destruct H. destruct_pairs.
       exists x. exists x0. auto.
       inversion H4; subst; try discriminate.
       destruct H. destruct H; destruct H.
       -- assert (protected p0).
          eapply (IHHestep2_1 Hestep2_1). unfold cterm2_ok; auto.
          apply H. apply H15. auto.
          now apply (join_protected_l p0 q).
       -- assert (protected q ).
          eapply (IHHestep2_2 Hestep2_2). unfold cterm2_ok; auto.
          apply H. apply H17. auto.
          now apply (join_protected_r p0 q).
     - inversion Heqecfg; subst.
       inversion H5; subst.
       assert (val_type md G d (Vloc l) (Typ (Tref (Typ bt p0) md' rt) q)) as valtyp.
       pose (impe2_value_type_preservation md G d e
                                           (Tref (Typ bt p0) md' rt) q r m (VSingle (Vloc l))
                                           H13 Hestep2)
         as vtp.
       unfold project_value in *; destruct_pairs; auto.
       apply VlocWT_iff_LocContxt in valtyp.
       assert (protected p0). eapply H0; eauto.
       now apply join_protected_l.
  Qed.
  
  Lemma diff_loc_protected : forall l,
      mem_sl_ind L ->
      (project_mem minit true) l <> (project_mem minit false) l ->
      protected (g0 l).
  Proof.
    intros. remember (g0 l) as p.
    unfold mem_sl_ind in *.
    rewrite <- (H l) in H0. unfold sec_level_le in H0. 
    destruct p; rewrite <- Heqp in H0. intuition.
    now unfold protected.
  Qed.
  
  Lemma vpair_if_diff : forall m1 m2 v1 v2 l,
      merge_mem m1 m2 = minit ->
      minit l = VPair v1 v2 -> m1 l <> m2 l.
  Proof.
    intros. inversion H; subst. rewrite <- H2 in H0.
    unfold merge_mem in H0. destruct (val_decidable (m1 l) (m2 l)); auto; discriminate.
  Qed.

End Security.