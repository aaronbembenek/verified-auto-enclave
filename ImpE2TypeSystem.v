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

Section Preservation.
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
      -- unfold project_value in *. rewrite sec_level_join_comm.
         split; constructor; auto.
      -- unfold project_value in *. split; constructor; auto.
  Qed.
    
  (* XXX I feel like this should be provable from something... but our typing *)
  (* system seems to be lacking something *)
  Lemma call_fxn_typ : forall pc md G d e r m Gm p Gp q c Gout,
    com_type pc md G d (Ccall e) Gout ->
    estep md d (e,r,m) (Vlambda md c) ->
    exp_type md G d e (Typ (Tlambda Gm p md Gp) q) -> com_type p md Gm d c Gp.
  Proof.
    intros.
    pose (merge_reg_exists r r) as tmp; destruct tmp as [r2 merger].
    pose (merge_mem_exists m m) as tmp; destruct tmp as [m2 mergem].
    pose (project_merge_inv_reg r r r2 merger) as tmp; destruct tmp as [projTr projFr].
    apply (project_merge_inv_mem m m m2) in mergem. destruct mergem as [projTm projFm].
    rewrite <- projTm, <- projTr in H0.
    pose (impe2_exp_complete md d e r2 m2 (Vlambda md c) true H0) as tmp.
    destruct tmp; destruct_pairs; assert (estep2 md d (e, r2, m2) x) as Hestep2 by auto.

    assert (val_type md G d (Vlambda md c) (Typ (Tlambda Gm p md Gp) q)).
    pose (impe2_value_type_preservation md G d e
                                        (Tlambda Gm p md Gp) q
                                        r2 m2 x H1 Hestep2).
    destruct_pairs. rewrite H3 in *; auto.
    rewrite VlambdaWT_iff_ComWT; eauto. (*GRRRRRR*)
  Qed.

  (* XXX nothing connecting loc_context to actual type at location *)
  Lemma ref_type : forall pc md md' d e1 e2 r m G bt s p0 p p' q l rt,
    com_type pc md G d (Cupdate e1 e2) G ->
    estep2 md d (e1, r, m) (VSingle (Vloc l)) ->
    exp_type md G d e1 (Typ (Tref (Typ s p) md' Mut) q) ->
    exp_type md G d e2 (Typ s p') ->
    Loc_Contxt l = Some (Typ bt p0, rt) ->
    s = bt /\ p = p0.
  Proof.
    intros.
    inversion H1; try discriminate; subst.
    inversion H2; try discriminate; subst.  Admitted.

  Lemma impe2_final_config_preservation (G: context) (d: loc_mode) :
    forall G' c r m pc md r' m' t,
      cstep2 md d (c,r,m) (r', m') t ->
      cconfig2_ok pc md G d c r m G' ->
      cterm2_ok G' d r' m'.
  Proof.
    intros G' c r m pc md r' m' t Hcstep Hcfgok.
    remember (c,r,m) as ccfg.
    remember (r',m') as cterm.
    generalize dependent G.
    generalize dependent G'.
    generalize dependent pc.
    generalize dependent c.
    generalize dependent r.
    generalize dependent m.
    generalize dependent r'.
    generalize dependent m'.
    pose Hcstep as Hcstep'.
    induction Hcstep'; unfold cterm2_ok; intros; subst; simpl in *; unfold_cfgs;
      unfold cconfig2_ok in Hcfgok; destruct_pairs; unfold_cfgs; subst;
        inversion Heqcterm; subst.
    (* CSkip *)
    - inversion H0; try discriminate; subst. split; [intros | split; intros]; simpl in *; auto.
      -- now apply H1 in H.
      -- now apply H2 in H.
    (* CAssign *)
    - inversion H1; try discriminate; subst.
      split; [intros | split; intros]; simpl in *; auto; unfold_cfgs.
      -- destruct (Nat.eq_dec x0 x).
         --- rewrite <- (Nat.eqb_eq x0 x) in e0; rewrite e0 in H.
             destruct_pairs.
             assert (cterm2_ok G d r m') as Hcterm.
             unfold cterm2_ok; auto.
             pose (econfig2_pair_protected
                     md G d e p r m' v v1 v2 s 
                     H H7 H0 Hcterm)
               as Heconfig.
             inversion H6; subst.
             now apply (join_protected_l p pc).
         --- rewrite <- (Nat.eqb_neq x0 x) in n. rewrite n in H.
             now apply H2 in H.
      -- inversion Hcstep; subst; try discriminate; unfold_cfgs. now apply H3 in H.
    (* Cdeclassify *)
    - inversion H2; try discriminate; subst.
      split; [intros | split; intros]; simpl in *; auto; unfold_cfgs.
      -- destruct (Nat.eq_dec x0 x).
         --- rewrite <- (Nat.eqb_eq x0 x) in e0; rewrite e0 in H.
             destruct_pairs.
             unfold mem_esc_hatch_ind in H6.
             assert (is_escape_hatch e) as Heh by now unfold is_escape_hatch.
             pose (H6 e Heh m') as Helocs.
             Search (loc_in_exp).
             assert (forall l, loc_in_exp e l -> exists v, m' l = VSingle v) as Hmsing.
             intros. pose (Helocs l H10) as tmp; destruct tmp; destruct_pairs; subst.
             rewrite <- H12; exists x1; auto.
             destruct (same_mem_locs_evals_same_value
                         e r m' md d G (Typ s p) v H8 H1 Heh Hmsing).
             rewrite H in H10. discriminate.
         --- rewrite <- (Nat.eqb_neq x0 x) in n. rewrite n in H.
             now apply H3 in H.
      -- now apply H4 in H.
   (* Cupdate *)
    - inversion H2; try discriminate; subst.
      split; [intros | split; intros]; simpl in *; auto; unfold_cfgs; subst.
      -- now apply H3 in H.
      -- destruct (Nat.eq_dec l0 l).
         --- pose e as e'. rewrite <- (Nat.eqb_eq l0 l) in e'; rewrite e' in H.
             destruct_pairs.
             pose (econfig2_pair_protected md G' d e2 p' r' m v v1 v2 s
                                           H H9 H1) as Hprotected.
             assert (cterm2_ok G' d r' m) as cterm2ok by now unfold cterm2_ok in *.
             apply Hprotected in cterm2ok.
             assert (p = p0) as peq. eapply ref_type. apply H2. apply H0. apply H8. apply H9.
             rewrite e in H7; apply H7.
             rewrite <- peq.
             apply sec_level_join_le_l in H14. apply sec_level_join_le_l in H14.
             inversion cterm2ok; subst. unfold sec_level_le in *.
             destruct p0; auto; try omega.
         --- rewrite <- (Nat.eqb_neq l0 l) in n. rewrite n in H.
             now apply H4 in H.
    (* Coutput *)
    - inversion H1; try discriminate; subst; split; auto.
    (* CCall *)
    - inversion H1; try discriminate; subst.
      unfold forall_dom in *; destruct_pairs.
      assert (com_type pc md G d c G') as lifted_ctyp.
      eapply subsumption; eauto.
      eapply call_fxn_typ; eauto.
      assert (estep md d (e,project_reg r true,project_mem m true) (Vlambda md c))
        as estep2estep.
      apply (impe2_exp_sound md d e r m (VSingle (Vlambda md c))); auto.
      apply estep2estep.
      now apply (sec_level_join_le_l pc q p).
      
      assert (cterm2_ok G' d r'0 m'0).
      -- eapply (IHHcstep' Hcstep' m'0 r'0 Heqcterm m r c); auto.
         unfold cconfig2_ok; split; eauto.
      -- unfold cterm2_ok in *; destruct_pairs; auto.
    (* Call-Div *)
    - inversion H5; try discriminate; subst.
      remember (VPair (Vlambda md c1) (Vlambda md c2)) as v.
      assert (protected q) as qP.
      eapply (econfig2_pair_protected md G d e q r m v
                                      (Vlambda md c1) (Vlambda md c2)
                                      (Tlambda Gm p md Gp)); eauto.
      unfold cterm2_ok in *; auto.
      assert (protected p) as pP. apply sec_level_join_le_r in H11. inversion qP; subst.
      unfold sec_level_le in H11; destruct p; try omega; auto.
      inversion pP; subst.

      assert (com_type Common.H md G d c1 G') as lifted_c1typ.
      eapply subsumption; eauto.
      eapply call_fxn_typ; eauto.
      assert (estep md d (e,project_reg r true,project_mem m true) (Vlambda md c1))
        as estep2estep.
      apply (impe2_exp_sound md d e r m (VPair (Vlambda md c1) (Vlambda md c2))); auto.
      apply estep2estep.
      destruct pc; unfold sec_level_le; auto.
      assert (com_type Common.H md G d c2 G') as lifted_c2typ.
      eapply subsumption; eauto.
      eapply call_fxn_typ; eauto.
      assert (estep md d (e,project_reg r false,project_mem m false) (Vlambda md c2))
        as estep2estep.
      apply (impe2_exp_sound md d e r m (VPair (Vlambda md c1) (Vlambda md c2))); auto.
      apply estep2estep.
      destruct pc; unfold sec_level_le; auto.

      split; intros; destruct_pairs; subst.
      (* see if there was an assignment in either c1 or c2 to change the registers *)
      -- destruct (assign_in_dec c1 x), (assign_in_dec c2 x).
         --- pose (assignment_more_secure Common.H md d c1 G G' x bt p lifted_c1typ a H14). 
             destruct p. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (assignment_more_secure Common.H md d c1 G G' x bt p lifted_c1typ a H14). 
             destruct p. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (assignment_more_secure Common.H md d c2 G G' x bt p lifted_c2typ a H14). 
             destruct p. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (no_assign_reg_context_constant
                     md d (Ccall e) r m r' m' (merge_trace (t1, t2)) x pc G G' Hcstep H5).
             assert (~assign_in (Ccall e) x) as noassign.
             rewrite (assign_not_in_call_div e x md d r m c1 c2); split; auto.
             apply a in noassign; destruct_pairs.
             apply (H6 x v1 v2 bt p). split. rewrite H15; auto. rewrite H16; auto.
      -- split; auto. intros; destruct_pairs.
         destruct (update_in_dec c1 l), (update_in_dec c2 l).
         --- pose (update_more_secure Common.H md d c1 G G' l bt p rt lifted_c1typ u H14). 
             destruct p. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (update_more_secure Common.H md d c1 G G' l bt p rt lifted_c1typ u H14). 
             destruct p. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (update_more_secure Common.H md d c2 G G' l bt p rt lifted_c2typ u H14). 
             destruct p. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (no_update_mem_constant
                     md d (Ccall e) r m r' m' (merge_trace (t1, t2)) l pc G G' Hcstep H5).
             assert (~update_in (Ccall e) l) as noupdate.
             rewrite (update_not_in_call_div e l md d r m c1 c2); split; auto.
             apply e0 in noupdate.
             apply (H7 l v1 v2 bt p rt). split; auto. rewrite noupdate; auto. 
    (* Cenclave *)
    - inversion H; try discriminate; subst. inversion H0; subst.
      eapply IHHcstep'; auto.
      unfold cconfig2_ok; auto; split.
      apply H5.  split; auto.
    (* Cseq-Nil*)
    - inversion H0; try discriminate; subst; split; auto.
    (* Cseq *)
    - inversion H0; try discriminate; subst.
      assert (cconfig2_ok pc md G d hd r0 m0 g') as hdcfg_ok.
      unfold cconfig2_ok; eauto.
      
      assert (cterm2_ok g' d r m) as hdcterm2_ok.
      eapply IHHcstep'1; eauto.
      unfold cterm2_ok in *; destruct_pairs.
      
      assert (cterm2_ok G' d r'0 m'0) as tl_cterm2_ok.
      eapply (IHHcstep'2 Hcstep'2 m'0 r'0 Heqcterm m r (Cseq tl)); eauto.
      unfold cconfig2_ok; eauto.
      unfold cterm2_ok in *; now destruct_pairs.
    (* Cif *)
    - inversion H1; try discriminate; subst.
      eapply IHHcstep'; auto.
      assert (cconfig2_ok pc' md G d c1 r m G') as c1ok.
      unfold cconfig2_ok; split; auto.
      apply c1ok.
    (* Celse *)
    - inversion H1; try discriminate; subst.
      eapply IHHcstep'; auto.
      assert (cconfig2_ok pc' md G d c2 r m G') as c2ok.
      unfold cconfig2_ok; split; auto.
      apply c2ok.
    (* Cif-Div *)
    - inversion H6; try discriminate; subst.
      assert (protected p).
      remember (VPair (Vnat n1) (Vnat n2)) as v.
      eapply econfig2_pair_protected. apply Heqv. apply H20. apply H0.
      assert (cterm2_ok G d r m) as Hcterm2_ok.
      unfold cterm2_ok in *; auto.
      apply Hcterm2_ok.
      (* get that pc' is protected *)
      assert (protected (sec_level_join pc p)) by now apply (join_protected_r pc p).
      inversion H12; subst. rewrite H16 in H22.
      destruct pc'; unfold sec_level_le in H22. omega.
      clear H22 H H12 H16.
      split; intros; destruct_pairs.
      (* see if there was an assignment in either c1 or c2 to change the registers *)
      -- destruct (assign_in_dec c1 x), (assign_in_dec c2 x).
         --- pose (assignment_more_secure Common.H md d c1 G G' x bt p0 H14 a H12).
             destruct p0. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (assignment_more_secure Common.H md d c1 G G' x bt p0 H14 a H12).
             destruct p0. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (assignment_more_secure Common.H md d c2 G G' x bt p0 H15 a H12).
             destruct p0. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (no_assign_reg_context_constant
                     md d (Cif e c1 c2) r m r' m' (merge_trace (t1, t2)) x pc G G'
                     Hcstep H6).
             assert (~ assign_in (Cif e c1 c2) x) as noassign.
             rewrite (assign_in_if_else e c1 c2 x). apply and_not_or. split; auto.
             apply a in noassign; destruct_pairs.
             apply (H7 x v1 v2 bt p0). split. rewrite H13; auto. rewrite H16; auto.
      -- split; auto. intros; destruct_pairs.
         destruct (update_in_dec c1 l), (update_in_dec c2 l).
         --- pose (update_more_secure Common.H md d c1 G G' l bt p0 rt H14 u H12).
             destruct p0. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (update_more_secure Common.H md d c1 G G' l bt p0 rt H14 u H12).
             destruct p0. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (update_more_secure Common.H md d c2 G G' l bt p0 rt H15 u H12).
             destruct p0. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (no_update_mem_constant
                     md d (Cif e c1 c2) r m r' m' (merge_trace (t1, t2)) l pc G G'
                     Hcstep H6).
             assert (~ update_in (Cif e c1 c2) l) as noupdate.
             rewrite (update_in_if_else e c1 c2 l). apply and_not_or. split; auto.
             apply e0 in noupdate; destruct_pairs.
             apply (H8 l v1 v2 bt p0 rt). split; [rewrite noupdate | ]; auto. 
    (* Cwhile-T *)
    - inversion H1; try discriminate; subst.
      (* cterm after executing c is ok *)
      assert (cterm2_ok G' d r m) as cok.
      eapply IHHcstep'1; auto.
      assert (cconfig2_ok pc' md G' d c r0 m0 G') as ccfgok.
      unfold cconfig2_ok in *; split; auto.
      apply ccfgok.
      (* cterm after executing the rest of while is ok *)
      assert (cterm2_ok G' d r'0 m'0).
      eapply IHHcstep'2; auto.
      assert (cconfig2_ok pc md G' d (Cwhile e c) r m G') as cwhileok.
      unfold cterm2_ok in *; destruct_pairs; unfold cconfig2_ok in *; split; auto.
      apply cwhileok.
      (* putting them together, final state is ok *)
      unfold cterm2_ok in *; destruct_pairs. split; auto.
    (* Cwhile-F *)
    - inversion H1; try discriminate; subst. auto.
    (* Cwhile-Div *)
    - inversion H6; try discriminate; subst.
      assert (protected p).
      remember (VPair (Vnat n1) (Vnat n2)) as v.
      eapply econfig2_pair_protected. apply Heqv. apply H13. apply H0.
      assert (cterm2_ok G' d r m) as Hcterm2_ok.
      unfold cterm2_ok in *; auto.
      apply Hcterm2_ok.
      (* get that pc' is protected *)
      assert (protected (sec_level_join pc p)) by now apply (join_protected_r pc p).
      inversion H12; subst. rewrite H16 in H19.
      destruct pc'; unfold sec_level_le in H19. omega.
      split; intros; destruct_pairs.
      (* see if there was an assignment in c to change the registers *)
      -- destruct (assign_in_dec c x).
         --- pose (assignment_more_secure Common.H md d c G' G' x bt p0 H14 a H17).
             destruct p0. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (no_assign_reg_context_constant
                     md d (Cwhile e c) r m r' m' (merge_trace (t1, t2)) x pc G' G'
                     Hcstep H6).
             assert (~assign_in (Cwhile e c) x) as noassign by
                   now rewrite (assign_in_while e c x).
             apply a in noassign; destruct_pairs.
             apply (H7 x v1 v2 bt p0). split; auto. rewrite H18; auto.
      -- split; auto. intros; destruct_pairs.
         destruct (update_in_dec c l).
         --- pose (update_more_secure Common.H md d c G' G' l bt p0 rt H14 u H17).
             destruct p0. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (no_update_mem_constant
                     md d (Cwhile e c) r m r' m' (merge_trace (t1, t2)) l pc G' G'
                     Hcstep H6).
             assert (~update_in (Cwhile e c) l) as noupdate by
                   now rewrite (update_in_while e c l).
             apply e0 in noupdate; destruct_pairs.
             apply (H8 l v1 v2 bt p0 rt). split; auto. rewrite noupdate; auto.
  Qed.

  

  Lemma impe2_type_preservation 
        (G: context) (d: loc_mode) :
    forall pc md c r m G' mdmid cmid rmid mmid rmid' mmid' tmid rfin mfin tfin,
      cconfig2_ok pc md G d c r m G' ->
      cstep2 mdmid d (cmid, rmid, mmid) (rmid', mmid') tmid
      -> cstep2 md d (c, r, m) (rfin, mfin) tfin
      -> imm_premise cmid mdmid rmid mmid rmid' mmid' tmid
                     c md r m rfin mfin tfin d ->
      exists pcmid Gmid Gmid',
        sec_level_le pc pcmid /\ cconfig2_ok pcmid mdmid Gmid d cmid rmid mmid Gmid'.
  Proof.
    intros pc md c r m G' mdmid cmid rmid mmid rmid' mmid' tmid rfin mfin tfin
           Hccfg2ok HIP.
    revert tfin mfin rfin tmid mmid' rmid' mmid rmid cmid mdmid r m G' Hccfg2ok HIP.
    induction c; intros; destruct_pairs; inversion H0; try discriminate; subst; unfold_cfgs;
      inversion Hccfg2ok; try discriminate; subst; destruct_pairs;
        inversion H1; try discriminate; subst; unfold_cfgs.
    (* CALL *)
    - exists p. exists Gm. exists Gp. split. now apply sec_level_join_le_l in H10.
      unfold cconfig2_ok; split; auto; unfold_cfgs.
      eapply call_fxn_typ; eauto. 
      assert (estep md d (e,project_reg r true,project_mem m true) (Vlambda md cmid))
        as estep2estep.
      apply (impe2_exp_sound md d e r m (VSingle (Vlambda md cmid))); auto.
      apply estep2estep.
      split; auto; intros; unfold forall_dom in *; destruct_pairs.
      inversion H12; subst.
      -- apply H16 in H14; destruct H14; destruct_pairs.
         inversion H17; subst.
         assert (protected p1) by now apply (H4 x v1 v2 s1 p1).
         inversion H19; subst. 
         destruct p0; unfold sec_level_le in *; auto; try omega.
    (* ENCLAVE *)
    - exists pc. exists G. exists G'. split. apply sec_level_le_refl.
      split. inversion Hccfg2ok; unfold_cfgs; subst; try discriminate; destruct_pairs.
      inversion H1; try discriminate; unfold_cfgs; subst. inversion H6; subst.
      inversion H15; subst; auto.
      unfold cconfig2_ok; split; unfold_cfgs; auto.
    (* SEQ1 *)
    - exists pc. exists G. exists g'.
      split. apply sec_level_le_refl.
      split. auto.
      unfold cconfig2_ok; split; unfold_cfgs; auto.
    (* SEQ2 *)
    - exists pc. exists g'. exists G'.
      split. apply sec_level_le_refl.
      assert (cconfig2_ok pc md G d c r m g') as c_ok.
      unfold cconfig2_ok in *; destruct_pairs.
      split; auto. 
      assert (cterm2_ok g' d rmid mmid) as cterm2ok.
      apply (impe2_final_config_preservation G d g' c r m pc md rmid mmid tr'); auto.
      unfold cconfig2_ok in *; unfold cterm2_ok in *; destruct_pairs; unfold_cfgs; auto.
    (* IF *)
    - exists pc'. exists G. exists G'.
      split. now apply (sec_level_join_le_l pc p pc') in H19.
      split; unfold cconfig2_ok; auto.
    (* ELSE *)
    - exists pc'. exists G. exists G'.
      split. now apply (sec_level_join_le_l pc p pc') in H18.
      split; unfold cconfig2_ok; auto.
    (* WHILE1 *)
    - exists pc'. exists G'. exists G'.
      split. now apply (sec_level_join_le_l pc p pc') in H17.
      split; unfold cconfig2_ok; auto.
    (* WHILE2 *)
    - exists pc. exists G'. exists G'.
      split. now apply sec_level_le_refl.
      split; auto.
      assert (cconfig2_ok pc' md G' d c r m G').
      unfold cconfig2_ok; split; unfold_cfgs; auto.
      assert (cterm2_ok G' d rmid mmid) as cterm2ok.
      apply (impe2_final_config_preservation G' d G' c r m pc' md rmid mmid tr'); auto.
      unfold cconfig2_ok in *; unfold cterm2_ok in *; destruct_pairs; unfold_cfgs; auto.
  Qed.
  
End Preservation.