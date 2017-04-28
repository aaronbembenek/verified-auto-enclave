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

(*******************************************************************************
*
* SECURITY_PASSIVE
*
*******************************************************************************)

Section Secure_Passive.
  Lemma config2_ok_implies_obs_equal (m: mem2) (c: com) (t: trace2) :
    forall pc md G d r G' r' m',
      cconfig2_ok pc md G d c r m G' ->
      cstep2 md d (c,r,m) (r',m') t ->
      tobs_sec_level L (project_trace t true) = tobs_sec_level L (project_trace t false).
  Proof.
    intros pc md G d r G' r' m' Hccfg2ok Hcstep2.
    remember (c,r,m) as ccfg.
    generalize dependent c.
    generalize dependent r.
    generalize dependent m.
    generalize dependent pc.
    generalize dependent G'.
    generalize dependent G.
    pose Hcstep2 as Hcstep.
    induction Hcstep; intros; subst; simpl in *; auto; repeat unfold_cfgs; subst.
    (* OUTPUT *)
    - unfold sec_level_le_compute. destruct sl; auto.
      destruct v; simpl; auto.
      inversion Hccfg2ok; destruct_pairs; unfold_cfgs; subst; auto; try discriminate.
      inversion H; unfold_cfgs; try discriminate; subst; auto.
      remember (VPair v v0) as vpair.
      assert (cterm2_ok G' d r m) as Hctermok; unfold cterm2_ok; auto.
      assert (protected p) by apply (econfig2_pair_protected
                                       md G' d e p r m vpair v v0 s
                                       Heqvpair H11 H0 Hctermok).
      pose (sec_level_join_ge p pc); destruct_pairs.
      apply (sec_level_le_trans p (sec_level_join p pc) L) in H13; auto.
      destruct p; inversion H5; inversion H13.
    (* CALL *)
    - assert (imm_premise c md r m r'0 m'0 tr
                          (Ccall e) md r m r'0 m'0 tr d)
        as HIP by now apply IPcall.
      pose (impe2_type_preservation G d pc md (Ccall e) r m G'
                                    md c r m r'0 m'0 tr r'0 m'0 tr 
                                    Hccfg2ok Hcstep Hcstep2 HIP)
        as Lemma6.
      destruct Lemma6 as [pcmid [Gmid [Gmid' Lemma6]]]; destruct_pairs; subst.
      apply (IHHcstep Hcstep Gmid Gmid' pcmid m r c H1); auto.
    (* CALL-DIV *)
    - remember (VPair (Vlambda md c1) (Vlambda md c2)) as v.
      inversion Hccfg2ok; destruct_pairs; unfold_cfgs; subst; auto; try discriminate.
      inversion H; unfold_cfgs; try discriminate; subst; auto.
      assert (protected q) as Hqprotected.
      eapply econfig2_pair_protected in H10; auto. apply H0.
      assert (cterm2_ok G d r m) by now unfold cterm2_ok. apply H9.
      assert (protected (sec_level_join pc q)) as Hpcqprotected
          by apply (join_protected_r pc q Hqprotected).
      inversion Hpcqprotected; rewrite Hpcqprotected in H11.
      assert (protected p) as Hpprotected.
      unfold protected. unfold sec_level_le in H11; destruct p; intuition.
      clear H11 H14.
      assert (com_type p md Gm d c1 Gp).
      eapply call_fxn_typ; eauto. 
      assert (estep md d (e,project_reg r true,project_mem m true) (Vlambda md c1))
        as estepc1.
      apply (impe2_exp_sound md d e r m (VPair (Vlambda md c1) (Vlambda md c2))); auto.
      apply estepc1.
      assert (com_type p md Gm d c2 Gp).
      eapply call_fxn_typ; eauto. 
      assert (estep md d (e,project_reg r false,project_mem m false) (Vlambda md c2))
        as estepc2.
      apply (impe2_exp_sound md d e r m (VPair (Vlambda md c1) (Vlambda md c2))); auto.
      apply estepc2.
      assert (tobs_sec_level L t1 = []) as t1_empty.
      eapply protected_typ_no_obs_output in H1; auto.
      apply H9; auto. auto.
      assert (tobs_sec_level L t2 = []) as t2_empty.
      eapply protected_typ_no_obs_output in H2; auto.
      apply H11; auto. auto.
      pose (project_merge_inv_trace t1 t2 true) as Ht1; simpl in *.
      pose (project_merge_inv_trace t1 t2 false) as Ht2; simpl in *.
      now rewrite Ht1, Ht2, t1_empty, t2_empty.
    (* ENCLAVE *)
    - assert (imm_premise c (Encl enc) r m r'0 m'0 tr
                          (Cenclave enc c) Normal r m r'0 m'0 tr d)
        as HIP by now apply IPencl.
      pose (impe2_type_preservation G d pc Normal (Cenclave enc c) r m G'
                                    (Encl enc) c r m r'0 m'0 tr _ _ _ 
                                    Hccfg2ok Hcstep Hcstep2 HIP) as Lemma6.
      destruct Lemma6 as [pcmid [Gmid [Gmid' Lemma6]]]; destruct_pairs; subst.
      apply (IHHcstep Hcstep Gmid Gmid' pcmid m r c H0); auto.
   (* SEQ *)
    - assert (imm_premise hd md r0 m0 r m tr
                          (Cseq (hd::tl)) md r0 m0 r'0 m'0 (tr++tr') d)
        as HIP1 by apply (IPseq1 _ _ _ _ _ _ _ _ _ _ _ _ Hcstep1 Hcstep3 Hcstep2).
      pose (impe2_type_preservation G d pc md (Cseq (hd::tl)) r0 m0 G'
                                    md hd r0 m0 r m tr _ _ _ 
                                    Hccfg2ok Hcstep1 Hcstep2 HIP1) as Lemma61.

      assert (imm_premise (Cseq tl) md r m r'0 m'0 tr'
                          (Cseq (hd::tl)) md r0 m0 r'0 m'0 (tr++tr') d)
        as HIP2 by apply (IPseq2 _ _ _ _ _ _ _ _ _ _ _ _ Hcstep1 Hcstep3 Hcstep2).
      pose (impe2_type_preservation G d pc md (Cseq (hd::tl)) r0 m0 G'
                                    md (Cseq tl) r m r'0 m'0 tr' _ _ _
                                    Hccfg2ok Hcstep3 Hcstep2 HIP2)
        as Lemma62.

      destruct Lemma61 as [pcmid1 [Gmid1 [Gmid1' Lemma6]]]; destruct_pairs; subst.
      destruct Lemma62 as [pcmid2 [Gmid2 [Gmid2' Lemma6]]]; destruct_pairs; subst.
      assert (cconfig2_ok pcmid1 md Gmid1 d hd r0 m0 Gmid1') as seq1OK by now auto.
      assert (cconfig2_ok pcmid2 md Gmid2 d (Cseq tl) r m Gmid2') as seq2OK by now auto.
      pose (IHHcstep1 Hcstep1 Gmid1 Gmid1' pcmid1 m0 r0 hd seq1OK) as tr_same.
      pose (IHHcstep2 Hcstep3 Gmid2 Gmid2' pcmid2 m r (Cseq tl) seq2OK) as tr'_same.
      rewrite project_app_trace.
      rewrite <- tobs_sec_level_app.
      rewrite tr'_same, tr_same; auto.
      rewrite tobs_sec_level_app. rewrite project_app_trace; auto.
    (* IF *)
    -  assert (imm_premise c1 md r m r'0 m'0 tr
                           (Cif e c1 c2) md r m r'0 m'0 tr d)
         as HIP by apply (IPif  _ _ _ _ _ _ _ _ _ _ H0 Hcstep Hcstep2 Hcstep2).
       pose (impe2_type_preservation G d pc md (Cif e c1 c2) r m G'
                                     md c1 r m r'0 m'0 tr _ _ _
                                     Hccfg2ok Hcstep Hcstep2 HIP) as Lemma6.
       destruct Lemma6 as [pcmid [Gmid [Gmid' Lemma6]]]; destruct_pairs; subst.
       apply (IHHcstep Hcstep Gmid Gmid' pcmid m r c1 H1); auto.
    (* ELSE *)
    -  assert (imm_premise c2 md r m r'0 m'0 tr
                           (Cif e c1 c2) md r m r'0 m'0 tr d)
         as HIP by apply (IPelse _ _ _ _ _ _ _ _ _ _ H0 Hcstep Hcstep2).
       pose (impe2_type_preservation G d pc md (Cif e c1 c2) r m G'
                                     md c2 r m r'0 m'0 tr _ _ _
                                     Hccfg2ok Hcstep Hcstep2 HIP) as Lemma6.
       destruct Lemma6 as [pcmid [Gmid [Gmid' Lemma6]]]; destruct_pairs; subst.
       apply (IHHcstep Hcstep Gmid Gmid' pcmid m r c2 H1); auto.
    (* IFELSE-DIV *)
    - remember (VPair (Vnat n1) (Vnat n2)) as v.
      inversion Hccfg2ok; destruct_pairs; unfold_cfgs; subst; auto; try discriminate.
      inversion H; unfold_cfgs; try discriminate; subst; auto.
      assert (protected p) as Hqprotected.
      eapply econfig2_pair_protected in H20; auto. apply H0.
      assert (cterm2_ok G d r m) by now unfold cterm2_ok. apply H11.
      assert (protected (sec_level_join pc p)) by now apply (join_protected_r pc p).
      inversion H11; rewrite H11 in H22.
      assert (protected pc') as Hpc'protected.
      unfold protected. unfold sec_level_le in H22. destruct pc'; intuition.
      assert (tobs_sec_level L t1 = [] /\ tobs_sec_level L t2 = []).
      destruct n1, n2; simpl in *;
        eapply (protected_typ_no_obs_output r m) in H2;
        eapply (protected_typ_no_obs_output r m) in H3;
        try apply H14; try apply H15; auto.
      destruct_pairs.
      pose (project_merge_inv_trace t1 t2 true) as Ht1; simpl in *.
      pose (project_merge_inv_trace t1 t2 false) as Ht2; simpl in *.
      now rewrite Ht1, Ht2, H12, H16.
    (* WHILE *)
    - assert (imm_premise c md r0 m0 r m tr
                          (Cwhile e c) md r0 m0 r'0 m'0 (tr++tr') d)
        as HIP1 by apply (IPwhilet1 _ _ _ _ _ _ _ _ _ _ _ _ H0 Hcstep1 Hcstep3 Hcstep2).
      pose (impe2_type_preservation G d pc md (Cwhile e c) r0 m0 G'
                                    md c r0 m0 r m tr _ _ _ 
                                    Hccfg2ok Hcstep1 Hcstep2 HIP1) as Lemma61.

      assert (imm_premise (Cwhile e c) md r m r'0 m'0 tr'
                          (Cwhile e c) md r0 m0 r'0 m'0 (tr++tr') d)
        as HIP2 by apply (IPwhilet2 _ _ _ _ _ _ _ _ _ _ _ _ H0 Hcstep1 Hcstep3 Hcstep2).
      pose (impe2_type_preservation G d pc md (Cwhile e c) r0 m0 G'
                                    md (Cwhile e c) r m r'0 m'0 tr' _ _ _
                                    Hccfg2ok Hcstep3 Hcstep2 HIP2)
        as Lemma62.

      destruct Lemma61 as [pcmid1 [Gmid1 [Gmid1' Lemma6]]]; destruct_pairs; subst.
      destruct Lemma62 as [pcmid2 [Gmid2 [Gmid2' Lemma6]]]; destruct_pairs; subst.
      assert (cconfig2_ok pcmid1 md Gmid1 d c r0 m0 Gmid1') as seq1OK by auto.
      assert (cconfig2_ok pcmid2 md Gmid2 d (Cwhile e c) r m Gmid2') as seq2OK by auto.
      pose (IHHcstep1 Hcstep1 Gmid1 Gmid1' pcmid1 m0 r0 c seq1OK) as tr_same.
      pose (IHHcstep2 Hcstep3 Gmid2 Gmid2' pcmid2 m r (Cwhile e c) seq2OK) as tr'_same.
      rewrite project_app_trace.
      rewrite <- tobs_sec_level_app.
      rewrite tr'_same, tr_same; auto.
      rewrite tobs_sec_level_app. rewrite <- project_app_trace; auto.
    (* WHILE-DIV *)
    - remember (VPair (Vnat n1) (Vnat n2)) as v.
      inversion Hccfg2ok; destruct_pairs; unfold_cfgs; subst; auto; try discriminate.
      inversion H; unfold_cfgs; try discriminate; subst; auto.
      assert (protected p) as Hqprotected.
      eapply econfig2_pair_protected in H13; auto. apply H0.
      assert (cterm2_ok G' d r m) by now unfold cterm2_ok. apply H11.
      assert (protected (sec_level_join pc p)) by now apply (join_protected_r pc p).
      inversion H11; rewrite H11 in H19.
      assert (protected pc') as Hpc'protected.
      unfold protected. unfold sec_level_le in H19. destruct pc'; intuition.

      assert (com_type pc' md G' d Cskip G') as skip_typ by apply CTskip.
      assert (com_type pc md G' d (Cseq [c; Cwhile e c]) G') as seq_type.
      assert (com_type pc md G' d c G') as c_typ.
      apply (subsumption pc' pc md d G' G' G' G' c) in H14; auto.
      destruct pc; simpl in *; auto.
      apply (context_le_refl G'). apply (context_le_refl G').
      eapply Tseq. apply c_typ.
      eapply Tseq. apply H.
      eapply Tseqnil.
      assert (tobs_sec_level L t1 = [] /\ tobs_sec_level L t2 = []).
      destruct n1, n2; simpl in *.
      -- eapply protected_typ_no_obs_output in H2; auto. 
         eapply protected_typ_no_obs_output in H3; auto.
         apply skip_typ. auto.
         apply skip_typ. auto.
      -- eapply protected_typ_no_obs_output in H2; auto. 
         eapply protected_while_no_obs_output in H3; auto.
         apply H. apply H14. auto.
         apply skip_typ. auto.
      -- eapply protected_while_no_obs_output in H2; auto.
         eapply protected_typ_no_obs_output in H3; auto.
         apply skip_typ. auto.
         apply H. apply H14. auto.
      -- eapply protected_while_no_obs_output in H2; auto.
         eapply protected_while_no_obs_output in H3; auto.
         apply H. apply H14; auto.
         auto. apply H. apply H14. auto.
      -- destruct_pairs.
         pose (project_merge_inv_trace t1 t2 true) as Ht1; simpl in *.
         pose (project_merge_inv_trace t1 t2 false) as Ht2; simpl in *.
         now rewrite Ht1, Ht2, H12, H16.
  Qed.
 
  Lemma secure_passive : forall G G' d c,
    well_formed_spec g0 ->
    corresponds G ->
    com_type L Normal G d c G' ->
    secure_prog L d c G.
  Proof.
    unfold secure_prog.
    intros G G' d c Hg0wf Hcorr Hcomtype
           m0 mknown r' m' t tobs Hmmerge
           Hcstep2 Htobs Hind Hesc.
    rewrite Htobs.
    apply (config2_ok_implies_obs_equal minit c t (L) Normal G d
                     reg_init2 G' r' m'); auto.
    unfold cconfig2_ok; split; unfold_cfgs; auto.
    split; intros; destruct_pairs.
    - inversion H.
    - split; intros; destruct_pairs.
      -- unfold corresponds in Hcorr; destruct_pairs.
         unfold well_formed_spec in Hg0wf.
         pose (Hg0wf l) as Hgwf; destruct Hgwf; destruct_pairs.
         pose H3 as Hg0. apply (H1 l x bt rt) in Hg0.
         rewrite H0 in Hg0. inversion Hg0; subst.
         apply (diff_loc_protected l); auto.
         apply (vpair_if_diff m0 mknown v1 v2 l) in H; auto.
         apply project_merge_inv_mem in Hmmerge; destruct_pairs; subst; auto.
      -- split; intros; auto.
  Qed.
End Secure_Passive.
