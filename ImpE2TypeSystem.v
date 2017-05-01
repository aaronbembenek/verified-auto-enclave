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
Require Import ImpE2SecurityHelpers.

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

Section Config_Preservation.

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
    - inversion H3; try discriminate; subst.
      remember (VPair (Vlambda md c1) (Vlambda md c2)) as v.
      assert (protected q) as qP.
      eapply (econfig2_pair_protected md G d e q r m v
                                      (Vlambda md c1) (Vlambda md c2)
                                      (Tlambda Gm p md Gp)); eauto.
      unfold cterm2_ok in *; auto.
      assert (protected p) as pP. apply sec_level_join_le_r in H9. inversion qP; subst.
      unfold sec_level_le in H9; destruct p; try omega; auto.
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
      -- destruct (assign_in_dec x t1), (assign_in_dec x t2).
         --- pose (assignment_more_secure Common.H md d c1 G G' x bt p
             (project_reg r true) (project_mem m true)
                                  r1 m1 t1 lifted_c1typ H1 a H12). 
             destruct p. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (assignment_more_secure Common.H md d c1 G G' x bt p
                                          (project_reg r true) (project_mem m true)
                                          r1 m1 t1 lifted_c1typ H1 a H12). 
             destruct p. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (assignment_more_secure Common.H md d c2 G G' x bt p
                                          (project_reg r false) (project_mem m false)
                                          r2 m2 t2 lifted_c2typ H2 a H12). 
             destruct p. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (no_assign_pair_reg_context_constant
                     md d (Ccall e) r m (merge_reg r1 r2) (merge_mem m1 m2)
                     (merge_trace (t1, t2)) x pc G G' v1 v2 Hcstep H3).
             assert (~assign_in x t1 /\ ~assign_in x t2) as noassign by auto.
             repeat rewrite project_merge_inv_trace in a.
             apply a in noassign; destruct_pairs; auto.
             apply (H4 x v1 v2 bt p); auto. split; auto. rewrite H13; auto. rewrite H14; auto.
      -- split; auto. intros; destruct_pairs.
         destruct (update_in_dec l t1), (update_in_dec l t2).
         --- pose (update_more_secure Common.H md d c1 G G' l bt p rt
             (project_reg r true) (project_mem m true)
                                  r1 m1 t1 lifted_c1typ H1 u H12). 
             destruct p. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (update_more_secure Common.H md d c1 G G' l bt p rt
                                          (project_reg r true) (project_mem m true)
                                          r1 m1 t1 lifted_c1typ H1 u H12). 
             destruct p. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (update_more_secure Common.H md d c2 G G' l bt p rt
                                          (project_reg r false) (project_mem m false)
                                          r2 m2 t2 lifted_c2typ H2 u H12). 
             destruct p. unfold sec_level_le in *. omega.
             unfold protected; auto.
         --- pose (no_update_mem_constant
                     md d (Ccall e) r m (merge_reg r1 r2) (merge_mem m1 m2)
                     (merge_trace (t1, t2)) l pc G G' Hcstep H3).
             assert (~update_in l t1 /\ ~update_in l t2) as noupdate by auto.
             repeat rewrite project_merge_inv_trace in e0.
             apply e0 in noupdate; destruct_pairs.
             apply (H5 l v1 v2 bt p rt). split; auto. rewrite noupdate; auto. 
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
    - inversion H4; try discriminate; subst.
      assert (protected p).
      remember (VPair (Vnat n1) (Vnat n2)) as v.
      eapply econfig2_pair_protected. apply Heqv. apply H18. apply H0.
      assert (cterm2_ok G d r m) as Hcterm2_ok.
      unfold cterm2_ok in *; auto.
      apply Hcterm2_ok.
      (* get that pc' is protected *)
      assert (protected (sec_level_join pc p)) by now apply (join_protected_r pc p).
      inversion H10; subst. rewrite H14 in H20.
      destruct pc'; unfold sec_level_le in H20. omega.
      clear H20 H H10 H14.
      split; intros; destruct_pairs. unfold cleft in *. unfold cright in *.
      destruct n1; destruct n2; destruct (assign_in_dec x t1), (assign_in_dec x t2);
      (* see if there was an assignment in either c1 or c2 to change the registers *)
      [pose (assignment_more_secure Common.H md d c2 G G' x bt p0
                                    (project_reg r true) (project_mem m true)
                                    r1 m1 t1 H13 H2 a H10)
      | pose (assignment_more_secure Common.H md d c2 G G' x bt p0
                                     (project_reg r true) (project_mem m true)
                                     r1 m1 t1 H13 H2 a H10)
      | pose (assignment_more_secure Common.H md d c2 G G' x bt p0
                                     (project_reg r false) (project_mem m false)
                                     r2 m2 t2 H13 H3 a H10) |
      | pose (assignment_more_secure Common.H md d c2 G G' x bt p0
                                    (project_reg r true) (project_mem m true)
                                    r1 m1 t1 H13 H2 a H10)
      | pose (assignment_more_secure Common.H md d c2 G G' x bt p0
                                     (project_reg r true) (project_mem m true)
                                     r1 m1 t1 H13 H2 a H10)
      | pose (assignment_more_secure Common.H md d c1 G G' x bt p0
                                     (project_reg r false) (project_mem m false)
                                     r2 m2 t2 H12 H3 a H10) |
      | pose (assignment_more_secure Common.H md d c1 G G' x bt p0
                                     (project_reg r true) (project_mem m true)
                                     r1 m1 t1 H12 H2 a H10)
      | pose (assignment_more_secure Common.H md d c1 G G' x bt p0
                                     (project_reg r true) (project_mem m true)
                                     r1 m1 t1 H12 H2 a H10) 
      | pose (assignment_more_secure Common.H md d c2 G G' x bt p0
                                    (project_reg r false) (project_mem m false)
                                    r2 m2 t2 H13 H3 a H10) |
      | pose (assignment_more_secure Common.H md d c1 G G' x bt p0
                                     (project_reg r true) (project_mem m true)
                                     r1 m1 t1 H12 H2 a H10)
      | pose (assignment_more_secure Common.H md d c1 G G' x bt p0
                                     (project_reg r true) (project_mem m true)
                                     r1 m1 t1 H12 H2 a H10) 
      | pose (assignment_more_secure Common.H md d c1 G G' x bt p0
                                    (project_reg r false) (project_mem m false)
                                    r2 m2 t2 H12 H3 a H10) |
      ].
      1-3,5-7,9-11,13-15: destruct p0; [unfold sec_level_le in *; omega | unfold protected; auto].
      1-4: 
        pose (no_assign_pair_reg_context_constant
                md d (Cif e c1 c2) r m (merge_reg r1 r2) (merge_mem m1 m2)
                (merge_trace (t1, t2)) x pc G G' v1 v2 Hcstep H4);
        assert (~assign_in x t1 /\ ~assign_in x t2) as noassign by auto;
        pose (no_assign_pair_reg_context_constant
                md d (Cif e c1 c2) r m (merge_reg r1 r2) (merge_mem m1 m2)
                (merge_trace (t1, t2)) x pc G G' v1 v2
                Hcstep H4);
        repeat rewrite project_merge_inv_trace in a;
        apply a in noassign; destruct_pairs; auto;
          apply (H5 x v1 v2 bt p0); split; try rewrite H11; try rewrite H14; auto.

      (* Same thing for updates *)
      split; auto; intros; destruct_pairs.
      destruct n1; destruct n2; destruct (update_in_dec l t1), (update_in_dec l t2);
      (* see if there was an update in either c1 or c2 to change the registers *)
      [pose (update_more_secure Common.H md d c2 G G' l bt p0 rt
                                    (project_reg r true) (project_mem m true)
                                    r1 m1 t1 H13 H2 u H10)
      | pose (update_more_secure Common.H md d c2 G G' l bt p0 rt
                                     (project_reg r true) (project_mem m true)
                                     r1 m1 t1 H13 H2 u H10)
      | pose (update_more_secure Common.H md d c2 G G' l bt p0 rt
                                     (project_reg r false) (project_mem m false)
                                     r2 m2 t2 H13 H3 u H10) |
      | pose (update_more_secure Common.H md d c2 G G' l bt p0 rt
                                    (project_reg r true) (project_mem m true)
                                    r1 m1 t1 H13 H2 u H10)
      | pose (update_more_secure Common.H md d c2 G G' l bt p0 rt
                                     (project_reg r true) (project_mem m true)
                                     r1 m1 t1 H13 H2 u H10)
      | pose (update_more_secure Common.H md d c1 G G' l bt p0 rt
                                     (project_reg r false) (project_mem m false)
                                     r2 m2 t2 H12 H3 u H10) |
      | pose (update_more_secure Common.H md d c1 G G' l bt p0 rt
                                     (project_reg r true) (project_mem m true)
                                     r1 m1 t1 H12 H2 u H10)
      | pose (update_more_secure Common.H md d c1 G G' l bt p0 rt
                                     (project_reg r true) (project_mem m true)
                                     r1 m1 t1 H12 H2 u H10) 
      | pose (update_more_secure Common.H md d c2 G G' l bt p0 rt
                                    (project_reg r false) (project_mem m false)
                                    r2 m2 t2 H13 H3 u H10) |
      | pose (update_more_secure Common.H md d c1 G G' l bt p0 rt
                                     (project_reg r true) (project_mem m true)
                                     r1 m1 t1 H12 H2 u H10)
      | pose (update_more_secure Common.H md d c1 G G' l bt p0 rt
                                     (project_reg r true) (project_mem m true)
                                     r1 m1 t1 H12 H2 u H10) 
      | pose (update_more_secure Common.H md d c1 G G' l bt p0 rt
                                    (project_reg r false) (project_mem m false)
                                    r2 m2 t2 H12 H3 u H10) |
      ].
      1-3,5-7,9-11,13-15: destruct p0; [unfold sec_level_le in *; omega | unfold protected; auto].
      1-4: 
        pose (no_update_mem_constant
                md d (Cif e c1 c2) r m (merge_reg r1 r2) (merge_mem m1 m2)
                (merge_trace (t1, t2)) l pc G G' Hcstep H4);
        assert (~update_in l t1 /\ ~update_in l t2) as noupdate by auto;
        repeat rewrite project_merge_inv_trace in e0;
        apply e0 in noupdate; destruct_pairs;
          apply (H6 l v1 v2 bt p0 rt); split; try rewrite noupdate; auto.
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
    - inversion H4; try discriminate; subst.
      assert (protected p).
      remember (VPair (Vnat n1) (Vnat n2)) as v.
      eapply econfig2_pair_protected; eauto. 
      assert (cterm2_ok G' d r m) as Hcterm2_ok.
      unfold cterm2_ok in *; auto.
      apply Hcterm2_ok.
      (* get that pc' is protected *)
      assert (protected (sec_level_join pc p)) by now apply (join_protected_r pc p).
      inversion H10; subst. rewrite H14 in H17.
      destruct pc'; unfold sec_level_le in H17. omega.
      split; intros; destruct_pairs; auto. unfold cleft in *; unfold cright in *.
      destruct n1; destruct n2; destruct (assign_in_dec x t1), (assign_in_dec x t2).
      1-3,5-6,9,11:
        inversion H2; try discriminate; subst; inversion H3; try discriminate; subst;
        unfold assign_in in *; destruct a as [x1 [x2 a]];
          try destruct a0 as [x3 [x4 a0]];
          simpl in *; try omega.
      1,3,5,9: pose (no_assign_pair_reg_context_constant
                       md d (Cwhile e c) r m (merge_reg r1 r2) (merge_mem m1 m2)
                       (merge_trace (t1, t2)) x pc G' G' v1 v2 Hcstep H4);
        assert (~assign_in x t1 /\ ~assign_in x t2) as noassign by auto;
        repeat rewrite project_merge_inv_trace in a; 
        apply a in noassign; destruct_pairs; auto;
          apply (H5 x v1 v2 bt p0); split; try rewrite H16; try rewrite H18; auto.
      1,5: inversion H3; try discriminate; unfold_cfgs; subst; unfold_cfgs;
        inversion H20; subst; rewrite cstep_seq_singleton in H25;
          assert (com_type Common.H md G' d (Cwhile e hd) G') as cwhiletyp
            by now eapply Twhile; eauto.
      1,2: apply assign_in_app in a; try destruct a as [a1 | a2];
           [pose (assignment_more_secure Common.H md d hd G' G' x bt p0
                                         (project_reg r false) (project_mem m false)
                                         r0 m0 tr H12 H21 a1 H15) |
            pose (assignment_more_secure Common.H md d (Cwhile e hd) G' G' x bt p0
                                         r0 m0 r2 m2 tr' cwhiletyp H25 a2 H15)].
      1-4: destruct p0; unfold sec_level_le in *; [omega | unfold protected in *; auto].
      1-3: inversion H2; try discriminate; unfold_cfgs; subst; unfold_cfgs;
           inversion H20; subst; rewrite cstep_seq_singleton in H25;         
             assert (com_type Common.H md G' d (Cwhile e hd) G') as cwhiletyp
               by now eapply Twhile; eauto.
      1-3: apply assign_in_app in a; destruct a as [a1 | a2];
           [pose (assignment_more_secure Common.H md d hd G' G' x bt p0
                                         (project_reg r true) (project_mem m true)
                                      r0 m0 tr H12 H21 a1 H15) |
         pose (assignment_more_secure Common.H md d (Cwhile e hd) G' G' x bt p0
                                      r0 m0 r1 m1 tr' cwhiletyp H25 a2 H15)].
      1-6: destruct p0; unfold sec_level_le in *; [omega | unfold protected in *; auto].

      (* same thing for updates...*)
      split; intros; destruct_pairs; auto.
      destruct n1; destruct n2; destruct (update_in_dec l t1), (update_in_dec l t2).
      1-3,5-6,9,11:
        inversion H2; try discriminate; subst; inversion H3; try discriminate; subst;
        unfold update_in in *; destruct u as [x1 [x2 a]];
          try destruct u0 as [x3 [x4 a0]];
          simpl in *; try omega.
      1,3,5,9: pose (no_update_mem_constant
                       md d (Cwhile e c) r m (merge_reg r1 r2) (merge_mem m1 m2)
                       (merge_trace (t1, t2)) l pc G' G' Hcstep H4);
        assert (~update_in l t1 /\ ~update_in l t2) as noupdate by auto;
        repeat rewrite project_merge_inv_trace in e0;
        apply e0 in noupdate; destruct_pairs;
          apply (H6 l v1 v2 bt p0 rt); split; try rewrite noupdate; auto.
      1,5: inversion H3; try discriminate; unfold_cfgs; subst; unfold_cfgs;
        inversion H20; subst; rewrite cstep_seq_singleton in H25;
          assert (com_type Common.H md G' d (Cwhile e hd) G') as cwhiletyp
            by now eapply Twhile; eauto.
      1,2: apply update_in_app in u; try destruct u as [a1 | a2];
           [pose (update_more_secure Common.H md d hd G' G' l bt p0 rt
                                         (project_reg r false) (project_mem m false)
                                         r0 m0 tr H12 H21 a1 H15) |
            pose (update_more_secure Common.H md d (Cwhile e hd) G' G' l bt p0 rt
                                         r0 m0 r2 m2 tr' cwhiletyp H25 a2 H15)].
      1-4: destruct p0; unfold sec_level_le in *; [omega | unfold protected in *; auto].
      1-3: inversion H2; try discriminate; unfold_cfgs; subst; unfold_cfgs;
           inversion H20; subst; rewrite cstep_seq_singleton in H25;         
             assert (com_type Common.H md G' d (Cwhile e hd) G') as cwhiletyp
               by now eapply Twhile; eauto.
      1-3: apply update_in_app in u; destruct u as [a1 | a2];
           [pose (update_more_secure Common.H md d hd G' G' l bt p0 rt
                                         (project_reg r true) (project_mem m true)
                                      r0 m0 tr H12 H21 a1 H15) |
         pose (update_more_secure Common.H md d (Cwhile e hd) G' G' l bt p0 rt
                                      r0 m0 r1 m1 tr' cwhiletyp H25 a2 H15)].
      1-6: destruct p0; unfold sec_level_le in *; [omega | unfold protected in *; auto].
  Qed.  

  Lemma impe2_type_preservation (G: context) (d: loc_mode) :
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
  
End Config_Preservation.
