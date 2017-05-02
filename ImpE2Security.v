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
Require Import ImpE2TypeSystem.
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

(*******************************************************************************
*
* SECURITY_PASSIVE
*
*******************************************************************************)

Section Secure_Passive.
  Lemma protected_typ_no_obs_output r2 m2 is_left : forall pc md d G c G' r' m' tr,
    com_type pc md G d c G' ->
    protected pc ->
    cstep md d (c,project_reg r2 is_left,project_mem m2 is_left) (r',m') tr ->
    tobs_sec_level L tr = [].
  Proof.
    intros. remember (c,project_reg r2 is_left,project_mem m2 is_left) as ccfg.
    generalize dependent pc. generalize dependent G. generalize dependent G'.
    generalize dependent c. generalize dependent r2. generalize dependent m2.
    induction H1; intros; inversion H; subst; auto;
      unfold_cfgs; unfold_cfgs; unfold_cfgs; subst.
    - inversion H2; try discriminate; subst.
      rewrite join_protected_r in H12; auto.
      unfold sec_level_le in H12; destruct sl; intuition.
    - inversion H2; try discriminate; subst.
      eapply call_fxn_typ in H4; eauto.
      eapply IHcstep; eauto.
      inversion H3; subst. rewrite join_protected_l in H6; auto.
      unfold sec_level_le in *; destruct p; try omega; auto.
    - inversion H2; try discriminate; subst.
      inversion H; subst.
      eapply (IHcstep m2 r2 c'); eauto.
    - inversion H1; try discriminate; subst.
      assert (tobs_sec_level L tr = []).
      eapply (IHcstep1 m2 r2 hd); eauto.
      assert (tobs_sec_level L tr' = []).
      pose (merge_reg r r).
      pose (merge_mem m m).
      eapply (IHcstep2 m0 r0 (Cseq tl)); eauto.
      unfold r0; rewrite project_merge_inv_reg; unfold m0; rewrite project_merge_inv_mem.
      destruct is_left; auto. 
      rewrite <- tobs_sec_level_app. rewrite H; rewrite H0; auto.
    - inversion H2; try discriminate; subst.
      eapply (IHcstep m2 r2 c1); eauto.
      rewrite join_protected_l in H15; auto.
      unfold sec_level_le in H15; destruct pc'; intuition; now unfold protected.
    - inversion H2; try discriminate; subst.
      eapply (IHcstep m2 r2 c2); eauto.
      rewrite join_protected_l in H15; auto.
      unfold sec_level_le in H15; destruct pc'; intuition; now unfold protected.
    - inversion H1; try discriminate; subst.
      assert (tobs_sec_level L tr = []).
      eapply (IHcstep1 m2 r2 c); eauto.
      rewrite join_protected_l in H11; auto.
      unfold sec_level_le in H11; destruct pc'; intuition; now unfold protected.
      assert (tobs_sec_level L tr' = []).
      pose (merge_reg r r).
      pose (merge_mem m m).
      eapply (IHcstep2 m0 r0 (Cwhile e c)); eauto.
      unfold r0; unfold m0; rewrite project_merge_inv_reg, project_merge_inv_mem.
      destruct is_left; auto.
      rewrite <- tobs_sec_level_app. rewrite H; rewrite H3; auto.
  Qed.
    
  Lemma protected_while_no_obs_output : forall pc pc' md d G e c r m r' m' tr p,
      com_type pc md G d (Cwhile e c) G ->
      com_type pc' md G d c G ->
      exp_type md G d e (Typ Tnat p) ->
      protected p ->
      sec_level_le p L \/ md <> Normal ->
      protected pc' ->
      cstep md d (Cseq [c; Cwhile e c],r,m) (r',m') tr ->
      tobs_sec_level L tr = [].
  Proof.
    intros.
    inversion H5; try discriminate; subst; unfold_cfgs; unfold_cfgs.
    inversion H8; subst. inversion H2; inversion H4; subst.
    pose (merge_reg r r). pose (merge_mem m m).
    assert (tobs_sec_level L tr0 = []).
    assert (cstep md d (hd, project_reg r1 true, project_mem m1 true) (r0, m0) tr0).
    unfold r1, m1; rewrite project_merge_inv_reg, project_merge_inv_mem; auto.
    eapply (protected_typ_no_obs_output r1 m1 true Common.H md d G hd G r0 m0 tr0); eauto.
    assert (tobs_sec_level L tr' = []).
    rewrite cstep_seq_singleton in H13.
    assert (com_type Common.H md G d (Cwhile e hd) G).
    eapply Twhile; eauto. unfold sec_level_join; unfold sec_level_le; auto.
    pose (merge_reg r0 r0). pose (merge_mem m0 m0).
    eapply (protected_typ_no_obs_output r2 m2 true Common.H md d G (Cwhile e hd) G r' m' tr');
      eauto; unfold r2, m2; rewrite project_merge_inv_reg, project_merge_inv_mem; auto.
    rewrite <- tobs_sec_level_app; rewrite H6; rewrite H7; auto.
  Qed.

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
      eapply econfig2_pair_protected in H8; auto. apply H0.
      assert (cterm2_ok G d r m) by now unfold cterm2_ok. apply H7.
      assert (protected (sec_level_join pc q)) as Hpcqprotected
          by apply (join_protected_r pc q Hqprotected).
      inversion Hpcqprotected; rewrite Hpcqprotected in H9.
      assert (protected p) as Hpprotected.
      unfold protected. unfold sec_level_le in H9; destruct p; intuition.
      clear H9 H12.
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
      apply H7; auto. auto.
      assert (tobs_sec_level L t2 = []) as t2_empty.
      eapply protected_typ_no_obs_output in H2; auto.
      apply H9; auto. auto.
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
      eapply econfig2_pair_protected in H18; auto. apply H0.
      assert (cterm2_ok G d r m) by now unfold cterm2_ok. apply H9.
      assert (protected (sec_level_join pc p)) by now apply (join_protected_r pc p).
      inversion H9; rewrite H9 in H20.
      assert (protected pc') as Hpc'protected.
      unfold protected. unfold sec_level_le in H20. destruct pc'; intuition.
      assert (tobs_sec_level L t1 = [] /\ tobs_sec_level L t2 = []).
      destruct n1, n2; simpl in *;
        eapply (protected_typ_no_obs_output r m) in H2;
        eapply (protected_typ_no_obs_output r m) in H3;
        try apply H12; try apply H13; auto.
      destruct_pairs.
      pose (project_merge_inv_trace t1 t2 true) as Ht1; simpl in *.
      pose (project_merge_inv_trace t1 t2 false) as Ht2; simpl in *.
      now rewrite Ht1, Ht2, H10, H14.
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
      eapply econfig2_pair_protected in H11; auto. apply H0.
      assert (cterm2_ok G' d r m) by now unfold cterm2_ok. apply H9.
      assert (protected (sec_level_join pc p)) by now apply (join_protected_r pc p).
      inversion H9; rewrite H9 in H17.
      assert (protected pc') as Hpc'protected.
      unfold protected. unfold sec_level_le in H17. destruct pc'; intuition.

      assert (com_type pc' md G' d Cskip G') as skip_typ by apply CTskip.
      assert (com_type pc md G' d (Cseq [c; Cwhile e c]) G') as seq_type.
      assert (com_type pc md G' d c G') as c_typ.
      apply (subsumption pc' pc md d G' G' G' G' c) in H12; auto.
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
         eapply protected_while_no_obs_output in H3; eauto.
         apply skip_typ. auto.
      -- eapply protected_while_no_obs_output in H2; auto.
         eapply protected_typ_no_obs_output in H3; eauto.
         apply H. apply H12. apply H11. auto. auto. auto.
      -- eapply protected_while_no_obs_output in H2; eauto.
         eapply protected_while_no_obs_output in H3; eauto.
      -- destruct_pairs.
         pose (project_merge_inv_trace t1 t2 true) as Ht1; simpl in *.
         pose (project_merge_inv_trace t1 t2 false) as Ht2; simpl in *.
         now rewrite Ht1, Ht2, H10, H14.
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
    apply (config2_ok_implies_obs_equal minit2 c t (L) Normal G d
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
         rewrite <- Hmmerge; repeat rewrite project_merge_inv_mem; auto.
      -- split; intros; auto.
  Qed.
End Secure_Passive.
