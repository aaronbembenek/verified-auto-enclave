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
* Soundness
*
*******************************************************************************)
Section Soundness.
  Lemma impe2_exp_sound : forall md d e r m v is_left,
      estep2 md d (e, r, m) v ->
      estep md d (e, project_reg r is_left, project_mem m is_left) (project_value v is_left).
  Proof.
    intros.
    remember (e, r, m) as ecfg.
    generalize dependent e.
    induction H; intros; try rewrite Heqecfg in H; simpl in *; try rewrite H.
    1-3: constructor; simpl; auto.
    - apply Estep_var with (x:=x); auto; subst; apply project_comm_reg.
    - destruct_conjs.
      apply contains_nat_project_nat with (is_left := is_left) in H2; destruct H2.
      apply contains_nat_project_nat with (is_left := is_left) in H3; destruct H3.
      unfold val2_add. assert (H2' := H2).
      eapply project_value_apply_op with (v2 := v2) in H2'; eauto; erewrite H2'.
      eapply Estep_add; simpl; eauto;
        [ rewrite <- H2; eapply IHestep2_1 | rewrite <- H3; eapply IHestep2_2 ];
        rewrite Heqecfg; unfold ecfg_update_exp2; auto.
    - inversion H; subst.
      apply Estep_deref with (e:=e) (l:=l) (m:=project_mem m0 is_left)
                                    (r:=project_reg r0 is_left); simpl; auto.
  Qed.

  Lemma impe2_sound : forall md d c r m r' m' t is_left,
    cstep2 md d (c, r, m) (r', m') t ->
    cstep md d (project_ccfg (c, r, m) is_left)
          (project_reg r' is_left, project_mem m' is_left) (project_trace t is_left).
  Proof.
    intros.
    remember (c, r, m) as ccfg.
    remember (r', m') as cterm.
    generalize dependent r'; generalize dependent m'.
    generalize dependent c; generalize dependent r; generalize m.
    induction H; intros; try rewrite Heqccfg in H, Heqcterm; simpl in *; inversion Heqcterm; subst.
    - constructor; auto.
    - eapply impe2_exp_sound in H0.
      eapply Cstep_assign; unfold ccfg_to_ecfg; simpl in *; eauto.
      apply project_update_comm_reg.
    - eapply impe2_exp_sound in H1.
      eapply Cstep_declassify; unfold ccfg_to_ecfg; simpl; eauto.
      apply project_update_comm_reg.
    - eapply impe2_exp_sound in H0; eapply impe2_exp_sound in H1.
      eapply Cstep_update; unfold ccfg_to_ecfg; simpl; eauto.
      now apply project_update_comm_mem.
    - eapply impe2_exp_sound in H0.
      eapply Cstep_output; unfold ccfg_to_ecfg; simpl; eauto. 
      destruct sl; auto.
    - eapply impe2_exp_sound in H0.
      eapply Cstep_call; unfold ccfg_to_ecfg; simpl; eauto.
      eapply IHcstep2; unfold_cfgs; eauto.
    - apply impe2_exp_sound with (is_left := is_left) in H0; simpl in *;
        rewrite project_merge_inv_reg; rewrite project_merge_inv_mem.
      destruct is_left;
        [apply Cstep_call with (e:=e) (c:=c1) | apply Cstep_call with (e:=e) (c:=c2)]; auto;
      unfold ccfg_update_com; simpl; rewrite project_merge_inv_trace; auto.
    - eapply Cstep_enclave; eauto.
    - eapply Cstep_seq_nil; eauto. 
    - eapply Cstep_seq_hd; eauto.
      eapply IHcstep2_1; eauto.
      unfold ccfg_update_com2; eauto.
      eapply IHcstep2_2; eauto.
      now apply project_app_trace.
    - eapply impe2_exp_sound in H0.
      eapply Cstep_if; unfold ccfg_to_ecfg; simpl; eauto.
      eapply IHcstep2; unfold_cfgs; simpl; eauto.
    - eapply impe2_exp_sound in H0.
      eapply Cstep_else; unfold_cfgs; simpl; eauto.
    - apply impe2_exp_sound with (is_left := is_left) in H0; simpl in *.
      destruct H1; apply l2_zero_or_one in H1; apply l2_zero_or_one in H4.
        rewrite project_merge_inv_reg; rewrite project_merge_inv_mem;
          unfold cleft in *; unfold cright in *; subst.
        destruct is_left; [destruct H1 | destruct H4]; rewrite H in *.
        1,3: apply Cstep_else with (e := e) (c1 := c1) (c2 := c2).
        7,8: apply Cstep_if with (e := e) (c1 := c1) (c2 := c2).
        all: auto; unfold_cfgs; simpl in *; try rewrite project_merge_inv_trace; auto.
    - rewrite project_app_trace; simpl in *; subst.
      eapply Cstep_while_t; unfold_cfgs; simpl; eauto.
      now apply impe2_exp_sound with (is_left := is_left) in H0.
    - eapply Cstep_while_f; unfold_cfgs; simpl; eauto.      
      eapply impe2_exp_sound in H0; eauto.
    - apply impe2_exp_sound with (is_left := is_left) in H0; simpl in *;
        rewrite project_merge_inv_reg; rewrite project_merge_inv_mem; destruct_conjs;
          apply l2_zero_or_one in H1; apply l2_zero_or_one in H4;
            unfold cleft in *; unfold cright in *.
      destruct is_left; [destruct H1; rewrite H1 in * | destruct H4; rewrite H4 in *];
        rewrite project_merge_inv_trace; subst; unfold_cfgs; simpl in *.
      1,2: inversion H2; subst; try discriminate.
      3,4: inversion H3; subst; try discriminate.
      1,3: eapply Cstep_while_f; unfold_cfgs; simpl; eauto.
      all: inversion H5; subst; simpl in *; subst; eapply Cstep_while_t; simpl; eauto;
        apply -> cstep_seq_singleton; auto.
  Qed.

End Soundness.

Section Completeness.
  Lemma impe2_exp_complete : forall md d e r m v'1 v'2,
    estep md d (e, project_reg r true, project_mem m true) v'1 ->
    estep md d (e, project_reg r false, project_mem m false) v'2 ->
    exists v', estep2 md d (e, r, m) v' /\
          (project_value v' true = v'1) /\
          (project_value v' false = v'2).
  Proof.
    Local Ltac invert_estep :=
      match goal with
      | [ H : estep _ _ _ _ |- _ ] => inversion H; subst; try discriminate; simpl in *
      end.
    
    intros.
    remember (e, project_reg r true, project_mem m true) as ecfg1.
    generalize dependent e.
    revert v'2.
    induction H; intros; try rewrite Heqecfg1 in H0; simpl in *;
      invert_estep; subst; try discriminate.
    - inversion H1; subst; eexists; repeat split.
      econstructor; eauto.
      all: cbn; auto.
    - inversion H1; subst; eexists; repeat split.
      eapply Estep2_loc; eauto.
      all: now cbn.
    - inversion H1; subst; eexists; repeat split.
      eapply Estep2_lambda; eauto.
      all: now cbn.
    - inversion H2; subst; eexists; repeat split.
      eapply Estep2_var; eauto.
    - inversion H3; subst.
      edestruct IHestep1; eauto; destruct_conjs; subst.
      edestruct IHestep2; eauto; destruct_conjs; subst.
      eexists; repeat split.
      eapply Estep2_add; eauto.
      split; [destruct x | destruct x0]; simpl in *; subst; unfold contains_nat;
        [left | right | left | right]; eexists; eauto.
      1,2: apply project_value_apply_op; auto.
    - inversion H4; subst.
      inversion Heqecfg1; subst.
      edestruct IHestep; eauto; destruct_conjs.
      eexists; repeat split.
      eapply Estep2_deref; eauto.
      all: eapply no_location_pairs in H6; subst; simpl in *; inversion H1; subst; eauto.
  Qed.
      
  Lemma impe2_complete : forall md d c r m r'1 m'1 t'1 r'2 m'2 t'2,
      (cstep md d (project_ccfg (c, r, m) true) (r'1, m'1) t'1 /\
      cstep md d (project_ccfg (c, r, m) false) (r'2, m'2) t'2) ->
      exists r' m' t',
        cstep2 md d (c, r, m) (r', m') t' /\
        (project_reg r' true) = r'1 /\
        (project_mem m' true) = m'1 /\
        (project_trace t' true) = t'1 /\
        (project_reg r' false) = r'2 /\
        (project_mem m' false) = m'2 /\
        (project_trace t' false) = t'2.
  Proof.
    Local Ltac destruct_merge_inv :=
      repeat
        match goal with
        | [ |- project_mem (merge_mem _ _) _ = _ ] => rewrite project_merge_inv_mem; auto
        | [ |- project_reg (merge_reg _ _) _ = _ ] => rewrite project_merge_inv_reg; auto
        | [ |- project_trace (merge_trace _) _ = _ ] => rewrite project_merge_inv_trace; auto
        | _ => idtac
        end.
    
    Local Ltac invert_cstep :=
      match goal with
      | [ H : cstep _ _ _ _ _ |- _ ] => inversion H; subst; try discriminate; simpl in *
      end.

    Local Ltac destruct_exp_complete H :=
      eapply impe2_exp_complete in H; eauto; destruct H; destruct_conjs.

    Local Ltac e2_determinism x1 x2 H :=
      assert (x1 = x2) by (apply estep2_deterministic with (v1 := x2) in H; auto); subst.

    intros; destruct H.
    remember (project_ccfg (c, r, m) true) as ccfg1.
    remember (r'1, m'1) as cterm1.
    generalize dependent r'1; generalize dependent m'1.
    generalize dependent r'2; generalize dependent m'2.
    generalize dependent c; generalize dependent r; generalize dependent m.
    revert t'2.
    induction H; intros; unfold project_ccfg in *; rewrite Heqccfg1 in *;
      simpl in *; invert_cstep.
    (* SKIP *)
    - do 3 eexists; repeat split; inversion Heqcterm1; subst; eauto.
      econstructor; auto.
      all: now cbn.
    (* ASSIGN *)
    - inversion H5; subst.
      destruct_exp_complete H9.
      do 3 eexists; repeat split; eauto.
      eapply Cstep2_assign with (x := x0) (e := e0) (v := x); eauto.
      all: simpl; auto.
      1,4: rewrite project_update_comm_reg; simpl; unfold project_ccfg; simpl.
      all: congruence.
    (* DECLASSIFY *)
    - inversion H6; subst.
      destruct_exp_complete H1.
      do 3 eexists; repeat split; eauto.
      eapply Cstep2_declassify with (x := x0) (v := x); eauto.
      all: simpl; auto.
      1,3: rewrite project_update_comm_reg; simpl; unfold project_ccfg; simpl.
      all: congruence.
    (* UPDATE *)
    - inversion H6; subst.
      destruct_exp_complete H11; destruct_exp_complete H7.
      assert (x0 = VSingle (Vloc l)) by (eapply no_location_pairs in H5; eauto);
        subst; simpl in *; subst.
      do 3 eexists; repeat split; simpl; eauto.
      eapply Cstep2_update; eauto.
      congruence.
      all: inversion H8; subst.
      1,3: inversion Heqcterm1; apply project_update_comm_mem.
      all: now simpl.
    (* OUTPUT *)
    - inversion H5; subst.
      destruct_exp_complete H0.
      do 3 eexists; repeat split; eauto.
      eapply Cstep2_output with (e := e0); eauto.
      all: simpl; auto; congruence.
    (* CALL *)
    - inversion H5; subst.
      destruct_exp_complete H9.
      destruct x; subst.
      + simpl in *. assert (c = c1) by congruence; subst.
        edestruct IHcstep; unfold_cfgs; simpl; eauto. 
        do 2 destruct H3; destruct_conjs.
        exists x; exists x0; exists x1; repeat split.
        apply Cstep2_call with (e := e0) (c := c1); auto.
        unfold ccfg_to_ecfg2; simpl in *; subst; auto.
        all: congruence.
      + exists (merge_reg r'1 r'2); exists (merge_mem m'1 m'2); exists (merge_trace (tr, t'2)); repeat split.
        eapply Cstep2_call_div; unfold_cfgs; simpl in *; subst; eauto.
        1,2: inversion Heqcterm1; subst; auto.
        all: destruct_merge_inv.
    (* ENCLAVE *)
    - inversion H9; subst.
      edestruct IHcstep; eauto.
      do 3 destruct H; destruct_conjs.
      exists x; exists x0; exists x1; repeat split; auto.
      eapply Cstep2_enclave; eauto.
    (* SEQ_NIL *)
    - exists r; exists m; exists []; repeat split.
      apply Cstep2_seq_nil; auto.
      all: inversion Heqcterm1; now subst.
    (* SEQ_HD *)
    - inversion H6; inversion Heqcterm1; subst; unfold_cfgs; simpl in *.
      edestruct IHcstep1; eauto.
      do 2 destruct H; destruct_conjs; subst.
      edestruct IHcstep2; eauto.
      do 2 destruct H2; destruct_conjs; subst.
      do 3 eexists; repeat split; eauto.
      eapply Cstep2_seq_hd; eauto.
      all: rewrite project_app_trace; auto.
    (* IF BOTH TRUE *)
    - inversion H5; subst.
      destruct_exp_complete H0.
      destruct x; subst.
      + simpl in *; subst.
        destruct IHcstep with (c := c0) (m'1 := m') (r'1 := r') (m'2 := m'2) (r'2 := r'2)
                                        (t'2 := t'2) (m0 := m) (r0 := r); auto.
        do 3 destruct H0; destruct_conjs.
        exists x; exists x0; exists x1; repeat split; auto.
        apply Cstep2_if with (e := e0) (c1 := c0) (c2 := c3); auto.
        all: inversion Heqcterm1; subst; auto.
      + exists (merge_reg r'1 r'2); exists (merge_mem m'1 m'2); exists (merge_trace (tr, t'2)); repeat split.
        apply Cstep2_if_div with (e := e0) (c1 := c0) (c2 := c3) (n1 := 1) (n2 := 1)
                                           (r1 := r') (m1 := m') (r2 := r'2) (m2 := m'2); auto.
        unfold_cfgs; simpl in *; now subst.
        all: inversion Heqcterm1; subst; auto; destruct_merge_inv.
    (* IF TRUE, FALSE *)
    - inversion H5; subst.
      destruct_exp_complete H0.
      destruct x; subst.
      + simpl in *; subst; discriminate.
      + exists (merge_reg r'1 r'2); exists (merge_mem m'1 m'2); exists (merge_trace (tr, t'2)); repeat split.
        apply Cstep2_if_div with (e := e0) (c1 := c0) (c2 := c3) (n1 := 1) (n2 := 0)
                                           (r1 := r') (m1 := m') (r2 := r'2) (m2 := m'2); auto.
        unfold_cfgs; simpl in *; now subst.
        all: inversion Heqcterm1; subst; auto; destruct_merge_inv.
    (* IF FALSE, TRUE *)
    - inversion H5; subst.
      destruct_exp_complete H0.
      destruct x; subst.
      + simpl in *; subst; discriminate.
      + exists (merge_reg r'1 r'2); exists (merge_mem m'1 m'2); exists (merge_trace (tr, t'2)); repeat split.
        apply Cstep2_if_div with (e := e0) (c1 := c0) (c2 := c3) (n1 := 0) (n2 := 1)
                                           (r1 := r') (m1 := m') (r2 := r'2) (m2 := m'2); auto.
        unfold_cfgs; simpl in *; now subst.
        all: inversion Heqcterm1; subst; auto; destruct_merge_inv.    
    - inversion H5; subst.
      destruct_exp_complete H0.
      destruct x; subst.
      + simpl in *; subst.
        destruct IHcstep with (c := c3) (m'1 := m') (r'1 := r') (m'2 := m'2) (r'2 := r'2)
                                        (t'2 := t'2) (m0 := m) (r0 := r); auto.
        do 3 destruct H0; destruct_conjs.
        exists x; exists x0; exists x1; repeat split; auto.
        apply Cstep2_else with (e := e0) (c1 := c0) (c2 := c3); auto.
        all: inversion Heqcterm1; subst; auto.
      + exists (merge_reg r'1 r'2); exists (merge_mem m'1 m'2); exists (merge_trace (tr, t'2)); repeat split.
        apply Cstep2_if_div with (e := e0) (c1 := c0) (c2 := c3) (n1 := 0) (n2 := 0)
                                           (r1 := r') (m1 := m') (r2 := r'2) (m2 := m'2); auto.
        unfold_cfgs; simpl in *; now subst.
        all: inversion Heqcterm1; subst; auto; destruct_merge_inv.
    (* WHILE BOTH TRUE *)
    - inversion H6; subst.
      destruct_exp_complete H7.
      destruct x; subst.
      + inversion Heqcterm1; subst; unfold_cfgs; simpl in *.
        edestruct IHcstep1; eauto.
        do 2 destruct H7; destruct_conjs; subst.
        edestruct IHcstep2; eauto.
        do 2 destruct H4; destruct_conjs; subst.
        do 3 eexists; repeat split; eauto.
        eapply Cstep2_while_t; eauto.
        all: now rewrite project_app_trace.
      + exists (merge_reg r'1 r'2); exists (merge_mem m'1 m'2);
          exists (merge_trace (tr ++ tr', tr0 ++ tr'0)); repeat split.
        eapply Cstep2_while_div; eauto.
        all: unfold_cfgs; simpl in *; inversion Heqcterm1; subst; auto.
        1,2: eapply Cstep_seq_hd; simpl; eauto; apply cstep_seq_singleton; auto.
        all: destruct_merge_inv.
    (* WHILE TRUE, FALSE *)
    - inversion H9; subst.
      destruct_exp_complete H0.
      destruct x; subst.
      + simpl in *; subst; discriminate.
      + exists (merge_reg r'1 (project_reg r0 false)); exists (merge_mem m'1 (project_mem m0 false));
          exists (merge_trace (tr ++ tr', [])); repeat split.
        simpl in *; subst.
        eapply Cstep2_while_div; eauto.
        all: unfold_cfgs; simpl in *; inversion Heqcterm1; subst; auto.
        eapply Cstep_seq_hd; simpl; eauto; apply cstep_seq_singleton; auto.
        constructor; auto.
        all: destruct_merge_inv.
    (* WHILE FALSE, TRUE *)
    - inversion H4; subst.
      destruct_exp_complete H5.
      destruct x; subst.
      + simpl in *; subst; discriminate.
      + unfold_cfgs; simpl in *; subst.
        exists (merge_reg r'1 r'2); exists (merge_mem m'1 m'2);
          eexists; inversion Heqcterm1; subst; repeat split; eauto.        
        eapply Cstep2_while_div; eauto.
        all: unfold_cfgs; simpl in *; subst; auto.
        econstructor; eauto.
        eapply Cstep_seq_hd; simpl; eauto; apply cstep_seq_singleton; eauto.
        all: destruct_merge_inv.
    (* WHILE BOTH FALSE *)
    - inversion H7; subst.
      destruct_exp_complete H9.
      destruct x; subst.
      + inversion Heqcterm1; subst; unfold_cfgs; simpl in *; subst.
        do 3 eexists; repeat split; eauto.
        eapply Cstep2_while_f; eauto.
        all: now cbn.
      + exists (merge_reg (project_reg r true) (project_reg r false));
          exists  (merge_mem (project_mem m true) (project_mem m false));
          eexists; inversion Heqcterm1; subst; unfold_cfgs; simpl in *; subst;
          repeat split; eauto.
        eapply Cstep2_while_div; eauto.
        all: unfold_cfgs; simpl in *; subst; auto.
        1,2: econstructor; auto.
        all: destruct_merge_inv.
  Qed.
  
End Completeness.