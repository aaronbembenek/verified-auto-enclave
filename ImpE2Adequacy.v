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
      pose (project_value_apply_op op v1 v2 x x0 is_left H2 H3); rewrite e0.
      apply Estep_binop with (e1:=e1) (e2:=e2); simpl; auto;
        [rewrite <- H2; apply (IHestep2_1 e1) | rewrite <- H3; apply (IHestep2_2 e2)];
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
    generalize dependent r'.
    generalize dependent m'.
    generalize dependent c.
    induction H; intros; try rewrite Heqccfg in H, Heqcterm; simpl in *; inversion Heqcterm; subst.
    - constructor; auto.
    - apply impe2_exp_sound with (is_left:=is_left) in H0.
      apply Cstep_assign with (x:=x) (e:=e) (v := project_value v is_left); auto.
      unfold ccfg_to_ecfg; simpl in *; auto.
      apply project_update_comm_reg.
    - apply impe2_exp_sound with (is_left:=is_left) in H1.
      apply Cstep_declassify with (x:=x) (e:=e) (v :=(project_value v is_left)); auto.
      apply project_update_comm_reg.
    - apply impe2_exp_sound with (is_left:=is_left) in H0.
      apply impe2_exp_sound with (is_left:=is_left) in H1.
      apply Cstep_update with (e1 := e1) (e2 := e2) (l := l) (v := project_value v is_left); auto.
      now apply project_update_comm_mem.
    - apply impe2_exp_sound with (is_left:=is_left) in H0; simpl in *.
      apply Cstep_output with (e := e); auto.
      destruct sl; auto.
    - apply impe2_exp_sound with (is_left:=is_left) in H0; simpl in *.
      apply Cstep_call with (e := e) (c := c); auto.
      apply IHcstep2 with (c1 := c); auto.
    - apply impe2_exp_sound with (is_left := is_left) in H0; simpl in *;
        apply project_merge_inv_reg in H3; apply project_merge_inv_mem in H4.
      destruct_conjs; subst.
      destruct is_left;
        [apply Cstep_call with (e:=e) (c:=c1) | apply Cstep_call with (e:=e) (c:=c2)]; auto;
      unfold ccfg_update_com; simpl; rewrite project_merge_inv_trace; auto.
    - apply Cstep_enclave with (enc := enc) (c := c); auto.
      apply IHcstep2 with (c1 := c); auto.
    - apply Cstep_seq_nil; auto. 
    - apply Cstep_seq_hd with (hd:=hd) (tl:=tl)
                                       (r:=(project_reg r0 is_left))
                                       (m:=(project_mem m0 is_left))
                                       (tr:=(project_trace tr is_left))
                                       (tr':=(project_trace tr' is_left)); auto.
      apply IHcstep2_1 with (c0:=hd); auto.
      apply IHcstep2_2 with (c:=Cseq tl); auto.
      admit.
      (* XXX: getting stuck with a weird induction hypothesis... maybe generalizing wrong *)
      now apply project_app_trace.
    - apply impe2_exp_sound with (is_left := is_left) in H0; simpl in *.
      apply Cstep_if with (e:=e) (c1:=c1) (c2:=c2); auto.
      apply IHcstep2 with (c0 := c1); auto.
    - apply impe2_exp_sound with (is_left := is_left) in H0; simpl in *.
      apply Cstep_else with (e:=e) (c1:=c1) (c2:=c2); auto.
      apply IHcstep2 with (c0 := c2); auto.
    - apply impe2_exp_sound with (is_left := is_left) in H0; simpl in *.
      destruct H1; apply l2_zero_or_one in H1; apply l2_zero_or_one in H6.
        apply project_merge_inv_reg in H4; apply project_merge_inv_mem in H5;
          destruct_conjs; unfold cleft in *; unfold cright in *; subst.
        destruct is_left; [destruct H1 | destruct H6]; rewrite H in *.
        1,3: apply Cstep_else with (e := e) (c1 := c1) (c2 := c2).
        7,8: apply Cstep_if with (e := e) (c1 := c1) (c2 := c2).
        all: auto; unfold_cfgs; simpl in *; try rewrite project_merge_inv_trace; auto.
    - rewrite project_app_trace; simpl in *; subst.
      apply Cstep_while_t with (e := e) (c := c)
                                        (r := (project_reg r0 is_left))
                                        (m := (project_mem m0 is_left)); auto.
      now apply impe2_exp_sound with (is_left := is_left) in H0.
      now apply IHcstep2_1 with (c0 := c).
      (* XXX problem with inductive hypothesis *)
      apply IHcstep2_2 with (c0 := (Cwhile e c)); auto.
      admit.
    - apply Cstep_while_f with (e := e) (c := c); auto.
      now apply impe2_exp_sound with (is_left := is_left) in H0.
    - apply impe2_exp_sound with (is_left := is_left) in H0; simpl in *;
        apply project_merge_inv_reg in H4; apply project_merge_inv_mem in H5;
          destruct_conjs; apply l2_zero_or_one in H1; apply l2_zero_or_one in H8;
            unfold cleft in *; unfold cright in *.
      destruct is_left; [destruct H1; rewrite H1 in * | destruct H8; rewrite H8 in *];
        rewrite project_merge_inv_trace; subst; unfold_cfgs; simpl in *.
      1,2: inversion H2; subst; try discriminate.
      3,4: inversion H3; subst; try discriminate.
      1,3: apply Cstep_while_f with (e := e) (c := c); auto.
      all: apply Cstep_while_t with (e := e) (c := c) (r := r0) (m := m0); auto;
        unfold_cfgs; simpl in *;
          assert (c = hd) by congruence; rewrite H; auto;
            assert ([Cwhile e c] = tl) by congruence; subst;
              now apply -> cstep_seq_singleton in H10. 
  Admitted.

End Soundness.

Section Completeness.
  Lemma impe2_exp_complete : forall md d e r m v'i is_left,
      estep md d (e, project_reg r is_left, project_mem m is_left) v'i ->
      exists v', estep2 md d (e, r, m) v' /\ (project_value v' is_left = v'i).
  Proof.
    intros.
    remember (e, project_reg r is_left, project_mem m is_left) as ecfg.
    generalize dependent e.
    induction H; intros; rewrite Heqecfg in H; simpl in *.
    - exists (VSingle (Vnat n)); subst; split; auto; now constructor.
    - exists (VSingle (Vloc l)); subst; split; auto; now constructor.
    - exists (VSingle (Vlambda md c)); subst; split; auto; now constructor.
    - exists (r x); split; auto. rewrite H. apply Estep2_var with (x:=x); auto.
      rewrite Heqecfg in H0; simpl in *. rewrite <- H0.
      now apply project_comm_reg.
    - destruct IHestep1 with (e := e1). rewrite Heqecfg; auto.
      destruct IHestep2 with (e := e2). rewrite Heqecfg; auto.
      destruct_conjs.
      exists (apply_op op x x0); split; auto.
      apply Estep2_binop with (e1:=e1) (e2:=e2); auto.
      split. now apply project_nat_contains_nat in H5.
      now apply project_nat_contains_nat in H4.
      apply project_value_apply_op; auto.
    - assert (r0 = project_reg r is_left) by congruence.
      assert (m0 = project_mem m is_left) by congruence.
      destruct IHestep with (e0 := e). congruence.
      destruct_conjs.
      apply no_location_pairs in H6.
      exists (m l); split.
      apply Estep2_deref with (e := e) (r :=r) (m := m) (l := l); auto.
      congruence.
      rewrite <- H6; auto.
      rewrite <- project_comm_mem; rewrite <- H4; auto.
    Qed.
      
  Lemma impe2_complete : forall md d c r m r'1 m'1 t'1 r'2 m'2 t'2,
      (cstep md d (project_ccfg (c, r, m) true) (r'1, m'1) t'1) /\
      (cstep md d (project_ccfg (c, r, m) false) (r'2, m'2) t'2) ->
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
        | [ H : merge_mem _ _ _ |- _ ] => apply project_merge_inv_mem in H; destruct_conjs; auto
        | [ H : merge_reg _ _ _ |- _ ] => apply project_merge_inv_reg in H; destruct_conjs; auto
        | [ |- project_trace (merge_trace _) _ = _ ] => rewrite project_merge_inv_trace; auto
        | _ => idtac
        end.
    
    Local Ltac invert_cstep :=
      match goal with
      | [ H : cstep _ _ _ _ _ |- _ ] => inversion H; subst; try discriminate; simpl in *
      end.

    Local Ltac destruct_exp_complete :=
      repeat
        match goal with
        | [ H : estep _ _ _ _ |- _ ] => apply impe2_exp_complete in H; destruct H; destruct_conjs
        end.

    Local Ltac e2_determinism x1 x2 H :=
      assert (x1 = x2) by (apply estep2_deterministic with (v1 := x2) in H; auto); subst.

    intros.
    destruct H.
    remember (project_ccfg (c, r, m) true) as ccfg1.
    remember (r'1, m'1) as cterm1.
    generalize dependent r'1; generalize dependent m'1.
    generalize dependent r'2; generalize dependent m'2.
    generalize dependent c; generalize dependent r; generalize dependent m.
    revert t'2.
    induction H; intros; unfold project_ccfg in *; rewrite Heqccfg1 in *; simpl in *;
      invert_cstep; destruct_exp_complete.
    (* SKIP *)
    - do 3 eexists; repeat split; inversion Heqcterm1; subst; eauto.
      econstructor; auto.
      all: now cbn.
    (* ASSIGN *)
    - inversion H5; subst.
      e2_determinism x1 x2 H.
      do 3 eexists; repeat split; eauto.
      eapply Cstep2_assign with (x := x0) (e := e0) (v := x2); eauto.
      all: simpl; auto.
      1,3: rewrite project_update_comm_reg; simpl; unfold project_ccfg; simpl.
      all: congruence.
    (* DECLASSIFY *)
    - inversion H6; subst.
      e2_determinism x1 x2 H.
      do 3 eexists; repeat split; eauto.
      eapply Cstep2_declassify with (x := x0) (v := x2); eauto.
      all: simpl; auto.
      1,3: rewrite project_update_comm_reg; simpl; unfold project_ccfg; simpl.
      all: congruence.
    (* UPDATE *)
    - inversion H6; subst.
      e2_determinism x x1 H; e2_determinism x0 x2 H4.
      pose (no_location_pairs x1 l true H7).
      do 3 eexists; repeat split; eauto.
      eapply Cstep2_update; eauto.
      all: simpl; auto.
      rewrite <- e; unfold ccfg_to_ecfg2; auto.
      congruence.
      inversion Heqcterm1. apply project_update_comm_mem.
      rewrite e in H2; simpl in H2; inversion H2.
      apply project_update_comm_mem.
    (* OUTPUT *)
    - inversion H5; subst.
      e2_determinism x x0 H.
      do 3 eexists; repeat split; eauto.
      eapply Cstep2_output with (e := e0); eauto.
      all: simpl; auto; congruence.
    (* CALL *)
    - assert (e = e0) by congruence; rewrite H6 in *.
      e2_determinism x x0 H.
      destruct x0; subst.
      + simpl in *. assert (c = c1) by congruence; subst.
        edestruct IHcstep; unfold_cfgs; simpl; eauto. 
        do 2 destruct H4; destruct_conjs.
        exists x; exists x0; exists x1; repeat split.
        apply Cstep2_call with (e := e0) (c := c1); auto.
        unfold ccfg_to_ecfg2; simpl in *; subst; auto.
        all: congruence.
      + pose (merge_reg_exists r'1 r'2) as mr; destruct mr as [mr].
        pose (merge_mem_exists m'1 m'2) as mm; destruct mm as [mm].
        exists mr; exists mm; exists (merge_trace (tr, t'2)); repeat split.
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
      e2_determinism x x0 H.
      destruct x0; subst.
      + simpl in *; subst.
        destruct IHcstep with (c := c0) (m'1 := m') (r'1 := r') (m'2 := m'2) (r'2 := r'2)
                                        (t'2 := t'2) (m0 := m) (r0 := r); auto.
        do 3 destruct H4; destruct_conjs.
        exists x; exists x0; exists x1; repeat split; auto.
        apply Cstep2_if with (e := e0) (c1 := c0) (c2 := c3); auto.
        all: inversion Heqcterm1; subst; auto.
      + pose (merge_reg_exists r'1 r'2) as mr; destruct mr as [mr].
        pose (merge_mem_exists m'1 m'2) as mm; destruct mm as [mm].
        exists mr; exists mm; exists (merge_trace (tr, t'2)); repeat split.
        apply Cstep2_if_div with (e := e0) (c1 := c0) (c2 := c3) (n1 := 1) (n2 := 1)
                                           (r1 := r') (m1 := m') (r2 := r'2) (m2 := m'2); auto.
        unfold_cfgs; simpl in *; now subst.
        all: inversion Heqcterm1; subst; auto; destruct_merge_inv.
    (* IF TRUE, FALSE *)
    - inversion H5; subst.
      e2_determinism x x0 H.
      destruct x0; subst.
      + simpl in *; subst; discriminate.
      + pose (merge_reg_exists r'1 r'2) as mr; destruct mr as [mr].
        pose (merge_mem_exists m'1 m'2) as mm; destruct mm as [mm].
        exists mr; exists mm; exists (merge_trace (tr, t'2)); repeat split.
        apply Cstep2_if_div with (e := e0) (c1 := c0) (c2 := c3) (n1 := 1) (n2 := 0)
                                           (r1 := r') (m1 := m') (r2 := r'2) (m2 := m'2); auto.
        unfold_cfgs; simpl in *; now subst.
        all: inversion Heqcterm1; subst; auto; destruct_merge_inv.
    (* IF FALSE, TRUE *)
    - inversion H5; subst.
      e2_determinism x x0 H.
      destruct x0; subst.
      + simpl in *; subst; discriminate.
      + pose (merge_reg_exists r'1 r'2) as mr; destruct mr as [mr].
        pose (merge_mem_exists m'1 m'2) as mm; destruct mm as [mm].
        exists mr; exists mm; exists (merge_trace (tr, t'2)); repeat split.
        apply Cstep2_if_div with (e := e0) (c1 := c0) (c2 := c3) (n1 := 0) (n2 := 1)
                                           (r1 := r') (m1 := m') (r2 := r'2) (m2 := m'2); auto.
        unfold_cfgs; simpl in *; now subst.
        all: inversion Heqcterm1; subst; auto; destruct_merge_inv.    
    - inversion H5; subst.
      e2_determinism x x0 H.
      destruct x0; subst.
      + simpl in *; subst.
        destruct IHcstep with (c := c3) (m'1 := m') (r'1 := r') (m'2 := m'2) (r'2 := r'2)
                                        (t'2 := t'2) (m0 := m) (r0 := r); auto.
        do 3 destruct H4; destruct_conjs.
        exists x; exists x0; exists x1; repeat split; auto.
        apply Cstep2_else with (e := e0) (c1 := c0) (c2 := c3); auto.
        all: inversion Heqcterm1; subst; auto.
      + pose (merge_reg_exists r'1 r'2) as mr; destruct mr as [mr].
        pose (merge_mem_exists m'1 m'2) as mm; destruct mm as [mm].
        exists mr; exists mm; exists (merge_trace (tr, t'2)); repeat split.
        apply Cstep2_if_div with (e := e0) (c1 := c0) (c2 := c3) (n1 := 0) (n2 := 0)
                                           (r1 := r') (m1 := m') (r2 := r'2) (m2 := m'2); auto.
        unfold_cfgs; simpl in *; now subst.
        all: inversion Heqcterm1; subst; auto; destruct_merge_inv.
    (* WHILE BOTH TRUE *)
    - inversion H6; subst.
      e2_determinism x x0 H.
      destruct x0; subst.
      + admit.
      + pose (merge_reg_exists r'1 r'2) as mr; destruct mr as [mr].
        pose (merge_mem_exists m'1 m'2) as mm; destruct mm as [mm].
        exists mr; exists mm; exists (merge_trace (tr ++ tr', tr0 ++ tr'0)); repeat split.
        eapply Cstep2_while_div; eauto.
        all: unfold_cfgs; simpl in *; inversion Heqcterm1; subst; auto.
        1,2: eapply Cstep_seq_hd; simpl; eauto; apply cstep_seq_singleton; auto.
        all: destruct_merge_inv.
    (* WHILE TRUE, FALSE *)
    - inversion H9; subst.
      e2_determinism x x0 H.
      destruct x0; subst.
      + simpl in *; subst; discriminate.
      + admit.
    (* WHILE FALSE, TRUE *)
    - inversion H4; subst.
      e2_determinism x x0 H.
      destruct x0; subst.
      + simpl in *; subst; discriminate.
      + admit.
    (* WHILE BOTH FALSE *)
    - admit.
  Admitted.
  
End Completeness.