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

Section Misc.
  Lemma l2_zero_or_one (n : nat) : n < 2 -> n = 0 \/ n = 1.
  Proof. omega. Qed.

  Lemma filter_app (f:event -> bool) l1 l2:
    filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
  Proof.
    induction l1; simpl; auto. rewrite IHl1. destruct (f a); auto.
  Qed.
End Misc.

Section Project_Merge.
  (* XXX: these assumptions are gross, but the semantics become a mess if we
     dont' have them... *)

  Lemma no_location_pairs : forall md d e r m v l is_left,
    estep2 md d (e, r, m) v ->
    project_value v is_left = Vloc l ->
    v = VSingle (Vloc l).
  Proof.
    intros.
    induction H.
    1,3: discriminate. 
    - simpl in H0; inversion H0; now subst.
    - (* XXX need a hypothesis about registers not having pairs? *)
      admit.
    - destruct_conjs. unfold contains_nat in *.
      do 2 destruct H3; do 2 destruct H4; simpl; subst.
      + discriminate.
      + destruct H4; subst; destruct is_left; simpl in *; discriminate.
      + destruct H3; subst; destruct is_left; simpl in *; discriminate.
      + destruct H3; destruct H4; destruct is_left; subst; simpl in *; discriminate.
    - pose (No_Pointers2 m0 l0); destruct a.
      rewrite <- H2. specialize (H4 l).
      (* XXX: need value decidability *)
      admit.
  Admitted.
      
  Lemma project_comm_reg : forall r b x,
      (project_reg r b) x = project_value (r x) b.
  Proof.
    intros; unfold project_reg; destruct (r x); auto.
  Qed.

  Lemma project_comm_mem : forall m b x,
      (project_mem m b) x = project_value (m x) b.
  Proof.
    intros; unfold project_mem; destruct (m x); auto.
  Qed.

  (* XXX: this might be a pain to prove with registers as functions. Used below in soundness. *)
  Lemma project_update_comm_reg : forall ccfg x v is_left,
      project_reg (ccfg_update_reg2 ccfg x v) is_left = 
      ccfg_update_reg (project_ccfg ccfg is_left) x (project_value v is_left).
  Proof.
    intros.
    extensionality z.
    unfold project_reg; unfold ccfg_update_reg; unfold ccfg_update_reg2.
    destruct (z =? x).
    - unfold project_value; auto.
    - simpl; now unfold project_reg.
  Qed.

  Lemma project_update_comm_mem : forall ccfg l v is_left,
      project_mem (ccfg_update_mem2 ccfg l v) is_left = 
      ccfg_update_mem (project_ccfg ccfg is_left) l (project_value v is_left).
  Proof.
    intros.
    extensionality z.
    unfold_cfgs; unfold ccfg_update_mem2; unfold project_mem.
    destruct (z =? l).
    - unfold project_value; auto.
    - simpl; now unfold project_mem.
  Qed.

  (* XXX: these lemmata are necessary because merge_reg and merge_mem are propositional *)
  Lemma merge_reg_exists : forall r1 r2,
      exists r, merge_reg r1 r2 r.
  Proof.
  Admitted.

  Lemma merge_mem_exists : forall m1 m2,
      exists m, merge_mem m1 m2 m.
  Proof.
  Admitted.
  
  Lemma project_merge_inv_reg : forall r1 r2 r,
      merge_reg r1 r2 r -> (project_reg r true = r1) /\ (project_reg r false = r2).
  Proof.
  Admitted.

  Lemma project_merge_inv_mem : forall m1 m2 m,
      merge_mem m1 m2 m <-> (project_mem m true = m1) /\ (project_mem m false = m2).
  Proof.
  Admitted.

  Lemma project_merge_inv_trace : forall t1 t2 is_left,
      project_trace (merge_trace (t1, t2)) is_left = (if is_left then t1 else t2).
  Proof.
  Admitted.

  Lemma project_app_trace : forall t1 t2 is_left,
      project_trace (t1 ++ t2) is_left =
      (project_trace t1 is_left) ++ (project_trace t2 is_left).
  Proof.
    intros.
    induction t1.
    - rewrite app_nil_l; now cbn.
    - cbn; rewrite IHt1; now destruct (event2_to_event a is_left).
  Qed.

  Lemma contains_nat_project_nat : forall v is_left,
      contains_nat v -> exists n, project_value v is_left = Vnat n.
  Proof.
    intros.
    destruct v.
    - unfold contains_nat in H; destruct H.
      + destruct H; exists x; simpl; congruence.
      + destruct H; destruct H; discriminate.
    - unfold contains_nat in H; destruct H.
      + destruct H; discriminate.
      + destruct H; destruct H.
        destruct is_left; [exists x | exists x0]; simpl; congruence.
  Qed.

  Lemma project_value_apply_op : forall op v1 v2 n1 n2 is_left,
      project_value v1 is_left = Vnat n1 ->
      project_value v2 is_left = Vnat n2 ->
      (project_value (apply_op op v1 v2) is_left) = Vnat (op n1 n2).
  Proof.
  Admitted.

End Project_Merge.

Section Semantics.
  (* XXX: thought I needed this for exp_output_wf, didn't use it. Might still be useful...? *)
  Lemma estep2_deterministic : forall md d e r m v1 v2,
      estep2 md d (e, r, m) v1 ->
      estep2 md d (e, r, m) v2 ->
      v1 = v2.
  Proof.
    intros; revert H0; revert v2.
    induction H; intros; destruct ecfg as [[e' r'] m']; simpl in *; try rewrite H in H0.
    1-3: inversion H0; subst; try discriminate; simpl in H1; congruence.
    inversion H1; subst; try discriminate; simpl in *; congruence.
    - rewrite H in H3; inversion H3; try discriminate; simpl in *;
        assert (e1 = e0) by congruence; assert (e2 = e3) by congruence;
          subst; apply IHestep2_1 in H5; apply IHestep2_2 in H6; congruence.
   - rewrite H in H3; inversion H3; subst; try discriminate; simpl in *.
      assert (e0 = e1) by congruence.
      assert (r0 = r1) by congruence.
      assert (m0 = m1) by congruence.
      subst. apply IHestep2 in H5. assert (l = l0) by congruence; now subst.
  Qed.  
 
  (* Executing a singleton sequence is the same as executing the command *)
  Lemma cstep_seq_singleton : forall md d c r m r' m' t,
      cstep md d (Cseq [c], r, m) (r', m') t <->
      cstep md d (c, r, m) (r', m') t.
    split; intros.
    - inversion H; subst; try discriminate; unfold_cfgs.
      simpl in H3.
      simpl in H2; assert (tl = []) by congruence.
      rewrite H0 in H7. inversion H7; subst; try discriminate.
      rewrite app_nil_r; congruence.
    - eapply Cstep_seq_hd; simpl; eauto.
      try econstructor; now simpl.
      now rewrite app_nil_r.
  Qed.
  
  Lemma apply_op_pair (op : nat -> nat -> nat) (v1 v2: val2) :
    contains_nat v1 /\ contains_nat v2 /\
    (exists v3 v4, apply_op op v1 v2 = VPair v3 v4) <->
    exists v' v'', contains_nat v1 /\ contains_nat v2 /\
                   (v1 = VPair v' v'' \/ v2 = VPair v' v'').
  Proof.
    intros.
    split; intros; destruct_pairs.
    induction v1, v2; unfold apply_op in *; destruct H1; destruct H1.
    destruct v, v0; try discriminate.
    - destruct v, v0; try discriminate.
      destruct v1; try discriminate.
      exists (Vnat n0). exists (Vnat n1).
      split; auto. 
    - destruct v, v0; try discriminate.
      1-4: unfold contains_nat in H; destruct H; destruct H;
        [discriminate | destruct H; inversion H].
      2-5: unfold contains_nat in H; destruct H; destruct H;
        [discriminate | destruct H; inversion H].
      exists (Vnat n). exists (Vnat n0). split; auto.
    - destruct v, v0; try discriminate.
      1-4: unfold contains_nat in H; destruct H; destruct H;
        [discriminate | destruct H; inversion H].
      2-5: unfold contains_nat in H; destruct H; destruct H;
        [discriminate | destruct H; inversion H].
      exists (Vnat n). exists (Vnat n0). split; auto.
    - destruct H. destruct H. destruct H; destruct_pairs.
      split; [ | split]; auto.
      destruct H1.
      -- rewrite H1. destruct v2; destruct v.
         destruct H0; destruct H0; [discriminate | destruct H0; inversion H0].
         2-5: destruct H0; destruct H0; [discriminate | destruct H0; inversion H0].
         --- unfold apply_op.
             destruct x; auto. exists (Vlambda m c). exists x0; auto.
             destruct x0; auto.
             exists (Vnat n0). exists (Vlambda m c); auto.
             exists (Vnat (op n n0)); exists (Vnat (op n n1)); auto.
             exists (Vnat n0); exists (Vloc l); auto.
             exists (Vloc l); exists x0; auto.
         --- unfold apply_op.
             destruct x; auto. exists (Vlambda m c). exists x0; auto.
             destruct x0; auto.
             exists (Vnat n0); exists (Vlambda m c); auto.
             exists (Vnat (op n0 x1)). exists (Vnat (op n1 x2)); auto.
             exists (Vnat n0). exists (Vloc l). auto.
             exists (Vloc l). exists x0. auto.
      -- rewrite H1 in *. destruct v1; destruct v.
         destruct H; destruct H; [discriminate | destruct H; inversion H].
         2-5: destruct H; destruct H; [discriminate | destruct H; inversion H].
         unfold apply_op.
         destruct x. destruct H0; destruct H0; [discriminate | destruct H0; inversion H0].
          destruct x0. destruct H0; destruct H0; [discriminate | destruct H0; inversion H0].
          exists (Vnat (op n n0)). exists (Vnat (op n n1)). auto.
          destruct H0; destruct H0; [discriminate | destruct H0; inversion H0].
          destruct H0; destruct H0; [discriminate | destruct H0; inversion H0].
          unfold apply_op.
          destruct x; auto. exists (Vnat x1). exists (Vnat x2). auto.
          destruct x0; auto. exists (Vnat x1). exists (Vnat x2); auto.
          exists (Vnat (op x1 n0)). exists (Vnat (op x2 n1)); auto.
          1-2: exists (Vnat x1); exists (Vnat x2); auto.
  Qed.

End Semantics.


     