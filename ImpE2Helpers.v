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
  Axiom No_Pointers2 : forall (m: mem2) l,
    (forall l', m l <> VSingle (Vloc l')) /\
    (forall l' l'', m l <> VPair (Vloc l') (Vloc l'')).

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

  Lemma no_location_pairs : forall v l is_left,
      project_value v is_left = Vloc l ->
      v = VSingle (Vloc l).
  Proof.
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

Section Security.
  (* We somehow need to know that if c performs an assignment or update of x, then *)
  (* the type of x in the env is at a higher security level than pc' *)
  (* Otherwise, the reg/mem and context does not change *)
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
   
  Lemma assignment_more_secure : forall pc md d c G G' x bt q r m r' m' tr,
      com_type pc md G d c G' ->
      cstep md d (c,r,m) (r',m') tr ->
      assign_in x tr ->
      G' x = Some (Typ bt q) ->
      sec_level_le pc q.
  Proof.
  Admitted.
  
  Lemma assign_in_while_protected :
    com_type pc md G d (Cwhile e c) G ->
    com_type pc' md G d c G ->
    protected pc' ->
    cstep md d (Cwhile e c, r, m) (r',m') tr ->
    assign_in x tr ->
    G x = Some (Typ bt p) ->
    protected p.
    
  Lemma no_assign_reg_context_constant : forall md d c r m r' m' tr x pc G G',
      cstep2 md d (c, r, m) (r', m') tr ->
      com_type pc md G d c G' ->
      ~assign_in x (project_trace tr true) /\
      ~assign_in x (project_trace tr false) ->
      r x = r' x /\ G x = G' x.
  Proof.
  Admitted.
  Lemma assign_in_app : forall tr tr' x,
      assign_in x (tr ++ tr') <-> assign_in x tr \/ assign_in x tr'.
  Proof.
    unfold assign_in. split; intros. destruct H as [v [r H]]. apply in_app_or in H.
    destruct H; [left | right]; exists v; exists r; auto.
    destruct H; destruct H as [v [r H]]; exists v; exists r; apply in_or_app;
      [now left | now right].
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
   
  Lemma update_more_secure : forall pc md d c G G' x bt q rt r m r' m' tr,
      com_type pc md G d c G' ->
      cstep md d (c,r,m) (r',m') tr ->
      update_in x tr ->
      Loc_Contxt x = Some (Typ bt q, rt) ->
      sec_level_le pc q.
  Proof.
  Admitted.
  Lemma no_update_mem_constant : forall md d c r m r' m' tr x pc G G',
      cstep2 md d (c, r, m) (r', m') tr ->
      com_type pc md G d c G' ->
      ~update_in x (project_trace tr true) /\ ~update_in x (project_trace tr false) ->
      m x = m' x.
  Proof.
  Admitted.
  Lemma update_in_app : forall tr tr' x,
      update_in x (tr ++ tr') <-> update_in x tr \/ update_in x tr'.
  Proof.
    unfold assign_in. split; intros. destruct H as [v [r H]]. apply in_app_or in H.
    destruct H; [left | right]; exists v; exists r; auto.
    destruct H; destruct H as [v [r H]]; exists v; exists r; apply in_or_app;
      [now left | now right].
  Qed.

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
       pose (No_Pointers2 m l0); destruct_pairs.
       pose (H6 l). intuition. apply n in H4. omega.
    -- inversion H0; try discriminate; subst.
       inversion H3.
  Qed.
  
  Lemma same_mem_locs_evals_same_value : forall e r m md d G typ vfin,
      exp_type md G d e typ ->
      estep2 md d (e,r,m) vfin ->
      is_escape_hatch e ->      (forall l, loc_in_exp e l -> exists v, m l = VSingle v) ->
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
      
      pose (IHe1 H5 H6 H7 _ H2 _ H12) as He1; destruct He1 as [x He1].
      pose (IHe2 H10 H9 H8 _ H3 _ H13) as He2; destruct He2 as [y He2].
      unfold contains_nat in *.
      destruct H4 as [[n0 H41']|[n0 [n1 blah]]]; destruct H11 as [[n4 H11']|[n2 [n3 blah']]];
        subst; try discriminate.
      exists (Vnat (op n0 n4)). now unfold apply_op.
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

  Lemma tobs_sec_level_app (sl: sec_level) (l l': trace) :
    tobs_sec_level sl l ++ tobs_sec_level sl l' = tobs_sec_level sl (l ++ l').
  Proof.
    unfold tobs_sec_level. now rewrite (filter_app _ l l').
  Qed.

  (* If there has been an update to l from minit to m0, we can assume the updated values were *)
  (* protected because the update values must have derived from the initial memory locations *)
  (* which were different and thus protected *)
  (* Else there has not been an update, and the initial memory location l was protected in minit *)
  Lemma sl_ind_iff_mem_pairs_protected : forall (m: mem2) l md d r e G v1 v2 bt p,
      mem_sl_ind L ->
      estep2 md d (e,r,m) (VSingle (Vloc l)) ->
      exp_type md G d (Ederef e) (Typ bt p) ->
      m l = VPair v1 v2 <-> protected p.
  Admitted.

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
       pose (apply_op_pair op v1 v2) as Hop_pair.
       destruct Hop_pair as [Hop1 Hop2].
       assert (contains_nat v1 /\ contains_nat v2 /\
               (exists v3 v4 : val, apply_op op v1 v2 = VPair v3 v4)).
       split; auto. split; auto. exists v3. exists v0.  auto.
       apply Hop1 in H. destruct H. destruct H. destruct_pairs.
       exists x. exists x0. auto.
       inversion H4; subst; try discriminate.
       destruct H. destruct H; destruct H.
       -- assert (protected p0).
          eapply (IHHestep2_1 Hestep2_1). unfold cterm2_ok; auto.
          apply H. apply H14. auto.
          now apply (join_protected_l p0 q).
       -- assert (protected q ).
          eapply (IHHestep2_2 Hestep2_2). unfold cterm2_ok; auto.
          apply H. apply H18. auto.
          now apply (join_protected_r p0 q).
     - inversion Heqecfg; subst.
       inversion H5; subst.
       eapply sl_ind_iff_mem_pairs_protected; eauto.
  Qed.
  
End Security.

     