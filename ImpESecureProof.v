(* FIXME: Copied these from pset4; probably won't need all of them. *)

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
Import ListNotations.
Require Import Common.
Require Import ImpE.
Require Import ImpE2.

(*******************************************************************************
*
* SECURITY
*
*******************************************************************************)

Section Security.
  Definition esc_hatch : Type := exp.
  Definition is_esc_hatch (e: esc_hatch) (G: context) := exp_novars e /\ all_loc_immutable e G.
  
  Definition tobs_sec_level (sl: sec_level) : trace -> trace :=
    filter (fun event => match event with
                         | Out sl' v => sec_level_le_compute sl' sl
                         | AEnc c c' enc_equiv => true
                         | ANonEnc c => true
                         | _ => false                           
                         end).
   
  (* XXX I think it might be easier to use definitions instead of inductive
     types (don't get the error about not being able to find an instance
     for all the quantified variables *)
  Definition knowledge_attack (c: com) (sl: sec_level) (cstep: csemantics)
             (tobs: trace) (m: mem) : Prop :=
    forall d r' m' k' t,
      cstep Normal d (c, reg_init, m, []) (r', m', k') t ->
      tobs_sec_level sl tobs = tobs_sec_level sl t.

  (* XXX need to enforce that all U are unset? *)
  Definition knowledge_ind (m: mem) (g: sec_spec) (U: set condition)
             (sl: sec_level) (m': mem) : Prop :=
    forall l, sec_level_le (cur (g l) U) sl -> m l = m' l.

  Definition knowledge_esc (m0 m: mem) (estep: esemantics) (e: esc_hatch)
             (m': mem) : Prop :=
    exists md, forall d v,
        estep md d (e, reg_init, m0, []) v /\
        estep md d (e, reg_init, m, []) v ->
        estep md d (e, reg_init, m', []) v.

  Definition cnd_unset (m: mem) (cnd: condition) : Prop := m (Cnd cnd) = Vnat 0.
  Definition cnd_set (m: mem) (cnd: condition) : Prop := m (Cnd cnd) = Vnat 1.
                
  (* XXX This thing with e and csemantics is a little weird. Probably want to
     define one that encapsulates both, but I'm not sure how...
   *)
  Definition secure_prog (sl: sec_level) (g: sec_spec)
             (cstep: csemantics) (estep: esemantics) (c: com) : Prop :=
    forall m0 r m k d tobs mknown,
      cstep Normal d (c, reg_init, m0, []) (r, m, k) tobs ->
      (exists m'' t'', tobs = Mem m'' :: t'') ->
      (forall mind U,
          In (Mem mind) tobs ->
          (forall cnd, cnd_unset mind cnd <-> In cnd U) ->
          knowledge_ind m0 g U sl mknown) ->
      (forall mdecl e,
          In (Decl e mdecl) tobs ->
          knowledge_esc m0 mdecl estep e mknown) ->
      knowledge_attack c sl cstep tobs mknown.
End Security.

Section Preservation.
  (* Conditions set and unset at the beginning of execution *)
  Parameter SC : set condition.
  Parameter UC : set condition.
  Parameter g: sec_spec.
  Definition cnd_in_S (l: location) (m0 : mem2) : Prop :=
    is_Cnd l /\ m0 l = VSingle (Vnat 1).
  Ltac unfold_cfgs :=
    unfold ccfg_update_reg2 in *;
    unfold ccfg_to_ecfg2 in *;
    unfold ccfg_reg2 in *;
    unfold ccfg_mem2 in *;
    unfold ccfg_kill2 in *;
    unfold ccfg_com2 in *;
    unfold ecfg_exp2 in *;
    unfold ecfg_reg2 in *;
    unfold ecfg_update_exp2 in *.                   

  Definition cterm2_ok (G: context) (d: loc_mode) (m0: mem2)
             (r: reg2) (m: mem2) (K: kill2) : Prop :=
      (forall x v1 v2 bt p,
          (r x = VPair v1 v2 /\ (var_context G) x = Some (Typ bt p)) -> protected p SC) 
      /\ (forall l v1 v2 bt p rt,
          (m (Not_cnd l) = VPair v1 v2 /\ (loc_context G) (Not_cnd l) = Some (Typ bt p, rt))
          -> protected p SC)
      /\ (forall e v md', is_esc_hatch e G ->
                          (estep2 md' d (e, reg_init2, m0, K) v ->
                           estep2 md' d (e, r, m, K) v))
      /\ project_kill K true = project_kill K false
      /\ knowledge_ind (project_mem m0 true) g UC L (project_mem m0 false).

  Definition cconfig2_ok (pc: sec_policy) (md: mode) (G: context) (d: loc_mode)
             (m0: mem2) (ccfg2: cconfig2) (G': context) (K': kill2) : Prop :=
    (forall i, set_In i UC -> (ccfg_mem2 ccfg2) (Cnd i) = VSingle (Vnat 0))
    /\  com_type pc md G (project_kill (ccfg_kill2 ccfg2) true) UC d
                 (ccfg_com2 ccfg2) G' (project_kill K' true)
    /\ (forall x v1 v2 bt p,
           ((ccfg_reg2 ccfg2) x = VPair v1 v2
            /\ (var_context G) x = Some (Typ bt p))
           -> protected p SC)
    /\ (forall l v1 v2 bt p rt,
           ((ccfg_mem2 ccfg2) (Not_cnd l) = VPair v1 v2
            /\ (loc_context G) (Not_cnd l) = Some (Typ bt p, rt))    
           -> protected p SC)
    /\ (forall e v md', is_esc_hatch e G ->
                        (estep2 md' d  (e, reg_init2, m0, ccfg_kill2 ccfg2) v ->
                         estep2 md' d (e, ccfg_reg2 ccfg2, ccfg_mem2 ccfg2, ccfg_kill2 ccfg2) v))
    /\ project_kill (ccfg_kill2 ccfg2) true = project_kill (ccfg_kill2 ccfg2) false
    /\ knowledge_ind (project_mem m0 true) g UC L (project_mem m0 false).

  Lemma esc_hatch_reg_irrelevance (e : esc_hatch) :
    forall G md d r m k v r',
    is_esc_hatch e G -> estep2 md d (e, r, m, k) v ->
    estep2 md d (e, r', m, k) v.
  Proof.
    intros. unfold is_esc_hatch in *.
    remember (e, r, m, k) as ecfg2.
    generalize dependent e.
    induction H0; intros; subst; auto.
    1-3: constructor; unfold_cfgs; auto.
    - unfold_cfgs. subst. unfold exp_novars in H1. simpl in H1. omega.
    - unfold_cfgs; subst; destruct_pairs.
      assert (exp_novars e1 /\ all_loc_immutable e1 G).
      split. unfold exp_novars in *. destruct_pairs; inversion H; destruct_pairs; auto.
      unfold all_loc_immutable in *; destruct_pairs; inversion H0; destruct_pairs; auto.
      assert (exp_novars e2 /\ all_loc_immutable e2 G).
      split. unfold exp_novars in *. destruct_pairs; inversion H; destruct_pairs; auto.
      unfold all_loc_immutable in *; destruct_pairs; inversion H0; destruct_pairs; auto.
      pose (IHestep2_1 e1 H1); pose (IHestep2_2 e2 H2).
      apply (Estep2_binop md d (Ebinop e1 e2 op,r',m,k) e1 e2 n1 n2); unfold_cfgs; auto.
    - inversion Heqecfg2; subst; destruct_pairs.
      assert (exp_novars e). unfold exp_novars in *; destruct_pairs; inversion H; auto.
      apply (Estep2_deref md d (Ederef e,r',m,k) e r' m k l (m l)); unfold_cfgs; auto.
      apply (IHestep2 e); split; auto.
      unfold all_loc_immutable in *; inversion H1; auto.
    - unfold_cfgs; subst.
      destruct_pairs. unfold all_loc_immutable in H2. simpl in H2. omega.
  Qed.

  (*Lemma esc_hatch_nopairs_equivalent (e : esc_hatch) : *)

  Lemma econfig2_locs_protected (e: exp) (m0: mem2):
    forall G d r m k v v1 v2 bt bt' p p' q md md' rt e',
      knowledge_ind (project_mem m0 true) g UC L (project_mem m0 false) ->
      v = VPair v1 v2 ->
      exp_type md G d e (Typ bt p) ->
      estep2 md d (e,r,m,k) v ->
      e = Ederef e' ->
      exp_type md G d e' (Typ (Tref (Typ bt' p') md' rt) q) ->
      protected q SC.
  Proof.
  Admitted.

  Lemma econfig2_pair_protected : forall md G d e p r m k v v1 v2 bt m0,
      v = VPair v1 v2 ->
      exp_type md G d e (Typ bt p) ->
      estep2 md d (e,r,m,k) v ->
      (* XXX assume that if the value is a location, then the policy on the location *)
      (* is protected by S. This should be fine because we're assuming this for *)
      (* memories that are indistinguishable *)
      (forall bt' (p' q: sec_policy) md' rt e',
          e = Ederef e' ->
          exp_type md G d e' (Typ (Tref (Typ bt' p') md' rt) q)
          -> protected q SC) ->
      cterm2_ok G d m0 r m k ->
      protected p SC.
  Proof.
    intros.
    remember (e,r,m,k) as ecfg.
    generalize dependent e.
    induction H1; intros; subst; try discriminate; unfold_cfgs;
    unfold cterm2_ok in H3; destruct_pairs; subst.
    - inversion H2; subst.
      apply (H x v1 v2 bt p); split; auto. 
    - inversion Heqecfg; subst.
      inversion H5; subst.
      assert (protected q SC). apply (H6 bt p0 q md' rt e); auto.
      apply (join_protected_r SC p0 q); auto.
    - destruct H2; destruct_pairs; try discriminate.
  Qed.

  Lemma impe2_final_config_preservation (G: context) (d: loc_mode) (m0: mem2) :
      forall G' K' c r m k pc md r' m' t,
        (forall l e v, loc_in_exp e G l -> m0 l = VSingle v) -> 
        context_wt G d ->
        cconfig2_ok pc md G d m0 (c,r,m,k) G' K' ->
        cstep2 md d (c,r,m,k) (r', m', K') t ->
        cterm2_ok G' d m0 r' m' K'.
  Proof.
    intros G' K' c r m k pc md r' m' t Hlocs Hcwt Hcfgok Hcstep.
    remember (c,r,m,k) as ccfg2; subst.
    unfold cconfig2_ok in Hcfgok; destruct_pairs.
    induction c; unfold cterm2_ok; intros; subst; simpl in *; unfold_cfgs.
    (* CSkip *)
    - inversion Hcstep; try discriminate; subst.
        inversion H0; try discriminate; subst.
      split; [intros | split; intros]; simpl in *; auto.
      -- now apply H1 in H7.
      -- now apply H2 in H7.
(*    (* CAssign *)
    - inversion H3; try discriminate; subst;
        inversion H4; try discriminate; subst.
      split; [intros | split; intros]; simpl in *; auto; unfold_cfgs.
      -- inversion H12; subst.
         destruct (Nat.eq_dec x0 x).
         --- rewrite <- (Nat.eqb_eq x0 x) in e; rewrite e in H9.
             destruct_pairs.
             assert (protected p S).
             apply (econfig2_pair_protected
                      md (Cntxt vc lc) d e0 p r m' K' v0 v1 v2 S s H m0
                      H9 H11 H16).
             (* XXX ergh now we either have to pass in the assumption or *)
             (* do something weird *)
             ---- admit.
             ---- unfold cterm2_ok; split; intros. now apply H5 in H13.
             ----- split; intros. now apply H6 in H13.
             ------ split; intros; auto.
             ---- inversion H10; subst. now apply (join_protected_l S p pc).
         --- rewrite <- (Nat.eqb_neq x0 x) in n. rewrite n in H9.
             apply H5 in H9; auto.
      -- now apply H6 in H9.
      -- split; intros; auto.
         apply (esc_hatch_reg_irrelevance
                  e1 md' d r m' K' v1
                  (fun var : var => if var =? x then v0 else r var)); auto.
    (* Cdeclassify *)
    - inversion H3; try discriminate; subst;
        inversion H4; try discriminate; subst.
      split; [intros | split; intros]; simpl in *; auto; unfold_cfgs.
      inversion_clear H12; subst.
      
      destruct (Nat.eq_dec x0 x).
      --- rewrite <- (Nat.eqb_eq x0 x) in e; rewrite e in *.
          
          inversion H11; try discriminate; subst.
*)
  Admitted.
         
  Lemma impe2_type_preservation
        (G: context) (d: loc_mode) (S: set condition) (H: set esc_hatch) (m0: mem2) :
    forall pc md (U: set condition) c r m K G' K',
      context_wt G d ->
      cconfig2_ok pc md G d m0 (c, r, m, K) G' K' ->
      forall mdmid cmid rmid mmid rmid' mmid' kmid' tmid rfin mfin kfin tfin,
        imm_premise
          (cstep2 mdmid d (cmid, rmid, mmid, K') (rmid', mmid', kmid') tmid)
          (cstep2 md d (c, r, m, K) (rfin, mfin, kfin) tfin) ->
        (exists pcmid Gmid Gmid' Umid,
          policy_le pc pcmid ->
          Umid = [] \/ (forall i, In i U -> In i Umid) ->
          cconfig2_ok pcmid mdmid Gmid d m0 (cmid, rmid, mmid, K') Gmid' K').
  Proof.
  Admitted.
 
End Preservation.


(*******************************************************************************
*
* ADEQUACY
*
*******************************************************************************)
Section Adequacy.

  Definition not_pair_val (v : val2) : Prop :=
    match v with
    | VPair _ _ => False
    | _ => True
    end.

  (* XXX: thought I needed this for exp_output_wf, didn't use it. Might still be useful...? *)
  Lemma estep2_deterministic : forall md d e r m k v1 v2,
    estep2 md d (e, r, m, k) v1 ->
    estep2 md d (e, r, m, k) v2 ->
    v1 = v2.
  Proof.
    intros; revert H0; revert v2.
    induction H; intros; destruct ecfg as [[[e' r'] m'] k']; simpl in *; try rewrite H in H0.
    1-3: inversion H0; subst; try discriminate; simpl in H1; congruence.
    inversion H1; subst; try discriminate; simpl in *; congruence.
    - rewrite H in H2; inversion H2; try discriminate; simpl in *;
        assert (e1 = e0) by congruence; assert (e2 = e3) by congruence;
          subst; apply IHestep2_1 in H4; apply IHestep2_2 in H5; congruence.
    - rewrite H in H3; inversion H3; subst; try discriminate; simpl in *.
      assert (e0 = e1) by congruence.
      assert (r0 = r1) by congruence.
      assert (m0 = m1) by congruence.
      assert (k0 = k1) by congruence.
      subst. apply IHestep2 in H5. assert (l = l0) by congruence; now subst.
    - rewrite H in H2; inversion H2; subst; try discriminate; simpl in *.
      assert (cnd = cnd0) by congruence; subst.
      apply IHestep2 in H4.
      destruct H1; destruct H5; destruct_conjs; subst; auto; congruence.
  Qed.      

  Lemma project_comm_reg : forall r b x,
      (project_reg r b) x = project_value (r x) b.
  Proof.
    intros; unfold project_reg; destruct (r x); auto.
  Qed.

  (* XXX: this might be a pain to prove with registers as functions. Used below in soundness. *)
  Lemma project_update_comm_reg : forall ccfg x v is_left,
      project_reg (ccfg_update_reg2 ccfg x v) is_left = 
      ccfg_update_reg (project_ccfg ccfg is_left) x (project_value v is_left).
  Proof.
  Admitted.

  Lemma project_update_comm_mem : forall ccfg l v is_left,
      project_mem (ccfg_update_mem2 ccfg l v) is_left = 
      ccfg_update_mem (project_ccfg ccfg is_left) l (project_value v is_left).
  Proof.
  Admitted.

  Lemma project_add_comm_kill : forall K is_left enc,
      project_kill (add_to_kill2 enc K) is_left =
      set_add Nat.eq_dec enc (project_kill K is_left).
  Proof.
  Admitted.

  Lemma project_merge_inv_reg : forall r1 r2 r,
      merge_reg r1 r2 r -> (project_reg r true = r1) /\ (project_reg r false = r2).
  Proof.
  Admitted.

  Lemma project_merge_inv_mem : forall m1 m2 m,
      merge_mem m1 m2 m -> (project_mem m true = m1) /\ (project_mem m false = m2).
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
  Admitted.

  Lemma impe2_exp_sound : forall md d e r m K v is_left,
      estep2 md d (e, r, m, K) v ->
      estep md d (e, project_reg r is_left, project_mem m is_left, project_kill K is_left)
            (project_value v is_left).
  Proof.
    intros.
    remember (e, r, m, K) as ecfg.
    generalize dependent e.
    induction H; intros; try rewrite Heqecfg in H; simpl in *; try rewrite H.
    1-3: constructor; simpl; auto.
    - apply Estep_var with (x:=x); auto; subst; apply project_comm_reg.
    - apply Estep_binop with (e1:=e1) (e2:=e2); simpl; auto; 
        [apply (IHestep2_1 e1) | apply (IHestep2_2 e2)];
        rewrite Heqecfg; unfold ecfg_update_exp2; auto.
    - inversion H; subst.
      apply Estep_deref with (e:=e) (l:=l) (m:=project_mem m0 is_left)
                                    (r:=project_reg r0 is_left)
                                    (k:=project_kill k is_left); simpl; auto.
      now apply mode_access_ok_project_ok.
    - apply Estep_isunset with (cnd := cnd) (v := (project_value v is_left)); simpl; auto.
      apply IHestep2; subst; auto.
      destruct H1; destruct_conjs; [left | right];
        simpl; split; try (now rewrite H1); try (now rewrite H2).
  Qed.
       
  Lemma impe2_sound : forall md d c r m K r' m' K' t is_left,
    cstep2 md d (c, r, m, K) (r', m', K') t ->
    cstep md d (project_ccfg (c, r, m, K) is_left)
          (project_reg r' is_left, project_mem m' is_left, project_kill K' is_left)
          (project_trace t is_left).
  Proof.
    intros.
    remember (c, r, m, K) as ccfg.
    remember (r', m', K') as cterm.
    generalize dependent r'.
    generalize dependent m'.
    generalize dependent K'.
    generalize dependent c.
    induction H; intros; try rewrite Heqccfg in H, Heqcterm; simpl in *; inversion Heqcterm; subst.
    - constructor; auto. now apply mode_alive_project_alive.
    - apply impe2_exp_sound with (is_left:=is_left) in H0.
      apply Cstep_assign with (x:=x) (e:=e) (v := project_value v is_left); auto.
      unfold ccfg_to_ecfg; simpl in *; auto.
      apply project_update_comm_reg.
      simpl in *; apply mode_alive_project_alive; auto.
    - apply impe2_exp_sound with (is_left:=is_left) in H1.
      apply Cstep_declassify with (x:=x) (e:=e) (v :=(project_value v is_left)); auto.
      apply project_update_comm_reg.
      now apply mode_alive_project_alive.
    - apply impe2_exp_sound with (is_left:=is_left) in H0.
      apply impe2_exp_sound with (is_left:=is_left) in H1.
      apply Cstep_update with (e1 := e1) (e2 := e2) (l := l) (v := project_value v is_left); auto.
      now apply mode_alive_project_alive.
      now apply mode_access_ok_project_ok.
      now apply project_update_comm_mem.
    - apply impe2_exp_sound with (is_left:=is_left) in H0; simpl in *.
      apply Cstep_output with (e := e); auto.
      now apply mode_alive_project_alive.
    - apply impe2_exp_sound with (is_left:=is_left) in H0; simpl in *.
      apply Cstep_call with (e := e) (c := c); auto.
      apply IHcstep2 with (c1 := c); auto.
    - apply impe2_exp_sound with (is_left := is_left) in H0; simpl in *;
        apply project_merge_inv_reg in H3; apply project_merge_inv_mem in H4.
      destruct_conjs; subst.
      destruct is_left;
        [apply Cstep_call with (e:=e) (c:=c1) | apply Cstep_call with (e:=e) (c:=c2)]; auto;
      unfold ccfg_update_com; simpl; rewrite project_merge_inv_trace; auto.
    - apply Cstep_cset with (c := c); auto.
      now apply mode_access_ok_project_ok.
      now apply project_update_comm_mem.
      now apply mode_alive_project_alive.
    - apply Cstep_enclave with (enc := enc) (c := c); auto.
      apply IHcstep2 with (c1 := c); auto.
    - apply Cstep_seq_nil; auto. 
    - apply Cstep_seq_hd with (hd:=hd) (tl:=tl)
                                       (r:=(project_reg r0 is_left))
                                       (m:=(project_mem m0 is_left))
                                       (k:=(project_kill k is_left))
                                       (tr:=(project_trace tr is_left))
                                       (tr':=(project_trace tr' is_left)); auto.
      apply IHcstep2_1 with (c0 := hd); auto.
      (* XXX: getting stuck with a weird induction hypothesis... maybe generalizing wrong *)
      apply IHcstep2_2 with (c := (Cseq tl)); auto.
      admit.
      now apply project_app_trace.
    - apply impe2_exp_sound with (is_left := is_left) in H0; simpl in *.
      apply Cstep_if with (e:=e) (c1:=c1) (c2:=c2) (v := (Vnat 1)); auto. discriminate.
      apply IHcstep2 with (c0 := c1); auto.
    - apply impe2_exp_sound with (is_left := is_left) in H0; simpl in *.
      apply Cstep_else with (e:=e) (c1:=c1) (c2:=c2) (v := (Vnat 0)); auto.
      apply IHcstep2 with (c0 := c2); auto.
    - apply impe2_exp_sound with (is_left := is_left) in H0; simpl in *;
        apply project_merge_inv_reg in H3; apply project_merge_inv_mem in H4;
          destruct_conjs; subst.
      destruct is_left; [destruct n1 | destruct n2].
      1,3: apply Cstep_else with (e := e) (c1 := c1) (c2 := c2) (v := Vnat 0); auto;
        rewrite project_merge_inv_trace; auto.
      apply Cstep_if with (e := e) (c1 := c1) (c2 := c2) (v := Vnat (S n1)); auto.
      discriminate.
      rewrite project_merge_inv_trace; auto.
      apply Cstep_if with (e := e) (c1 := c1) (c2 := c2) (v := Vnat (S n2)); auto.
      discriminate.
      rewrite project_merge_inv_trace; auto.
    - rewrite project_app_trace; simpl in *; subst.
      apply Cstep_while_t with (e := e) (c := c) (v := (Vnat 1))
                                        (r := (project_reg r0 is_left))
                                        (m := (project_mem m0 is_left))
                                        (k := (project_kill k is_left)); auto.
      now apply impe2_exp_sound with (is_left := is_left) in H0.
      now discriminate.
      now apply IHcstep2_1 with (c0 := c).
      now apply IHcstep2_2 with (c0 := (Cwhile e c)).
    - apply Cstep_while_f with (e := e) (c := c); auto.
      now apply impe2_exp_sound with (is_left := is_left) in H0.
      now apply mode_alive_project_alive.
    - apply impe2_exp_sound with (is_left := is_left) in H0; simpl in *;
        apply project_merge_inv_reg in H3; apply project_merge_inv_mem in H4;
          destruct_conjs; subst.
      admit.
     (* XXX: I think there's a typo in the paper's While-div rule that I need to figure out *)
     (* destruct is_left; [destruct n1 | destruct n2]; rewrite project_merge_inv_trace.
      +  assert (t1 = [] /\ k1 = (project_kill xK true) /\
                 (project_reg r true) = (project_reg r' true) /\
                 (project_mem m true) = (project_mem m' true)) by
            (inversion H1; subst; auto; try discriminate); destruct_conjs; subst.
         rewrite <- H4; rewrite <- H5.
         apply Cstep_while_f with (e := e) (c := c); auto.
         inversion H1; now try discriminate. *)

     
    - simpl in H0; subst; simpl in *; apply Cstep_kill with (enc := enc); auto.
      assert (mode_alive2 (Encl enc) K) by (unfold mode_alive2; now simpl).
      now apply mode_alive_project_alive.
      now apply project_add_comm_kill.      
  Admitted.

  Lemma impe2_exp_complete : forall md d e r m K v'i is_left,
      estep md d (e, project_reg r is_left, project_mem m is_left, project_kill K is_left) v'i ->
      exists v', estep2 md d (e, r, m, K) v' /\ (project_value v' is_left = v'i).
  Proof.
    intros.
    remember (e, project_reg r is_left, project_mem m is_left, project_kill K is_left) as ecfg.
    generalize dependent e.
    induction H; intros; rewrite Heqecfg in H; simpl in *.
    - exists (VSingle (Vnat n)); subst; split; auto; now constructor.
    - exists (VSingle (Vloc l)); subst; split; auto; now constructor.
    - exists (VSingle (Vlambda md c)); subst; split; auto; now constructor.
    - admit.
    - admit.
    - admit.
    - admit.
    Admitted. 
      
  Lemma impe2_complete : forall md d c r m K r'i m'i K'i t'i is_left,
      cstep md d (project_ccfg (c, r, m, K) is_left) (r'i, m'i, K'i) t'i ->
      exists r' m' K' t', cstep2 md d (c, r, m, K) (r', m', K') t' /\
                     (project_reg r' is_left) = r'i /\
                     (project_mem m' is_left) = m'i /\
                     (project_kill K' is_left) = K'i /\
                     (project_trace t' is_left) = t'i.
  Proof.
    (* Proof is done by straightforward induction *)
    intros; induction H; intuition.
  Admitted.
  
End Adequacy.

(***********************************)

Section Guarantees.

  Definition corresponds (G: context) (g: sec_spec) : Prop :=
    (forall l p bt rt, g l = p -> (loc_context G) l = Some (Typ bt p, rt))
    /\ (forall x, (var_context G) x = Some (Typ Tnat (LevelP L))).
  
  Definition g_prime (d: loc_mode) (g: sec_spec) (I: set enclave) : sec_spec :=
    fun l => match (d l) with
             | Encl i => if (set_mem Nat.eq_dec i I) then g l else LevelP L
             | _ => LevelP L
             end.
      
  Lemma secure_passive : forall g G G' K' d c,
    well_formed_spec g ->
    corresponds G g ->
    context_wt G d ->
    com_type (LevelP L) Normal G nil nil d c G' K' ->
    secure_prog L g cstep estep c.
  Proof.
  Admitted.

  Lemma secure_n_chaos : forall g G G' K' d c,
      well_formed_spec g ->
      corresponds G g ->
      context_wt G d ->
      com_type (LevelP L) Normal G nil nil d c G' K' ->
      secure_prog L g cstep_n_chaos estep c.
  Proof.
  Admitted.

  Lemma secure_e_chaos : forall g G G' K' d c I,
      well_formed_spec g ->
      corresponds G g ->
      context_wt G d ->
      com_type (LevelP L) Normal G nil nil d c G' K' ->
      secure_prog H (g_prime d g I) (cstep_e_chaos I) estep c.
  Proof.
  Admitted.
       
End Guarantees.

