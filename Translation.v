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
Require Import Sorting.Permutation.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Common.
Require ImpE.
Require ImpS.

Module E := ImpE.
Module S := ImpS.

Module id_trans.

  Notation encl0 := 0.
  Notation md := (E.Encl encl0).
  Notation d := (fun (_: location) => md).

  Definition rt_trans (rt: S.ref_type) : E.ref_type :=
    match rt with
    | S.Mut => E.Mut
    | S.Immut => E.Immut
    end.
  
  Fixpoint typ_trans (s: S.base_type) : E.base_type :=
    match s with
    | S.Tnat => E.Tnat
    | S.Tcond => E.Tcond md
    | S.Tref (S.Typ s' p) rt =>
      E.Tref (E.Typ (typ_trans s') p) md (rt_trans rt)
    | S.Tlambda Gminus U p Gplus =>
      E.Tlambda (cntxt_trans Gminus) [] U p md (cntxt_trans Gplus) []
    end

  with cntxt_trans (G: S.context) : E.context :=
    match G with
    | S.Cntxt vc lc =>
      E.Cntxt
        (fun x =>
           match vc x with
           | None => None
           | Some (S.Typ s p) => Some (E.Typ (typ_trans s) p)
           end)
        (fun l =>
           match lc l with
           | None => None
           | Some (S.Typ s p, rt) => Some (E.Typ (typ_trans s) p, rt_trans rt)
           end)
    end.

  Lemma typ_trans_inv : forall s b,
      typ_trans s = typ_trans b -> s = b.
  Proof.
    (* Need a better inductive principle for types. *)
  Admitted.
  
  Lemma cntxt_trans_pres_dom : forall G x s p,
      S.var_in_dom G x (S.Typ s p) <->
      E.var_in_dom (cntxt_trans G) x (E.Typ (typ_trans s) p).
  Proof.
    intros.
    split; intros; inversion H; subst; constructor; destruct G; simpl in *.
    - now rewrite H0.
    - destruct (var_cntxt x). destruct t. inversion H0.
      apply typ_trans_inv in H2. now rewrite H2. discriminate.
  Qed.

  Lemma trans_pres_forall_var:
    forall (P: var -> S.type -> Prop) (P': var -> E.type -> Prop) G x s p,
      (P x (S.Typ s p) -> P' x (E.Typ (typ_trans s) p)) ->
      S.forall_var G P ->
      E.forall_var (cntxt_trans G) P'.
  Proof.
  Admitted.
  
  Fixpoint id_trans (c: S.com) : E.com :=
    match c with
    | S.Cskip => E.Cskip
    | S.Cassign x e => E.Cassign x (id_trans_e e)
    | S.Cdeclassify x e => E.Cdeclassify x (id_trans_e e)
    | S.Cupdate e1 e2 => E.Cupdate (id_trans_e e1) (id_trans_e e2)
    | S.Coutput e sl => E.Coutput (id_trans_e e) sl
    | S.Ccall e => E.Ccall (id_trans_e e)
    | S.Cset cnd => E.Cset cnd
    | S.Cseq cs => E.Cseq (map id_trans cs)
    | S.Cif e c1 c2 => E.Cif (id_trans_e e) (id_trans c1) (id_trans c2)
    | S.Cwhile e c => E.Cwhile (id_trans_e e) (id_trans c)
    end

  with id_trans_e (e: S.exp) : E.exp :=
    match e with
    | S.Enat n => E.Enat n
    | S.Evar x => E.Evar x
    | S.Ebinop e1 e2 op => E.Ebinop (id_trans_e e1) (id_trans_e e2) op
    | S.Eloc l => E.Eloc l
    | S.Ederef e => E.Ederef (id_trans_e e)
    | S.Eisunset cnd => E.Eisunset cnd
    | S.Elambda c => E.Elambda md (id_trans c)
    end.

  Definition id_trans_wrapper (c: S.com) : E.com :=
    E.Cenclave encl0 (id_trans c).
  
  Lemma trans_pres_novars : forall e,
      S.exp_novars e -> E.exp_novars (id_trans_e e).
  Proof.
  Admitted.

  Lemma trans_pres_all_loc_immutable : forall e G G',
      S.all_loc_immutable e G ->
      G' = cntxt_trans G ->
      E.all_loc_immutable (id_trans_e e) G'.
  Proof.
  Admitted.
  
  Hint Constructors E.exp_type E.com_type.
  
  Lemma id_trans_sound' (c: S.com) :
    forall pc G U G',
      S.com_wt pc G U c G' ->
      E.com_type pc md (cntxt_trans G) [] U d (id_trans c) (cntxt_trans G') [].
  Proof.
    induction c using S.com_ind' with
    (P0:=fun e => forall G s p,
             S.exp_wt G e (S.Typ s p) ->
             E.exp_type md (cntxt_trans G) d (id_trans_e e)
                        (E.Typ (typ_trans s) p)).
    - intros. inversion H. subst. simpl. apply E.ETnat.
    - intros. inversion H. subst. simpl. apply E.ETvar.
      destruct G. simpl in *. now rewrite H2.
    - intros. inversion H. subst. simpl.
      apply E.ETbinop; [apply IHc in H3 | apply IHc0 in H7]; auto.
    - intros. inversion H. subst. simpl. constructor. auto.
      subst. simpl. destruct t as [s q]. constructor; auto.
      destruct G. simpl in *. now rewrite H3.
    - intros. inversion H. subst. simpl.
      apply E.ETderef with (md':=md) (rt:=rt_trans rt).
      apply IHc in H3. simpl in H3. auto. intuition.
    - intros. inversion H. subst. simpl.
      apply E.ETunset with (md':=md); intuition.
    - intros. inversion H. subst. simpl. apply IHc in H3. now apply E.ETlambda.
    - intros. inversion H. subst. simpl. apply E.CTskip. simpl. intuition.
    - intros. inversion H0. subst. simpl.
      apply E.CTseq with (Gs:=map cntxt_trans Gs) (Ks:=map (fun _ => []) Gs).
      + repeat rewrite map_length. auto.
      + repeat rewrite map_length. auto.
      + destruct Gs; now simpl.
      + destruct Gs; now simpl.
      + intros. rewrite map_length in H1.
        assert (i < length coms) by auto.
        apply H7 in H1.
        assert (In (nth i coms S.Cskip) coms) by (now apply nth_In).
        rewrite Forall_forall in H.
        apply (H _ H4) in H1.
        assert (i < length Gs) by omega.
        assert (i + 1 < length Gs) by omega.
        assert (nth i (map cntxt_trans Gs) E.mt = cntxt_trans (nth i Gs S.mt))
          by (now apply nth_pres_map).
        assert (nth i (map (fun _: S.context => []) Gs) [] =
                ([]: set E.enclave)) by (apply nth_map_default).
        assert (nth i (map id_trans coms) E.Cskip =
                id_trans (nth i coms S.Cskip)) by (now apply nth_pres_map).
        assert (nth (i + 1) (map cntxt_trans Gs) E.mt =
                cntxt_trans (nth (i + 1) Gs S.mt)) by (now apply nth_pres_map).
        assert (nth (i + 1) (map (fun _ : S.context => []) Gs) [] =
                ([]: set E.enclave)) by (apply nth_map_default).
        congruence.
      + rewrite map_length. symmetry. apply nth_pres_map. omega.
      + symmetry. apply nth_map_default.
    - intros. inversion H. subst.
      replace (id_trans (S.Cassign x e)) with (E.Cassign x (id_trans_e e)).
      eapply E.CTassign with (s:=typ_trans s) (p:=p); auto.
      all: simpl; auto.
      + right. intuition. discriminate.
      + apply functional_extensionality. intro. now destruct (x0 =? x).
    - intros. inversion H. subst.
      replace (id_trans (S.Cdeclassify x e))
      with (E.Cdeclassify x (id_trans_e e)).
      eapply E.CTdeclassify with (s:=typ_trans s) (p:=p); auto.
      all: simpl; auto.
      + now apply trans_pres_novars.
      + now apply trans_pres_all_loc_immutable with (G:=S.Cntxt vc lc).
      + apply functional_extensionality. intro. now destruct (x0 =? x).
    - intros. inversion H. subst. simpl.
      eapply E.CTupdate with (p:=p) (q:=q) (p':=p') (s:=typ_trans s) (md':=md);
        simpl; auto.
      apply IHc in H2. simpl in H2. auto.
    - intros. inversion H. subst. simpl.
      eapply E.CToutput with (p:=p) (s:=typ_trans s); simpl; auto.
    - intros. inversion H. subst. simpl.
      eapply E.CTcall with (p:=p) (q:=q) (Gm:=cntxt_trans Gminus)
                                  (Gp:=cntxt_trans Gplus); auto.
      + apply IHc in H1. now simpl in H1.
      + right. intuition. discriminate.
      + (*unfold E.forall_dom. unfold S.forall_dom in H4. destruct H4. split.
        * unfold E.forall_var. intros. unfold S.forall_var in H0.
          inversion H6. destruct t.*) admit.
      + admit.
      + admit.
    - intros. inversion H. subst. simpl.
      eapply E.CTset with (md':=md); simpl; auto.
      + admit (* missing premise *).
    - intros. inversion H; subst; simpl.
      + eapply E.CTifunset; simpl; auto. apply IHc1 in H6. simpl in H6. auto.
      + eapply E.CTifelse with (p:=p) (pc':=pc'); simpl; auto.
        * intuition. destruct H0. assert (exists c, e = S.Eisunset c).
          {
            destruct e; simpl in *; try discriminate; eauto.
          }
          destruct H1. now apply H3 in H1.
        * apply IHc1 in H4. now simpl in H4.
        * right. intuition. discriminate.
    - intros. inversion H. subst. simpl.
      eapply E.CTwhile with (p:=p) (pc':=pc'); simpl; auto.
      + apply IHc in H2. now simpl in H2.
      + right. intuition. discriminate.
  Admitted.

End id_trans.