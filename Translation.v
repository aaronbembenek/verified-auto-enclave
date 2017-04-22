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

Module S := ImpS.
Module E := ImpE.

Section TypeTrans.
  Definition subdom {A B C: Type} (f: A -> option B) (g: A -> option C) :=
    forall x,
      match f x with
      | Some _ => exists y, g x = Some y
      | None => True
      end.
  
  Inductive btrans : S.base_type -> E.loc_mode -> E.base_type -> Prop :=
  | Btrans_nat : forall d, btrans S.Tnat d E.Tnat
  | Btrans_cond : forall d md, btrans S.Tcond d (E.Tcond md)
  | Btrans_ref : forall d s s' p md rt,
      btrans s d s' ->
      btrans (S.Tref (S.Typ s p) rt) d (E.Tref (E.Typ s' p) md rt)
  | Btrans_lambda : forall Gm G'm Gp G'p d U p Km Kp md,
      context_trans Gm d G'm ->
      context_trans Gp d G'p ->
      btrans (S.Tlambda Gm U p Gp) d (E.Tlambda G'm Km U p md G'p Kp)

  with ttrans : S.type -> E.loc_mode -> E.type -> Prop :=
  | Ttrans : forall s p s' d,
      btrans s d s' ->
      ttrans (S.Typ s p) d (E.Typ s' p)

  with context_trans : S.context -> E.loc_mode -> E.context -> Prop :=
  | Gtrans : forall G d G',
      subdom (S.var_context G) (E.var_context G') ->
      subdom (S.loc_context G) (E.loc_context G') ->
      subdom (E.var_context G') (S.var_context G) ->
      subdom (E.loc_context G') (S.loc_context G) ->
      S.forall_var G (fun x t =>
                        exists t',
                          ttrans t d t' /\ E.var_in_dom G' x t') ->
      S.forall_loc G (fun x t rt =>
                        exists t',
                          ttrans t d t' /\ E.loc_in_dom G' x t' rt) ->
      S.forall_loc G (fun x t rt =>
                        let (s, p) := t in
                        policy_le p (LevelP L) \/ d x <> E.Normal) ->
      context_trans G d G'.
End TypeTrans.

Section TransDef.
  Inductive exp_trans : S.context -> S.exp -> S.type -> E.mode -> E.context ->
    E.loc_mode -> E.exp -> E.type -> Prop :=
  | TRnat : forall sG n p md eG d,
      exp_trans sG (S.Enat n) (S.Typ S.Tnat p)
                md eG d (E.Enat n) (E.Typ E.Tnat p)
  | TRvar : forall sG x t t' eG md d,
      ttrans t d t' ->
      E.var_context eG x = Some t' ->
      exp_trans sG (S.Evar x) t
                md eG d (E.Evar x) t'
  | TRcnd : forall sG cnd p d md md' eG,
      d (Cnd cnd) = md' ->
      exp_trans sG (S.Eloc (Cnd cnd)) (S.Typ S.Tcond p)
                md eG d (E.Eloc (Cnd cnd)) (E.Typ (E.Tcond md') p)
  | TRisunset : forall sG cnd md' md eG d p,
      d (Cnd cnd) = md' ->
      md' = E.Normal \/ md = md' ->
      exp_trans sG (S.Eisunset cnd) (S.Typ S.Tnat p)
                md eG d (E.Eisunset cnd) (E.Typ E.Tnat p)
  | TRloc : forall sG l t rt (q: sec_level) t' md' md eG d q,
      ttrans (S.Typ (S.Tref t rt) q) d (E.Typ (E.Tref t' md' rt) q) ->
      E.loc_context eG (Not_cnd l) = Some (t', rt) ->
      d (Not_cnd l) = md' ->
      exp_trans sG (S.Eloc (Not_cnd l)) (S.Typ (S.Tref t rt) q)
                md eG d (E.Eloc (Not_cnd l)) (E.Typ (E.Tref t' md' rt) q)
  | TRderef : forall sG (eG: E.context) e s p s' rt q md eG d e' md' p',
      exp_trans sG e (S.Typ (S.Tref (S.Typ s p) rt) q)
                md eG d e' (E.Typ (E.Tref (E.Typ s' p) md' rt) q) ->
      md' = E.Normal \/ md = md' ->
      p' = policy_join p q ->
      exp_trans sG (S.Ederef e) (S.Typ s p')
                md eG d (E.Ederef e') (E.Typ s' p').
End TransDef.

Section TransProof.  
  Lemma exp_trans_sound : forall e sG t md eG d e' t',
    S.exp_wt sG e t ->
    exp_trans sG e t md eG d e' t' ->
    E.exp_type md eG d e' t'.
  Proof.
    intros.
    induction H0.
    - inversion H. eapply E.ETnat.
    - now eapply E.ETvar.
    - inversion H. now eapply E.ETcnd.
    - inversion H. eapply E.ETunset with (md':=md'); intuition.
    - inversion H. now eapply E.ETloc.
    - eapply E.ETderef with (md':=md') (rt:=rt) (p:=p) (q:=q). inversion H. subst.
      Restart.
      induction e. Focus 5. intros.
      inversion H. inversion H0. subst.
      
  Admitted.
  
End TransProof.