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

  Definition dom_eq (G: S.context) (G': E.context) :=
    (forall x, (exists t, S.var_in_dom G x t) <->
               (exists t', E.var_in_dom G' x t')) /\
    (forall l, (exists t rt, S.loc_in_dom G l t rt) <->
               (exists t' rt', E.loc_in_dom G' l t' rt')).
  
  Inductive ttrans : S.base_type -> E.loc_mode -> E.base_type -> Prop :=
  | Ttrans_nat : forall d, ttrans S.Tnat d E.Tnat
  | Ttrans_cond : forall d md, ttrans S.Tcond d (E.Tcond md)
  | Ttrans_ref : forall d s s' p md rt,
      ttrans s d s' ->
      ttrans (S.Tref (S.Typ s p) rt) d (E.Tref (E.Typ s' p) md rt)
  | Ttrans_lambda : forall Gm G'm Gp G'p d U p Km Kp md,
      context_trans Gm d G'm ->
      context_trans Gp d G'p ->
      ttrans (S.Tlambda Gm U p Gp) d (E.Tlambda G'm Km U p md G'p Kp)

  with type_trans : S.type -> E.loc_mode -> E.type -> Prop :=
  | Ttrans : forall s p s' d,
      ttrans s d s' ->
      type_trans (S.Typ s p) d (E.Typ s' p)

  with context_trans : S.context -> E.loc_mode -> E.context -> Prop :=
  | Gtrans : forall G d G',
      dom_eq G G' ->
      S.forall_var G (fun x t =>
                        exists t',
                          type_trans t d t' /\ E.var_in_dom G' x t') ->
      S.forall_loc G (fun x t rt =>
                        exists t',
                          type_trans t d t' /\ E.loc_in_dom G' x t' rt) ->
      S.forall_loc G (fun x t rt =>
                        let (s, p) := t in
                        policy_le p (LevelP L) \/ d x <> E.Normal) ->
      context_trans G d G'. 
End TypeTrans.