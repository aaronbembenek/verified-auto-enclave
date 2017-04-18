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
Require Import Common.
Require ImpE.
Require ImpS.

Module E := ImpE.
Module S := ImpS.

Function id_trans (md: E.mode) (c: S.com) : E.com :=
  match c with
  | S.Cskip => E.Cskip
  | S.Cassign x e => E.Cassign x (id_trans_e md e)
  | S.Cdeclassify x e => E.Cdeclassify x (id_trans_e md e)
  | S.Cupdate e1 e2 => E.Cupdate (id_trans_e md e1) (id_trans_e md e2)
  | S.Coutput e sl => E.Coutput (id_trans_e md e) sl
  | S.Ccall e => E.Ccall (id_trans_e md e)
  | S.Cset cnd => E.Cset cnd
  | S.Cseq cs => E.Cseq (map (id_trans md) cs)
  | S.Cif e c1 c2 => E.Cif (id_trans_e md e) (id_trans md c1) (id_trans md c2)
  | S.Cwhile e c => E.Cwhile (id_trans_e md e) (id_trans md c)
  end

with id_trans_e (md: E.mode) (e: S.exp) : E.exp :=
  match e with
  | S.Enat n => E.Enat n
  | S.Evar x => E.Evar x
  | S.Ebinop e1 e2 op => E.Ebinop (id_trans_e md e1) (id_trans_e md e2) op
  | S.Eloc l => E.Eloc l
  | S.Ederef e => E.Ederef (id_trans_e md e)
  | S.Eisunset cnd => E.Eisunset cnd
  | S.Elambda c => E.Elambda md (id_trans md c)
  end.

Definition id_trans_wrapper (c: S.com) : E.com :=
  E.Cenclave 0 (id_trans (E.Encl 0) c).

(*
Lemma id_trans_ind:
  forall (P: E.mode -> S.com -> E.com -> Prop)
         (P0: E.mode -> S.exp -> E.exp -> Prop),
    (forall cs md,
        Forall (fun c => P md c (id_trans md c)) cs ->
        P md (S.Cseq cs) (E.Cseq (map (id_trans md) cs))) ->
    forall c md, P md c (id_trans md c).
Proof.
  intros.
  induction c using S.com_ind' with (P0:=fun e => P0 md e (id_trans_e md e)).
  Focus 9. simpl. auto.
  *)