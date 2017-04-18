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

Module id_trans.

  Definition encl0 := 0.
  Definition md := E.Encl encl0.

  Definition rt_trans (rt: S.ref_type) : E.ref_type :=
    match rt with
    | S.Mut => E.Mut
    | S.Immut => E.Immut
    end.
  
  Fixpoint typ_trans (d: E.loc_mode) (s: S.base_type) : E.base_type :=
    match s with
    | S.Tnat => E.Tnat
    | S.Tcond => E.Tcond md
    | S.Tref (S.Typ s' p) rt =>
      E.Tref (E.Typ (typ_trans d s') p) md (rt_trans rt)
    | S.Tlambda Gminus U p Gplus =>
      E.Tlambda (cntxt_trans d Gminus) [] U p md (cntxt_trans d Gplus) []
    end

  with cntxt_trans (d: E.loc_mode) (G: S.context) : E.context :=
    match G with
    | S.Cntxt vc lc =>
      E.Cntxt
        (fun x =>
           match vc x with
           | None => None
           | Some (S.Typ s p) => Some (E.Typ (typ_trans d s) p)
           end)
        (fun l =>
           match lc l with
           | None => None
           | Some (S.Typ s p, rt) => Some (E.Typ (typ_trans d s) p, rt_trans rt)
           end)
    end.
  
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

  Hint Constructors E.exp_type E.com_type.
  
  Lemma id_trans_sound' (c: S.com) (d: E.loc_mode) :
    forall pc G U G',
      S.com_wt pc G U c G' ->
      E.com_type pc md (cntxt_trans d G) [] U d (id_trans c)
                 (cntxt_trans d G') [].
  Proof.
    induction c using S.com_ind' with
    (P0:=fun e => forall G s p,
             S.exp_wt G e (S.Typ s p) ->
             E.exp_type md (cntxt_trans d G) d (id_trans_e e)
                        (E.Typ (typ_trans d s) p)).
    - intros. inversion H. subst. simpl. apply E.ETnat.
    - intros. inversion H. subst. simpl. apply E.ETvar.
      destruct G. simpl in *. now rewrite H2.
    - intros. inversion H. subst. simpl.
      apply E.ETbinop; [apply IHc in H3 | apply IHc0 in H7]; auto.
    - intros. inversion H. subst. simpl. constructor. Focus 2. subst.

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

End id_trans.