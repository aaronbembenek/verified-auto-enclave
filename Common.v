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

Section MachineModel.
  Definition var : Type := nat.
  Definition location : Type := nat.
  Definition register (value_t: Type) : Type := var -> value_t.
  Definition memory (value_t: Type) : Type := location -> value_t.
End MachineModel.

Section Security.
  Inductive sec_level : Set :=
  | L : sec_level
  | H : sec_level.

  Definition sec_level_le (sl sl': sec_level) :=
    match sl, sl' with
    | H, L  => False
    | _, _ => True
    end.

  Definition sec_level_le_compute (sl sl': sec_level) :=
    match sl, sl' with
      | H, L  => false
      | _, _ => true
    end.
  Lemma sec_level_le_correct (sl sl': sec_level) :
    sec_level_le_compute sl sl' = true <-> sec_level_le sl sl'.
  Proof.
    destruct sl, sl'; intuition; try discriminate; unfold sec_level_le in *; auto.
  Qed.

  Definition sec_level_join (sl sl': sec_level) : sec_level :=
    match sl, sl' with
    | H, _ | _, H => H
    | L, L => L
    end.
  Lemma sec_level_join_ge (sl sl': sec_level) :
    sec_level_le sl (sec_level_join sl sl') /\ sec_level_le sl' (sec_level_join sl sl').
  Proof.
    induction sl, sl'; unfold sec_level_join; unfold sec_level_le; auto.
  Qed.
  Lemma sec_level_join_le_l (sl sl' sl'': sec_level) :
    sec_level_le (sec_level_join sl sl') sl'' -> sec_level_le sl sl''.
  Proof.
    induction sl, sl', sl''; unfold sec_level_join; unfold sec_level_le; auto.
  Qed.
  Lemma sec_level_join_le_r (sl sl' sl'': sec_level) :
    sec_level_le (sec_level_join sl sl') sl'' -> sec_level_le sl' sl''.
  Proof.
    induction sl, sl', sl''; unfold sec_level_join; unfold sec_level_le; auto.
  Qed.
  Lemma sec_level_le_trans (sl sl' sl'': sec_level) :
    sec_level_le sl sl' -> sec_level_le sl' sl'' -> sec_level_le sl sl''.
  Proof.
    intros; unfold sec_level_le; induction sl, sl', sl''; auto.
  Qed.
  Lemma sec_level_le_refl (sl : sec_level) :
    sec_level_le sl sl.
  Proof.
    intros; unfold sec_level_le; induction sl; auto.
  Qed.

  Definition sec_spec : Type :=  location -> sec_level.
  Definition well_formed_spec (g : sec_spec) : Prop := forall l, exists p, g l = p.

  Definition protected (sl: sec_level) : Prop := sl = H.
  Lemma join_protected_l (sl sl': sec_level) :
    protected sl -> protected (sec_level_join sl sl').
  Proof.
    induction sl, sl'; unfold sec_level_join; simpl; auto.
    intros. inversion H0.
  Qed.
  Lemma join_protected_r (sl sl': sec_level) :
    protected sl' -> protected (sec_level_join sl sl').
  Proof.
    induction sl, sl'; unfold sec_level_join; simpl; auto.
    intros. inversion H0.
  Qed.

  Parameter g0: sec_spec.
  
End Security.