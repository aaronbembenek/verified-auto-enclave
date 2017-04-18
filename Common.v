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
  
  Definition condition : Type := nat.
  Inductive location : Type :=
  | Not_cnd : nat -> location
  | Cnd : condition -> location.
  Definition is_Cnd (l: location) : Prop :=
    match l with
    | Not_cnd _ => False
    | Cnd _ => True
    end.
  Definition is_Not_cnd (l: location) : Prop :=
    match l with
    | Not_cnd _ => True
    | Cnd _ => False
    end.
  Definition locations_eq l1 l2: bool :=
    match l1, l2 with
    | Not_cnd n, Not_cnd n' => n =? n'
    | Cnd c, Cnd c' => c =? c'
    | _, _ => false
    end.

  Definition register (value_t: Type) : Type := var -> value_t.
  Definition memory (value_t: Type) : Type := location -> value_t.
End MachineModel.

Section Security.
  Inductive sec_level : Set :=
  | L : sec_level
  | H : sec_level
  | T : sec_level.

  Inductive sec_level_rel : relation sec_level :=
  | sec_level_l_rel : sec_level_rel L H
  | sec_level_h_rel : sec_level_rel H T.
 
  Definition sec_level_le := clos_refl_trans sec_level sec_level_rel.
  
  Global Instance sec_level_le_refl : Reflexive sec_level_le.
  intro sl; destruct sl; unfold sec_level_le; apply rt_refl.
  Defined.

  Global Instance sec_level_le_trans : Transitive sec_level_le.
  intros sl1 sl2 sl3;  unfold sec_level_le; intros.
  apply rt_trans with (y:=sl2); auto.
  Defined.

  Lemma sec_level_le_dec : forall sl sl', {sec_level_le sl sl'} + {sec_level_le sl' sl}.
  Proof.
    intros; destruct sl, sl'; intuition;
      [left|left|right|left|right|right]; unfold sec_level_le.
    apply rt_step; apply sec_level_l_rel.
    apply rt_trans with (y := H); apply rt_step; [apply sec_level_l_rel | apply sec_level_h_rel].
    apply rt_step; apply sec_level_l_rel.
    apply rt_step; apply sec_level_h_rel.
    apply rt_trans with (y := H); apply rt_step; [apply sec_level_l_rel | apply sec_level_h_rel].
    apply rt_step; apply sec_level_h_rel.
  Qed.

  Definition sec_level_le_compute (sl sl': sec_level) :=
    match sl, sl' with
      | H, L | T, L | T, H => false
      | _, _ => true
    end.
  Lemma sec_level_le_correct (sl sl': sec_level) :
    sec_level_le_compute sl sl' = true <-> sec_level_le sl sl'.
  Proof.
    destruct sl, sl'; intuition; try discriminate; unfold sec_level_le in *.
    apply rt_step. constructor.
    apply rt_trans with (y := H); apply rt_step; constructor.
    (* XXX why is it so hard to prove that sec_level_le H L is False? *)
  Admitted.

  Definition sec_level_join (sl sl': sec_level) : sec_level :=
    match sl, sl' with
    | T, _ | _, T => T
    | H, _ | _, H => H
    | L, L => L
    end.

  Inductive sec_policy : Type :=
  | LevelP : sec_level -> sec_policy
  | ErasureP (l1: sec_level) (cnd: condition) (l2: sec_level)
             (l1_le_l2: sec_level_le l1 l2) : sec_policy.
  
  Definition sec_spec : Type :=  location -> sec_policy.

  Definition well_formed_spec (g : sec_spec) : Prop :=
    forall l, exists p, g l = p /\ p <> LevelP T /\ forall cnd sl pf, p <> ErasureP T cnd sl pf.

  Inductive policy_le : relation sec_policy :=
  | PLE1 : forall l1 l2,
      sec_level_le l1 l2 ->
      policy_le (LevelP l1) (LevelP l2)
  | PLE2 : forall p1 l2 l2' cnd pf,
      policy_le p1 (LevelP l2) ->
      policy_le p1 (ErasureP l2 cnd l2' pf)
  | PLE3 : forall l1 l1' p2 cnd pf,
      policy_le (LevelP l1') p2 ->
      policy_le (ErasureP l1 cnd l1' pf) p2
  | PLE4 : forall l1 l1' l2 l2' cnd pf1 pf2,
      sec_level_le l1 l2 ->
      sec_level_le l1' l2' ->
      policy_le (ErasureP l1 cnd l1' pf1) (ErasureP l2 cnd l2' pf2).

  Lemma policy_le_refl : reflexive sec_policy policy_le.
  Proof.
    intro x. destruct x.
    - apply PLE1. apply sec_level_le_refl.
    - apply PLE4; apply sec_level_le_refl.
  Qed.

  Lemma policy_le_antisymmetric : antisymmetric sec_policy policy_le.
  Proof.
  Admitted.

  Lemma policy_le_transitive : transitive sec_policy policy_le.
  Proof.
  Admitted.
  
  Lemma policy_le_partial_order : order sec_policy policy_le.
  Proof.
    split.
    - apply policy_le_refl.
    - apply policy_le_transitive.
    - apply policy_le_antisymmetric.
  Qed.  
  
  Parameter policy_join : sec_policy -> sec_policy -> sec_policy.
  Axiom policy_le_join : forall p1 p2,
      policy_le p1 (policy_join p1 p2) /\ policy_le p2 (policy_join p1 p2).
  
  Function cur (p : sec_policy) (U : set condition) : sec_level :=
    match p with
    | LevelP l => l
    | ErasureP l1 cnd l2 _ => if (set_mem Nat.eq_dec cnd U) then l1 else l2
    end.

  Inductive protected : sec_policy -> set condition -> Prop :=
  | level_high: forall S, protected (LevelP H) S
  | level_top: forall S, protected (LevelP T) S
  | erase_high: forall cnd S sl pf,
      protected (ErasureP H cnd sl pf) S
  | erase_low: forall cnd S sl pf,
      set_In cnd S -> protected (ErasureP L cnd sl pf) S
  | join_protected_l: forall S p p',
      protected p S ->
      protected (policy_join p p') S
  | join_protected_r: forall S p p',
      protected p' S ->
      protected (policy_join p p') S.

End Security.