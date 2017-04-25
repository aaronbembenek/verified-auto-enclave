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
Require Import OrderedType.

Module NatMap := FMapList.Make Nat_as_OT.
Module NatMapFacts := FMapFacts.WFacts_fun Nat_as_OT NatMap.

Section MachineModel.
  Definition var : Type := nat.
  
  Definition condition : Type := nat.
  Inductive location : Type :=
  | Not_cnd : nat -> location
  | Cnd : condition -> location.

  Inductive ref_type : Set :=
  | Mut
  | Immut.
  
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

  Definition update {B: Type} (f: nat -> B) (x: nat) (y: B) :=
    fun x0 => if x =? x0 then y else f x0.
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

  Inductive policy0 : Type :=
  | LevelP : sec_level -> policy0
  | ErasureP (l1: sec_level) (cnd: condition) (l2: sec_level)
             (l1_le_l2: sec_level_le l1 l2) : policy0.

  Inductive policy0_le : relation policy0 :=
  | BPLE1 : forall l1 l2,
      sec_level_le l1 l2 ->
      policy0_le (LevelP l1) (LevelP l2)
  | BPLE2 : forall p1 l2 l2' cnd pf,
      policy0_le p1 (LevelP l2) ->
      policy0_le p1 (ErasureP l2 cnd l2' pf)
  | BPLE3 : forall l1 l1' p2 cnd pf,
      policy0_le (LevelP l1') p2 ->
      policy0_le (ErasureP l1 cnd l1' pf) p2
  | BPLE4 : forall l1 l1' l2 l2' cnd pf1 pf2,
      sec_level_le l1 l2 ->
      sec_level_le l1' l2' ->
      policy0_le (ErasureP l1 cnd l1' pf1) (ErasureP l2 cnd l2' pf2).

  Definition ub x y z := policy0_le x z /\ policy0_le y z.

  Definition lub x y z :=
    ub x y z /\ (forall z0, ub x y z0 -> policy0_le z z0).
  
  Inductive policy : Type :=
  | SingleP : policy0 -> policy
  | JoinP : policy -> policy -> policy.

  Inductive pdenote : policy -> policy0 -> Prop :=
  | Psingle : forall p0, pdenote (SingleP p0) p0
  | Pjoin : forall p p0 p' p'0 q,
      pdenote p p0 ->
      pdenote p' p'0 ->
      lub p0 p'0 q ->
      pdenote (JoinP p p') q.
  
  Definition sec_spec : Type :=  location -> policy.

  Definition policy_le (p q: policy) : Prop :=
    forall p0 q0,
      pdenote p p0 ->
      pdenote q q0 ->
      policy0_le p0 q0.

  Definition liftp p := SingleP p.

  (* XXX might need axioms about sec policy lattice. *)

  (*
  Lemma policy_le_refl : reflexive sec_policy policy_le.
  Proof.
    intro x. destruct x.
    - apply PLE1. apply sec_level_le_refl.
    - apply PLE4; apply sec_level_le_refl.
    - 
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
      set_In cnd S -> protected (ErasureP L cnd sl pf) S.
  *)

End Security.

Lemma nth_pres_map {A B: Type} i (xs: list A) (f: A -> B) y z :
    i < length xs ->
    nth i (map f xs) y = f (nth i xs z).
Proof.
  revert xs. induction i; intros; destruct xs; simpl in *.
  - omega.
  - auto.
  - inversion H0.
  - apply lt_S_n in H0. auto.
Qed.

Lemma nth_map_default {A B: Type}: forall i (xs: list A) (x: B),
    nth i (map (fun _ => x) xs) x = x.
Proof.
  induction i; destruct xs; simpl; auto.
Qed.
    
