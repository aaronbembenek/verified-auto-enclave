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

  (* FIXME: Do we need to initialize everything to 0 or something? 
     what happens if we try to get the memory at a location that doesn't hold a value? *)
  Definition register (value_t: Type) : Type := var -> value_t.
  Definition memory (value_t: Type) : Type := location -> value_t.
End MachineModel.

Section Security.
  Inductive sec_level : Set :=
  | L : sec_level
  | H : sec_level
  | T : sec_level.
End Security.