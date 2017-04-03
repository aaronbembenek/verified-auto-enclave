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

  Definition register (value_t: Type) : Type := var -> value_t.
  Definition memory (value_t: Type) : Type := location -> value_t.
End MachineModel.

Section Security.
  Inductive sec_level : Set :=
  | L : sec_level
  | H : sec_level
  | T : sec_level.
End Security.