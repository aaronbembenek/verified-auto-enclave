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
  Definition Var : Type := nat.
  
  Definition Condition : Type := nat.
  Inductive Location : Type :=
  | Non_Cnd : nat -> Location
  | Cnd : Condition -> Location.
  Definition is_cnd (l: Location) : Prop := exists c, l = Cnd c.
  Definition is_non_cnd (l: Location) : Prop := exists n, l = Non_Cnd n.

  Definition Register (value_t: Type) : Type := Var -> value_t.
  Definition Memory (value_t: Type) : Type := Location -> value_t.
End MachineModel.

Section Security.
  Inductive Sec_Level : Set :=
  | L : Sec_Level
  | H : Sec_Level
  | T : Sec_Level.
End Security.