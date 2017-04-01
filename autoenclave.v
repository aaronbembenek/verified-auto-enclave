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

Variable Location : Type.
Variable Condition : set Location.
Definition is_cond (l: Location): Prop := set_In l Condition.

Variable Var : Type.

Inductive Mode : Set :=
| Normal : Mode
| Enclave : nat -> Mode.

Inductive Sec_Level : Set :=
| L : Sec_Level
| H : Sec_Level
| T : Sec_Level.

Section ImpE.
Section Syntax.
  Inductive Exp : Type :=
  | ENat : nat -> Exp
  | EVar : Var -> Exp
  | EPlus : Exp -> Exp -> Exp
  | EMult : Exp -> Exp -> Exp
  | ELoc : Location -> Exp
  | EDeref : Exp -> Exp
  | EIs_Unset (l: Location) : is_cond l -> Exp
  | ELambda : Mode -> Com -> Exp
                                   
  with Com : Type :=
  | CSkip : Com
  | CAssign : Var -> Exp -> Com
  | CDeclassify : Var -> Exp -> Com
  | CUpdate : Exp -> Exp -> Com
  | COutput : Exp -> Sec_Level -> Com
  | CSet (l: Location) : is_cond l -> Com
  | CEnclave : nat -> Com -> Com
  | CKill : nat -> Com
  | CSeq : list Com -> Com
  | CIfElse : Exp -> Com -> Com -> Com
  | CWhile : Exp -> Com -> Com.

  Inductive Val : Type :=
  | VLambda : Mode -> Com -> Val
  | VNat : nat -> Val
  | VLoc : Location -> Val.
End Syntax.

Section Semantics.
  Definition Reg : Type := Var -> Val.
  Definition Mem : Type := Location -> Val.

  Variable delta : Location -> Mode.
  
  Inductive EConfig : Type :=
  | ECfg (e: Exp) (r: Reg) (m: Mem) (k: set nat) : EConfig.
  
  Inductive EStep (m: Mode) (ecfg: EConfig): Val -> Prop :=
  | ESNat : forall n r mem k,
      ecfg = ECfg (ENat n) r mem k -> EStep m ecfg (VNat n).
End Semantics.
End ImpE.