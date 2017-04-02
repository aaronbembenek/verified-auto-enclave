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
Require Common.

Module ImpE.
Include Common.
  
Definition Enclave : Type := nat.
Inductive Mode : Type :=
| Normal : Mode
| Encl : Enclave -> Mode.

Section Syntax.
  Inductive Exp : Type :=
  | ENat : nat -> Exp
  | EVar : Var -> Exp
  | EPlus : Exp -> Exp -> Exp
  | EMult : Exp -> Exp -> Exp
  | ELoc : Location -> Exp
  | EDeref : Exp -> Exp
  | EIs_Unset : Condition -> Exp
  | ELambda : Mode -> Com -> Exp
                                   
  with Com : Type :=
  | CSkip : Com
  | CAssign : Var -> Exp -> Com
  | CDeclassify : Var -> Exp -> Com
  | CUpdate : Exp -> Exp -> Com
  | COutput : Exp -> Sec_Level -> Com
  | CSet : Condition -> Com
  | CEnclave : Enclave -> Com -> Com
  | CKill : Enclave -> Com
  | CSeq : list Com -> Com
  | CIf : Exp -> Com -> Com -> Com
  | CWhile : Exp -> Com -> Com.

  Inductive Val : Type :=
  | VLambda : Mode -> Com -> Val
  | VNat : nat -> Val
  | VLoc : Location -> Val.
End Syntax.

Section Semantics.
  Definition Reg : Type := Register Val.
  Definition Mem : Type := Memory Val.
  Definition Loc_Mode : Type := Location -> Mode.

  Definition EConfig : Type := Exp * Reg * Mem * set Enclave.
  Definition ecfg_exp (ecfg: EConfig) : Exp :=
    match ecfg with (e, _, _, _) => e end.
  Definition ecfg_reg (ecfg: EConfig) : Reg :=
    match ecfg with (_, r, _, _) => r end.
  (* FIXME: Not currently using the next two functions... *)
  Definition ecfg_mem (ecfg: EConfig) : Mem :=
    match ecfg with (_, _, m, _) => m end.
  Definition ecfg_kill (ecfg: EConfig) : set Enclave :=
    match ecfg with (_, _, _, k) => k end.
  Definition ecfg_update_exp (ecfg: EConfig) (e: Exp) : EConfig :=
    match ecfg with (_, r, m, k) => (e, r, m, k) end.
  
  Inductive EStep (md: Mode) (d: Loc_Mode) (ecfg: EConfig) : Val -> Prop :=
  | ESNat : forall n, ecfg_exp ecfg = ENat n -> EStep md d ecfg (VNat n)
  | ESLoc : forall l, ecfg_exp ecfg = ELoc l -> EStep md d ecfg (VLoc l)
  | ESLambda : forall c,
      ecfg_exp ecfg = ELambda md c -> EStep md d ecfg (VLambda md c)
  | ESVar : forall x v,
      ecfg_exp ecfg = EVar x -> ecfg_reg ecfg x = v -> EStep md d ecfg v
  | ESPlus : forall e1 e2 n1 n2,
      ecfg_exp ecfg = EPlus e1 e2 ->
      EStep md d (ecfg_update_exp ecfg e1) (VNat n1) ->
      EStep md d (ecfg_update_exp ecfg e2) (VNat n2) ->
      EStep md d ecfg (VNat (n1 + n2))
  | ESMult : forall e1 e2 n1 n2,
      ecfg_exp ecfg = EMult e1 e2 ->
      EStep md d (ecfg_update_exp ecfg e1) (VNat n1) ->
      EStep md d (ecfg_update_exp ecfg e2) (VNat n2) ->
      EStep md d ecfg (VNat (n1 * n2))
  | ESDeref : forall e r m k l v i,
      ecfg = (EDeref e, r, m, k) ->
      EStep md d (e, r, m, k) (VLoc l) ->
      m l = v ->
      d l = Normal \/ (d l = Encl i /\ ~set_In i k) ->
      EStep md d ecfg v
  | ESIs_Unset : forall cnd v res,
      ecfg_exp ecfg = EIs_Unset cnd ->
      EStep md d (ecfg_update_exp ecfg (EDeref (ELoc (Cnd cnd)))) v ->
      (v = VNat 0 /\ res = VNat 1) \/ (v <> VNat 0 /\ res = VNat 0) ->
      EStep md d ecfg res.

  (* FIXME: Semantics for commands. *)
End Semantics.
End ImpE.