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
  
Definition enclave : Type := nat.
Inductive mode : Type :=
| Normal : mode
| Encl : enclave -> mode.
(* FIXME: Seemed like we might want this but dunno if it'll be a pain *)
Definition enclave_dead (md : mode) (k : set enclave) :=
  match md with
  | Normal => False
  | Encl i => set_In i k
  end.
                    
Section Syntax.
  Inductive exp : Type :=
  | Enat : nat -> exp
  | Evar : var -> exp
  | Eplus : exp -> exp -> exp
  | Emult : exp -> exp -> exp
  | Eloc : location -> exp
  | Ederef : exp -> exp
  | Eisunset : condition -> exp
  | Elambda : mode -> com -> exp
                                   
  with com : Type :=
  | Cskip : com
  | Cassign : var -> exp -> com
  | Cdeclassify : var -> exp -> com
  | Cupdate : exp -> exp -> com
  | Coutput : exp -> sec_level -> com
  | Cset : condition -> com
  | Cenclave : enclave -> com -> com
  | Ckill : enclave -> com
  | Cseq : list com -> com
  | Cif : exp -> com -> com -> com
  | Cwhile : exp -> com -> com.

  Inductive val : Type :=
  | Vlambda : mode -> com -> val
  | Vnat : nat -> val
  | Vloc : location -> val.
End Syntax.

Section Semantics.
  Definition reg : Type := register val.
  Definition mem : Type := memory val.
  Definition loc_mode : Type := location -> mode.
  (* FIXME: Need to define enclave equivalence to use as a premise *)
  Inductive event : Type :=
  | Decl : exp -> mem -> event
  | Mem : mem -> event
  | Out : sec_level -> val -> event
  | ANonEnc : com -> event
  | AEnc : com -> event.
  Definition trace : Type := list event.

  Definition econfig : Type := exp * reg * mem * set enclave.
  Definition ecfg_exp (ecfg: econfig) : exp :=
    match ecfg with (e, _, _, _) => e end.
  Definition ecfg_reg (ecfg: econfig) : reg :=
    match ecfg with (_, r, _, _) => r end.
  (* FIXME: Not currently using the next two functions... *)
  Definition ecfg_mem (ecfg: econfig) : mem :=
    match ecfg with (_, _, m, _) => m end.
  Definition ecfg_kill (ecfg: econfig) : set enclave :=
    match ecfg with (_, _, _, k) => k end.
  Definition ecfg_update_exp (ecfg: econfig) (e: exp) : econfig :=
    match ecfg with (_, r, m, k) => (e, r, m, k) end.
  
  Inductive estep (md: mode) (d: loc_mode) (ecfg: econfig) : val -> Prop :=
  | Estep_nat : forall n, ecfg_exp ecfg = Enat n -> estep md d ecfg (Vnat n)
  | Estep_loc : forall l, ecfg_exp ecfg = Eloc l -> estep md d ecfg (Vloc l)
  | Estep_lambda : forall c,
      ecfg_exp ecfg = Elambda md c -> estep md d ecfg (Vlambda md c)
  | Estep_var : forall x v,
      ecfg_exp ecfg = Evar x -> ecfg_reg ecfg x = v -> estep md d ecfg v
  | Estep_plus : forall e1 e2 n1 n2,
      ecfg_exp ecfg = Eplus e1 e2 ->
      estep md d (ecfg_update_exp ecfg e1) (Vnat n1) ->
      estep md d (ecfg_update_exp ecfg e2) (Vnat n2) ->
      estep md d ecfg (Vnat (n1 + n2))
  | Estep_mult : forall e1 e2 n1 n2,
      ecfg_exp ecfg = Emult e1 e2 ->
      estep md d (ecfg_update_exp ecfg e1) (Vnat n1) ->
      estep md d (ecfg_update_exp ecfg e2) (Vnat n2) ->
      estep md d ecfg (Vnat (n1 * n2))
  | Estep_deref : forall e r m k l v,
      ecfg = (Ederef e, r, m, k) ->
      estep md d (e, r, m, k) (Vloc l) ->
      m l = v ->
      ~(enclave_dead(d l) k) ->
      estep md d ecfg v
  | Estep_isunset : forall cnd v res,
      ecfg_exp ecfg = Eisunset cnd ->
      estep md d (ecfg_update_exp ecfg (Ederef (Eloc (Cnd cnd)))) v ->
      (v = Vnat 0 /\ res = Vnat 1) \/ (v <> Vnat 0 /\ res = Vnat 0) ->
      estep md d ecfg res.

  (* Semantics for commands. *)
  Definition cconfig : Type := com * reg * mem * set enclave.
  Definition cterm : Type := reg * mem * set enclave.
  Definition ccfg_com (ccfg: cconfig) : com :=
    match ccfg with (c, _, _, _) => c end.
  Definition ccfg_reg (ccfg: cconfig) : reg :=
    match ccfg with (_, r, _, _) => r end.
  Definition ccfg_mem (ccfg: cconfig) : mem :=
    match ccfg with (_, _, m, _) => m end.
  Definition ccfg_kill (ccfg: cconfig) : set enclave :=
    match ccfg with (_, _, _, k) => k end.
  Definition ccfg_update_mem (ccfg: cconfig) (l: location) (v: val) : mem := 
    fun loc => if locations_eq loc l then v
               else (ccfg_mem ccfg) loc.
  Definition ccfg_update_reg (ccfg: cconfig) (x: var) (v: val) : reg :=
    fun var => if var =? x then v
               else (ccfg_reg ccfg) var.
  Definition ecfg_of_ccfg (e: exp) (ccfg : cconfig) : econfig :=
    (e, (ccfg_reg ccfg), (ccfg_mem ccfg), (ccfg_kill ccfg)).
  
  Inductive cstep (md: mode) (d: loc_mode) (ccfg: cconfig) : cterm -> trace -> Prop :=
  | Cstep_skip : cstep md d ccfg (ccfg_reg ccfg, ccfg_mem ccfg, ccfg_kill ccfg) []
  | Cstep_assign : forall x e v r',
      ccfg_com ccfg = Cassign x e ->
      estep md d (ecfg_of_ccfg e ccfg) v ->
      r' = ccfg_update_reg ccfg x v ->
      ~(enclave_dead md (ccfg_kill ccfg)) ->
      cstep md d ccfg (r', ccfg_mem ccfg, ccfg_kill ccfg) [].
  (*
  | Cdeclassify : var -> exp -> com
  | Cupdate : exp -> exp -> com
  | Coutput : exp -> sec_level -> com
  | Cset : condition -> com
  | Cenclave : enclave -> com -> com
  | Ckill : enclave -> com
  | Cseq : list com -> com
  | Cif : exp -> com -> com -> com
  | Cwhile : exp -> com -> com.
*)

                                            
End Semantics.
End ImpE.
