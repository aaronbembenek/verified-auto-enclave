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

Section Syntax.
  Definition enclave : Type := nat.
  Inductive mode : Type :=
  | Normal : mode
  | Encl : enclave -> mode.
  
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
  | Ccall : exp -> com
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

  Function exp_novars (e : exp) : Prop :=
    match e with
    | Evar _ => False
    | Eplus e1 e2 => exp_novars e1 /\ exp_novars e2
    | Emult e1 e2 => exp_novars e1 /\ exp_novars e2
    | Ederef e => exp_novars e
    | Elambda md c => com_novars c
    | _ => True
    end
  with com_novars (c : com) : Prop :=
    match c with
    | Cassign _ e => exp_novars e
    | Cdeclassify _ e => exp_novars e
    | Cupdate e1 e2 => exp_novars e1 /\ exp_novars e2
    | Coutput e _ => exp_novars e
    | Cif e _ _ => exp_novars e
    | Cwhile e _ => exp_novars e
    | Ccall e => exp_novars e
    | _ => True
    end.
  
End Syntax.

Section Semantics.
  Definition reg : Type := register val.
  Definition init_regfile : reg := fun x => Vnat 0.
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

  Definition mode_alive (md : mode) (k : set enclave) :=
    match md with
    | Normal => True
    | Encl i => ~set_In i k
    end.
  Definition mode_access_ok (md : mode) (d : loc_mode) (l : location) (k : set enclave) :=
    let lmd := d l in
    match lmd with
    | Normal => True
    | Encl _ => md = lmd /\ mode_alive lmd k
    end.

  Definition econfig : Type := exp * reg * mem * set enclave.
  Definition ecfg_exp (ecfg: econfig) : exp :=
    match ecfg with (e, _, _, _) => e end.
  Definition ecfg_reg (ecfg: econfig) : reg :=
    match ecfg with (_, r, _, _) => r end.
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
      mode_access_ok md d l k ->
      estep md d ecfg v
  | Estep_isunset : forall cnd v res,
      ecfg_exp ecfg = Eisunset cnd ->
      estep md d (ecfg_update_exp ecfg (Ederef (Eloc (Cnd cnd)))) v ->
      (v = Vnat 0 /\ res = Vnat 1) \/ (v <> Vnat 0 /\ res = Vnat 0) ->
      estep md d ecfg res.

  (* Semantics for commands. *)
  (* FIXME : add inference rules for attackers? *)
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
  Definition ccfg_to_ecfg (e: exp) (ccfg : cconfig) : econfig :=
    (e, (ccfg_reg ccfg), (ccfg_mem ccfg), (ccfg_kill ccfg)).
  Definition ccfg_update_com (c: com) (ccfg : cconfig) : cconfig :=
    (c, (ccfg_reg ccfg), (ccfg_mem ccfg), (ccfg_kill ccfg)).
  
  Inductive cstep (md: mode) (d: loc_mode) (ccfg: cconfig) : cterm -> trace -> Prop :=
  | Cstep_skip : cstep md d ccfg (ccfg_reg ccfg, ccfg_mem ccfg, ccfg_kill ccfg) []
  | Cstep_assign : forall x e v r',
      ccfg_com ccfg = Cassign x e ->
      estep md d (ccfg_to_ecfg e ccfg) v ->
      r' = ccfg_update_reg ccfg x v ->
      mode_alive md (ccfg_kill ccfg) ->
      cstep md d ccfg (r', ccfg_mem ccfg, ccfg_kill ccfg) []
  | Cstep_declassify : forall x e v r',
      ccfg_com ccfg = Cdeclassify x e ->
      exp_novars e ->
      estep md d (ccfg_to_ecfg e ccfg) v ->
      r' = ccfg_update_reg ccfg x v ->
      mode_alive md (ccfg_kill ccfg) ->
      cstep md d ccfg (r', ccfg_mem ccfg, ccfg_kill ccfg) [Decl e (ccfg_mem ccfg)]
  | Cstep_update : forall e1 e2 l v m',
      ccfg_com ccfg = Cupdate e1 e2 ->
      estep md d (ccfg_to_ecfg e1 ccfg) (Vloc l) ->
      estep md d (ccfg_to_ecfg e2 ccfg) v ->
      mode_alive md (ccfg_kill ccfg) ->
      mode_access_ok md d l (ccfg_kill ccfg) ->
      is_Not_cnd l ->
      m' = ccfg_update_mem ccfg l v ->
      cstep md d ccfg (ccfg_reg ccfg, m', ccfg_kill ccfg) []
  | Cstep_output : forall e sl v,
      ccfg_com ccfg = Coutput e sl ->
      estep md d (ccfg_to_ecfg e ccfg) v ->
      sl = L \/ sl = H ->
      mode_alive md (ccfg_kill ccfg) ->
      cstep md d ccfg (ccfg_reg ccfg, ccfg_mem ccfg, ccfg_kill ccfg) [Mem (ccfg_mem ccfg); Out sl v]
  | Cstep_call : forall e c r' m' k' tr,
      ccfg_com ccfg = Ccall e ->
      estep md d (ccfg_to_ecfg e ccfg) (Vlambda md c) ->
      cstep md d (ccfg_update_com c ccfg) (r', m', k') tr ->
      cstep md d ccfg (r', m', k') tr
  | Cstep_cset : forall c m',
      ccfg_com ccfg = Cset c ->
      mode_access_ok md d (Cnd c) (ccfg_kill ccfg) ->
      m' = ccfg_update_mem ccfg (Cnd c) (Vnat 1) ->
      mode_alive md (ccfg_kill ccfg) ->
      cstep md d ccfg (ccfg_reg ccfg, m', ccfg_kill ccfg) [Mem m']
  | Cstep_enclave : forall enc c r' m' k' tr,
    md = Normal ->
    ccfg_com ccfg = Cenclave enc c ->
    cstep (Encl enc) d (c, ccfg_reg ccfg, ccfg_mem ccfg, ccfg_kill ccfg) (r', m', k') tr ->
    cstep md d ccfg (r', m', k') tr
  | Cstep_seq_nil :
      ccfg_com ccfg = Cseq [] ->
      cstep md d ccfg (ccfg_reg ccfg, ccfg_mem ccfg, ccfg_kill ccfg) []
  | Cstep_seq_hd : forall hd tl r m k tr r' m' k' tr',
      ccfg_com ccfg = Cseq (hd::tl) ->
      cstep md d (ccfg_update_com hd ccfg) (r, m, k) tr ->
      cstep md d (Cseq tl, r, m, k) (r', m', k') tr' ->
      cstep md d ccfg (r', m', k') (tr++tr')
  | Cstep_if : forall e c1 c2 v r' m' k' tr,
      ccfg_com ccfg = Cif e c1 c2 ->
      estep md d (ccfg_to_ecfg e ccfg) v ->
      ~(v = (Vnat 0)) ->
      cstep md d (ccfg_update_com c1 ccfg) (r', m', k') tr ->
      cstep md d ccfg (r', m', k') tr
  | Cstep_else : forall e c1 c2 v r' m' k' tr,
      ccfg_com ccfg = Cif e c1 c2 ->
      estep md d (ccfg_to_ecfg e ccfg) v ->
      v = (Vnat 0) ->
      cstep md d (ccfg_update_com c2 ccfg) (r', m', k') tr ->
      cstep md d ccfg (r', m', k') tr
  | Cstep_while_t : forall e c v r m k tr r' m' k' tr',
      ccfg_com ccfg = Cwhile e c ->
      estep md d (ccfg_to_ecfg e ccfg) v ->
      ~(v = (Vnat 0)) ->
      cstep md d (ccfg_update_com c ccfg) (r, m, k) tr ->
      cstep md d (ccfg_update_com (Cwhile e c) ccfg) (r', m', k') tr' ->
      cstep md d ccfg (r', m', k') (tr++tr')
  | Cstep_while_f : forall e c,
      ccfg_com ccfg = Cwhile e c ->
      estep md d (ccfg_to_ecfg e ccfg) (Vnat 0) ->
      mode_alive md (ccfg_kill ccfg) ->
      cstep md d ccfg (ccfg_reg ccfg, ccfg_mem ccfg, ccfg_kill ccfg) []
  | Cstep_kill : forall enc,
      md = Normal ->
      ccfg_com ccfg = Ckill enc ->
      mode_alive (Encl enc) (ccfg_kill ccfg) ->
      cstep md d ccfg (ccfg_reg ccfg, ccfg_mem ccfg, set_add Nat.eq_dec enc (ccfg_kill ccfg)) [].
                                            
End Semantics.
End ImpE.
