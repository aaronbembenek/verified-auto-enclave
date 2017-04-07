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
Require Import Common.

Module ImpS.

Section Syntax.
  Inductive exp : Type :=
  | Enat : nat -> exp
  | Evar : var -> exp
  | Eplus : exp -> exp -> exp
  | Emult : exp -> exp -> exp
  | Eloc : location -> exp
  | Ederef : exp -> exp
  | Eisunset : condition -> exp
  | Elambda : com -> exp
                                   
  with com : Type :=
  | Cskip : com
  | Cassign : var -> exp -> com
  | Cdeclassify : var -> exp -> com
  | Cupdate : exp -> exp -> com
  | Coutput : exp -> sec_level -> com
  | Ccall : exp -> com
  | Cset : condition -> com
  | Cseq : list com -> com
  | Cif : exp -> com -> com -> com
  | Cwhile : exp -> com -> com.

  Inductive val : Type :=
  | Vlambda : com -> val
  | Vnat : nat -> val
  | Vloc : location -> val.

  Function exp_novars (e : exp) : Prop :=
    match e with
    | Evar _ => False
    | Eplus e1 e2 => exp_novars e1 /\ exp_novars e2
    | Emult e1 e2 => exp_novars e1 /\ exp_novars e2
    | Ederef e => exp_novars e
    | Elambda c => com_novars c
    | _ => True
    end
  with com_novars (c : com) : Prop :=
    match c with
    | Cassign _ e => exp_novars e
    | Cdeclassify _ e => exp_novars e
    | Cupdate e1 e2 => exp_novars e1 /\ exp_novars e2
    | Coutput e _ => exp_novars e
    | Cif e c1 c2 => exp_novars e /\ com_novars c1 /\ com_novars c2
    | Cwhile e c => exp_novars e /\ com_novars c
    | Ccall e => exp_novars e
    | Cseq ls => fold_left (fun acc c => (com_novars c) /\ acc) ls True                           
    | _ => True
    end.
  
End Syntax.

Section Semantics.
  Definition reg : Type := register val.
  Definition init_regfile : reg := fun x => Vnat 0.
  Definition mem : Type := memory val.

  (* FIXME: what to do about attackers? don't need to model, I'm guessing *)
  Inductive event : Type :=
  | Decl : exp -> mem -> event
  | Mem : mem -> event
  | Out : sec_level -> val -> event.
  Definition trace : Type := list event.

  Definition econfig : Type := exp * reg * mem.
  Definition ecfg_exp (ecfg: econfig) : exp :=
    match ecfg with (e, _, _) => e end.
  Definition ecfg_reg (ecfg: econfig) : reg :=
    match ecfg with (_, r, _) => r end.
  Definition ecfg_mem (ecfg: econfig) : mem :=
    match ecfg with (_, _, m) => m end.
  Definition ecfg_update_exp (ecfg: econfig) (e: exp) : econfig :=
    match ecfg with (_, r, m) => (e, r, m) end.

  
  Inductive estep (ecfg: econfig) : val -> Prop :=
  | Estep_nat : forall n, ecfg_exp ecfg = Enat n -> estep ecfg (Vnat n)
  | Estep_loc : forall l, ecfg_exp ecfg = Eloc l -> estep ecfg (Vloc l)
  | Estep_lambda : forall c,
      ecfg_exp ecfg = Elambda c -> estep ecfg (Vlambda c)
  | Estep_var : forall x v,
      ecfg_exp ecfg = Evar x -> ecfg_reg ecfg x = v -> estep ecfg v
  | Estep_plus : forall e1 e2 n1 n2,
      ecfg_exp ecfg = Eplus e1 e2 ->
      estep (ecfg_update_exp ecfg e1) (Vnat n1) ->
      estep (ecfg_update_exp ecfg e2) (Vnat n2) ->
      estep ecfg (Vnat (n1 + n2))
  | Estep_mult : forall e1 e2 n1 n2,
      ecfg_exp ecfg = Emult e1 e2 ->
      estep (ecfg_update_exp ecfg e1) (Vnat n1) ->
      estep (ecfg_update_exp ecfg e2) (Vnat n2) ->
      estep ecfg (Vnat (n1 * n2))
  | Estep_deref : forall e r m l v,
      ecfg = (Ederef e, r, m) ->
      estep (e, r, m) (Vloc l) ->
      m l = v ->
      estep ecfg v
  | Estep_isunset : forall cnd v res,
      ecfg_exp ecfg = Eisunset cnd ->
      estep (ecfg_update_exp ecfg (Ederef (Eloc (Cnd cnd)))) v ->
      (v = Vnat 0 /\ res = Vnat 1) \/ (v <> Vnat 0 /\ res = Vnat 0) ->
      estep ecfg res.

  (* Semantics for commands. *)
  Definition cconfig : Type := com * reg * mem.
  Definition cterm : Type := reg * mem.
  Definition ccfg_com (ccfg: cconfig) : com :=
    match ccfg with (c, _, _) => c end.
  Definition ccfg_reg (ccfg: cconfig) : reg :=
    match ccfg with (_, r, _) => r end.
  Definition ccfg_mem (ccfg: cconfig) : mem :=
    match ccfg with (_, _, m) => m end.
  Definition ccfg_update_mem (ccfg: cconfig) (l: location) (v: val) : mem := 
    fun loc => if locations_eq loc l then v
               else (ccfg_mem ccfg) loc.
  Definition ccfg_update_reg (ccfg: cconfig) (x: var) (v: val) : reg :=
    fun var => if var =? x then v
               else (ccfg_reg ccfg) var.
  Definition ccfg_to_ecfg (e: exp) (ccfg : cconfig) : econfig :=
    (e, (ccfg_reg ccfg), (ccfg_mem ccfg)).
  Definition ccfg_update_com (c: com) (ccfg : cconfig) : cconfig :=
    (c, (ccfg_reg ccfg), (ccfg_mem ccfg)).

  Inductive cstep (ccfg: cconfig) : cterm -> trace -> Prop :=
  | Cstep_skip : cstep ccfg (ccfg_reg ccfg, ccfg_mem ccfg) []
  | Cstep_assign : forall x e v r',
      ccfg_com ccfg = Cassign x e ->
      estep (ccfg_to_ecfg e ccfg) v ->
      r' = ccfg_update_reg ccfg x v ->
      cstep ccfg (r', ccfg_mem ccfg) []
  | Cstep_declassify : forall x e v r',
      ccfg_com ccfg = Cdeclassify x e ->
      exp_novars e ->
      estep (ccfg_to_ecfg e ccfg) v ->
      r' = ccfg_update_reg ccfg x v ->
      cstep ccfg (r', ccfg_mem ccfg) [Decl e (ccfg_mem ccfg)]
  | Cstep_update : forall e1 e2 l v m',
      ccfg_com ccfg = Cupdate e1 e2 ->
      estep (ccfg_to_ecfg e1 ccfg) (Vloc l) ->
      estep (ccfg_to_ecfg e2 ccfg) v ->
      is_Not_cnd l ->
      m' = ccfg_update_mem ccfg l v ->
      cstep ccfg (ccfg_reg ccfg, m') []
  | Cstep_output : forall e sl v,
      ccfg_com ccfg = Coutput e sl ->
      estep (ccfg_to_ecfg e ccfg) v ->
      sl = L \/ sl = H ->
      cstep ccfg (ccfg_reg ccfg, ccfg_mem ccfg) [Mem (ccfg_mem ccfg); Out sl v]
  | Cstep_call : forall e c r' m' tr,
      ccfg_com ccfg = Ccall e ->
      estep (ccfg_to_ecfg e ccfg) (Vlambda c) ->
      cstep (ccfg_update_com c ccfg) (r', m') tr ->
      cstep ccfg (r', m') tr
  | Cstep_cset : forall c m',
      ccfg_com ccfg = Cset c ->
      m' = ccfg_update_mem ccfg (Cnd c) (Vnat 1) ->
      cstep ccfg (ccfg_reg ccfg, m') [Mem m']
  | Cstep_seq_nil :
      ccfg_com ccfg = Cseq [] ->
      cstep ccfg (ccfg_reg ccfg, ccfg_mem ccfg) []
  | Cstep_seq_hd : forall hd tl r m tr r' m' tr',
      ccfg_com ccfg = Cseq (hd::tl) ->
      cstep (ccfg_update_com hd ccfg) (r, m) tr ->
      cstep (Cseq tl, r, m) (r', m') tr' ->
      cstep ccfg (r', m') (tr++tr')
  | Cstep_if : forall e c1 c2 v r' m' tr,
      ccfg_com ccfg = Cif e c1 c2 ->
      estep (ccfg_to_ecfg e ccfg) v ->
      ~(v = (Vnat 0)) ->
      cstep (ccfg_update_com c1 ccfg) (r', m') tr ->
      cstep ccfg (r', m') tr
  | Cstep_else : forall e c1 c2 v r' m' tr,
      ccfg_com ccfg = Cif e c1 c2 ->
      estep (ccfg_to_ecfg e ccfg) v ->
      v = (Vnat 0) ->
      cstep (ccfg_update_com c2 ccfg) (r', m') tr ->
      cstep ccfg (r', m') tr
  | Cstep_while_t : forall e c v r m tr r' m' tr',
      ccfg_com ccfg = Cwhile e c ->
      estep (ccfg_to_ecfg e ccfg) v ->
      ~(v = (Vnat 0)) ->
      cstep (ccfg_update_com c ccfg) (r, m) tr ->
      cstep (ccfg_update_com (Cwhile e c) ccfg) (r', m') tr' ->
      cstep ccfg (r', m') (tr++tr')
  | Cstep_while_f : forall e c,
      ccfg_com ccfg = Cwhile e c ->
      estep (ccfg_to_ecfg e ccfg) (Vnat 0) ->
      cstep ccfg (ccfg_reg ccfg, ccfg_mem ccfg) [].

End Semantics.
End ImpS.