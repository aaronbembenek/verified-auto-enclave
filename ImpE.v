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
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Sorting.Permutation.
Import ListNotations.
Require Import Common.

Module ImpE.

(*******************************************************************************
*
* SYNTAX
*
*******************************************************************************)

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

  Ltac auto_decide :=
    try match goal with
    | [x : nat, y : nat |- _] => destruct (Nat.eq_dec x y)
    | [x : var, y : var |- _] => destruct (Nat.eq_dec x y)
    | [x : condition, y : condition |- _] => destruct (Nat.eq_dec x y)
    | _ => idtac
    end; [left; now subst | right; congruence].

  Lemma exp_decidable : forall e1 e2 : exp, {e1 = e2} + {e1 <> e2}.
  Proof.
    Print exp_ind.
    intro; induction e1; destruct e2; try (right; discriminate).
    1-2: auto_decide.
    1-2: destruct IHe1_1 with (e2:=e2_1); destruct IHe1_2 with (e2:=e2_2); subst; auto;
      right; congruence.
    destruct l, l0; try (right; discriminate); auto_decide.
    destruct IHe1 with (e2:=e2); [left; now subst | right; congruence].
    auto_decide.
    (* Lambdas require that commands are decidable... :( *)
    Admitted.

  (*FIXME: Ezra needs to come back and figure out how to prove that expressions
    and commands are decidable. Is there a way to do a mutually recursive proof...?*)
  Lemma com_decidable : forall c1 c2 : com, {c1 = c2} + {c1 <> c2}.
  Admitted.
 
  Lemma prog_decidable : forall p1 p2 : (com + exp), {p1 = p2} + {p1 <> p2}.
  Proof.
    intros; destruct p1; destruct p2; try (right; discriminate).
    - destruct (com_decidable c c0). left; now subst. right; congruence.
    - destruct (exp_decidable e e0). left; now subst. right; congruence.
  Qed.

  Lemma mode_decidable : forall m1 m2 : mode, {m1 = m2} + {m1 <> m2}.
  Proof.
    intros; destruct m1; destruct m2; try (right; discriminate).
    - left; auto.
    - destruct (Nat.eq_dec e e0); [left; now subst | right; congruence].
  Qed.
  
  Lemma val_decidable : forall v1 v2 : val, {v1 = v2} + {v1 <> v2}.
  Proof.
    intros. destruct v1, v2; try (right; discriminate).
    - destruct (mode_decidable m m0); destruct (com_decidable c c0); subst;
        [left; auto | | |]; right; congruence.
    - auto_decide.
    - destruct l, l0; try (right; discriminate); auto_decide.
  Qed.

End Syntax.

(*******************************************************************************
*
* ENCLAVE EQUIVALENCE
*
*******************************************************************************)

Section Enclave_Equiv.
  Lemma mode_prog_decidable : forall ep1 ep2 : (mode * (com + exp)), {ep1 = ep2} + {ep1 <> ep2}.
  Proof.
    intros; destruct ep1, ep2; destruct (mode_decidable m m0); destruct (prog_decidable s s0).
    1: left; now subst.
    all: right; congruence.
  Qed.

  Fixpoint chi (c : com) : set (mode * (com + exp)) :=
  let chi_exp :=
      (fix chi_exp (e : exp) : set (mode * (com + exp)) :=
         match e with
         | Eplus e1 e2 | Emult e1 e2 => set_union mode_prog_decidable (chi_exp e1) (chi_exp e2)
         | Ederef e1 => chi_exp e1
         | Elambda Normal c => chi c
         | Elambda m _ => set_add mode_prog_decidable (m, inr e) nil
         | _ => nil
         end)
  
  in
  match c with
  | Cassign _ e => chi_exp e
  | Cdeclassify _ e => chi_exp e
  | Cupdate e1 e2 => set_union mode_prog_decidable (chi_exp e1) (chi_exp e2)
  | Coutput e _ => chi_exp e
  | Ccall e => chi_exp e
  | Cenclave enc c1 => set_add mode_prog_decidable (Encl enc, inl c1) nil
  | Cseq c_lst => fold_left (fun acc elt => set_union mode_prog_decidable (chi elt) acc) c_lst nil
  | Cif e c1 c2 => set_union mode_prog_decidable (chi_exp e)
                            (set_union mode_prog_decidable (chi c1) (chi c2))
  | _ => nil
  end.

  Definition enc_equiv (c1 c2 : com) : Prop := chi c1 = chi c2.

End Enclave_Equiv.

(*******************************************************************************
*
* SEMANTICS
*
*******************************************************************************)

Section Semantics.
  Definition reg : Type := register val.
  Definition reg_init : reg := fun x => Vnat 0.
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
  (* XXX I think we need to define semantics for expressions as well for all attackers? *)
  Definition esemantics : Type := mode -> loc_mode -> econfig -> val -> Prop.
  
  Inductive estep : esemantics :=
  | Estep_nat : forall md d ecfg n, ecfg_exp ecfg = Enat n -> estep md d ecfg (Vnat n)
  | Estep_loc : forall md d ecfg l, ecfg_exp ecfg = Eloc l -> estep md d ecfg (Vloc l)
  | Estep_lambda : forall md d ecfg c,
      ecfg_exp ecfg = Elambda md c -> estep md d ecfg (Vlambda md c)
  | Estep_var : forall md d ecfg x v,
      ecfg_exp ecfg = Evar x -> ecfg_reg ecfg x = v -> estep md d ecfg v
  | Estep_plus : forall md d ecfg e1 e2 n1 n2,
      ecfg_exp ecfg = Eplus e1 e2 ->
      estep md d (ecfg_update_exp ecfg e1) (Vnat n1) ->
      estep md d (ecfg_update_exp ecfg e2) (Vnat n2) ->
      estep md d ecfg (Vnat (n1 + n2))
  | Estep_mult : forall md d ecfg e1 e2 n1 n2,
      ecfg_exp ecfg = Emult e1 e2 ->
      estep md d (ecfg_update_exp ecfg e1) (Vnat n1) ->
      estep md d (ecfg_update_exp ecfg e2) (Vnat n2) ->
      estep md d ecfg (Vnat (n1 * n2))
  | Estep_deref : forall md d ecfg e r m k l v,
      ecfg = (Ederef e, r, m, k) ->
      estep md d (e, r, m, k) (Vloc l) ->
      m l = v ->
      mode_access_ok md d l k ->
      estep md d ecfg v
  | Estep_isunset : forall md d ecfg cnd v res,
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
  Definition ccfg_to_ecfg (e: exp) (ccfg : cconfig) : econfig :=
    (e, (ccfg_reg ccfg), (ccfg_mem ccfg), (ccfg_kill ccfg)).
  Definition ccfg_update_com (c: com) (ccfg : cconfig) : cconfig :=
    (c, (ccfg_reg ccfg), (ccfg_mem ccfg), (ccfg_kill ccfg)).
  Definition csemantics : Type := mode -> loc_mode -> cconfig -> cterm -> trace -> Prop.  

  (* XXX couldn't figure out a way to not have to introduce forall md d ccfg everywhere.. *)
  Inductive cstep : csemantics := 
  | Cstep_skip : forall md d ccfg, cstep md d ccfg (ccfg_reg ccfg, ccfg_mem ccfg, ccfg_kill ccfg) []
  | Cstep_assign : forall md d ccfg x e v r',
      ccfg_com ccfg = Cassign x e ->
      estep md d (ccfg_to_ecfg e ccfg) v ->
      r' = ccfg_update_reg ccfg x v ->
      mode_alive md (ccfg_kill ccfg) ->
      cstep md d ccfg (r', ccfg_mem ccfg, ccfg_kill ccfg) []
  | Cstep_declassify : forall md d ccfg x e v r',
      ccfg_com ccfg = Cdeclassify x e ->
      exp_novars e ->
      estep md d (ccfg_to_ecfg e ccfg) v ->
      r' = ccfg_update_reg ccfg x v ->
      mode_alive md (ccfg_kill ccfg) ->
      cstep md d ccfg (r', ccfg_mem ccfg, ccfg_kill ccfg) [Decl e (ccfg_mem ccfg)]
  | Cstep_update : forall md d ccfg e1 e2 l v m',
      ccfg_com ccfg = Cupdate e1 e2 ->
      estep md d (ccfg_to_ecfg e1 ccfg) (Vloc l) ->
      estep md d (ccfg_to_ecfg e2 ccfg) v ->
      mode_alive md (ccfg_kill ccfg) ->
      mode_access_ok md d l (ccfg_kill ccfg) ->
      is_Not_cnd l ->
      m' = ccfg_update_mem ccfg l v ->
      cstep md d ccfg (ccfg_reg ccfg, m', ccfg_kill ccfg) []
  | Cstep_output : forall md d ccfg e sl v,
      ccfg_com ccfg = Coutput e sl ->
      estep md d (ccfg_to_ecfg e ccfg) v ->
      sl = L \/ sl = H ->
      mode_alive md (ccfg_kill ccfg) ->
      cstep md d ccfg (ccfg_reg ccfg, ccfg_mem ccfg, ccfg_kill ccfg) [Mem (ccfg_mem ccfg); Out sl v]
  | Cstep_call : forall md d ccfg e c r' m' k' tr,
      ccfg_com ccfg = Ccall e ->
      estep md d (ccfg_to_ecfg e ccfg) (Vlambda md c) ->
      cstep md d (ccfg_update_com c ccfg) (r', m', k') tr ->
      cstep md d ccfg (r', m', k') tr
  | Cstep_cset : forall md d ccfg c m',
      ccfg_com ccfg = Cset c ->
      mode_access_ok md d (Cnd c) (ccfg_kill ccfg) ->
      m' = ccfg_update_mem ccfg (Cnd c) (Vnat 1) ->
      mode_alive md (ccfg_kill ccfg) ->
      cstep md d ccfg (ccfg_reg ccfg, m', ccfg_kill ccfg) [Mem m']
  | Cstep_enclave : forall md d ccfg enc c r' m' k' tr,
    md = Normal ->
    ccfg_com ccfg = Cenclave enc c ->
    cstep (Encl enc) d (c, ccfg_reg ccfg, ccfg_mem ccfg, ccfg_kill ccfg) (r', m', k') tr ->
    cstep md d ccfg (r', m', k') tr
  | Cstep_seq_nil : forall md d ccfg,
      ccfg_com ccfg = Cseq [] ->
      cstep md d ccfg (ccfg_reg ccfg, ccfg_mem ccfg, ccfg_kill ccfg) []
  | Cstep_seq_hd : forall md d ccfg hd tl r m k tr r' m' k' tr',
      ccfg_com ccfg = Cseq (hd::tl) ->
      cstep md d (ccfg_update_com hd ccfg) (r, m, k) tr ->
      cstep md d (Cseq tl, r, m, k) (r', m', k') tr' ->
      cstep md d ccfg (r', m', k') (tr++tr')
  | Cstep_if : forall md d ccfg e c1 c2 v r' m' k' tr,
      ccfg_com ccfg = Cif e c1 c2 ->
      estep md d (ccfg_to_ecfg e ccfg) v ->
      ~(v = (Vnat 0)) ->
      cstep md d (ccfg_update_com c1 ccfg) (r', m', k') tr ->
      cstep md d ccfg (r', m', k') tr
  | Cstep_else : forall md d ccfg e c1 c2 v r' m' k' tr,
      ccfg_com ccfg = Cif e c1 c2 ->
      estep md d (ccfg_to_ecfg e ccfg) v ->
      v = (Vnat 0) ->
      cstep md d (ccfg_update_com c2 ccfg) (r', m', k') tr ->
      cstep md d ccfg (r', m', k') tr
  | Cstep_while_t : forall md d ccfg e c v r m k tr r' m' k' tr',
      ccfg_com ccfg = Cwhile e c ->
      estep md d (ccfg_to_ecfg e ccfg) v ->
      ~(v = (Vnat 0)) ->
      cstep md d (ccfg_update_com c ccfg) (r, m, k) tr ->
      cstep md d (ccfg_update_com (Cwhile e c) ccfg) (r', m', k') tr' ->
      cstep md d ccfg (r', m', k') (tr++tr')
  | Cstep_while_f : forall md d ccfg e c,
      ccfg_com ccfg = Cwhile e c ->
      estep md d (ccfg_to_ecfg e ccfg) (Vnat 0) ->
      mode_alive md (ccfg_kill ccfg) ->
      cstep md d ccfg (ccfg_reg ccfg, ccfg_mem ccfg, ccfg_kill ccfg) []
  | Cstep_kill : forall md d ccfg enc,
      md = Normal ->
      ccfg_com ccfg = Ckill enc ->
      mode_alive (Encl enc) (ccfg_kill ccfg) ->
      cstep md d ccfg (ccfg_reg ccfg, ccfg_mem ccfg, set_add Nat.eq_dec enc (ccfg_kill ccfg)) [].
End Semantics.

(*******************************************************************************
*
* TYPING
*
*******************************************************************************)

Section Typing.
  Inductive ref_type : Set :=
  | Mut
  | Immut.

  (* FIXME: we might want to change contexts to be defined in terms of
     finite maps instead of functions. *)
  Inductive base_type : Type :=
  | Tnat : base_type
  | Tcond : mode -> base_type
  | Tref : type -> mode -> ref_type -> base_type
  | Tlambda (g: context) (k:set enclave) (u:set condition) (p: sec_policy)
            (md: mode) (g': context) (k':set enclave) : base_type
                           
  with type : Type :=
  | Typ : base_type -> sec_policy -> type
                                            
  with context : Type :=
  | Cntxt (var_cntxt: var -> option type)
          (loc_cntxt: location -> option (type * ref_type)) : context.

  Definition var_context (g: context) : var -> option type :=
    match g with Cntxt vc _ => vc end.
  Definition loc_context (g: context) : location -> option (type * ref_type) :=
    match g with Cntxt _ lc => lc end.

  (* FIXME: define this *)
  Variable all_loc_immutable : exp -> Prop.
  
  Inductive exp_type : mode -> context -> loc_mode -> exp -> type -> Prop :=
  | ETnat : forall md g d e n,
      e = Enat n ->
      exp_type md g d e (Typ Tnat (LevelP L))
  | ETvar : forall md g d e x t,
      e = Evar x ->
      var_context g x = Some t -> exp_type md g d e t
  | ETcnd : forall md g d e a md',
      let l := Cnd a in
      e = Eloc l ->
      d l = md' ->
      exp_type md g d e (Typ (Tcond md') (LevelP L))
  | ETloc : forall md g d e a md' t rt,
      let l := Not_cnd a in
      e = Eloc l ->
      d l = md' ->
      loc_context g l = Some (t, rt) ->
      exp_type md g d e (Typ (Tref t md' rt) (LevelP L))
  | ETderef : forall md g d e e' md' s p rt q,
      e = Ederef e' ->
      exp_type md g d e' (Typ (Tref (Typ s p) md' rt) q) ->
      md' = Normal \/ md' = md ->
      exp_type md g d e (Typ s (policy_join p q))
  | ETunset : forall md g d e cnd md',
      e = Eisunset cnd ->
      md' = d (Cnd cnd) ->
      md' = Normal \/ md' = md ->
      exp_type md g d e (Typ Tnat (LevelP L))
  | ETlambda : forall md g d e c p k u g' k',
      e = Elambda md c ->
      com_type p md g k u d c g' k' ->
      exp_type md g d e (Typ (Tlambda g k u p md g' k') (LevelP L))
  | ETplus : forall md g d e e1 e2 p q,
      e = Eplus e1 e2 ->
      exp_type md g d e1 (Typ Tnat p) ->
      exp_type md g d e2 (Typ Tnat q) ->
      exp_type md g d e (Typ Tnat (policy_join p q))
  | ETmult : forall md g d e e1 e2 p q,
      e = Emult e1 e2 ->
      exp_type md g d e1 (Typ Tnat p) ->
      exp_type md g d e2 (Typ Tnat q) ->
      exp_type md g d e (Typ Tnat (policy_join p q))

  with com_type : sec_policy -> mode -> context -> set enclave ->
                  set condition -> loc_mode -> com ->
                  context -> set enclave -> Prop :=
  | CTskip : forall c pc md g d k u,
      c = Cskip ->
      mode_alive md k ->
      com_type pc md g k u d c g k
  | CTkill : forall c i g d k u,
      c = Ckill i ->
      mode_alive (Encl i) k ->
      com_type (LevelP L) Normal g k u d c g (set_add Nat.eq_dec i k)
  | CTassign : forall pc md g k u d c x e s p q vc lc vc',
      c = Cassign x e ->
      exp_type md g d e (Typ s p) ->
      q = policy_join p pc ->
      q <> LevelP T ->
      policy_le q (LevelP L) \/ md <> Normal ->
      mode_alive md k ->
      g = Cntxt vc lc ->
      vc' = (fun y => if y =? x then Some (Typ s q) else vc y) ->
      com_type pc md g k u d c (Cntxt vc' lc) k
  | CTdeclassify : forall md g k u d c x e s p vc lc vc',
      c = Cdeclassify x e ->
      exp_type md g d e (Typ s p) ->
      p <> LevelP T ->
      mode_alive md k ->
      exp_novars e ->
      all_loc_immutable e ->
      vc' = (fun y => if y =? x then Some (Typ s (LevelP L)) else vc y) ->
      com_type (LevelP L) md g k u d c (Cntxt vc' lc) k
  | CToutput : forall pc md g k u d c e l s p,
      c = Coutput e l ->
      exp_type md g d e (Typ s p) ->
      mode_alive md k ->
      p <> LevelP T ->
      sec_level_le (sec_level_join (cur p u) (cur pc u)) l ->
      com_type pc md g k u d c g k.
  
End Typing.


(*******************************************************************************
*
* SECURITY
*
*******************************************************************************)

Section Security.
  Definition esc_hatch : Type := exp.
          
  Inductive attacker : Type :=
  | passive : attacker
  | active_nonencl : attacker
  | active_encl : attacker.

  Definition tobs_sec_level (sl: sec_level) (t: trace) : trace :=
    filter (fun event => match event with
                         | Out sl' v => if (sec_level_le_dec sl' sl) then true else false
                         | _ => false                           
                         end)
           t.
  
  (* XXX definition doesn't have a delta, so I'm assuming delta is just fixed (and quantifying over it) *)
  Inductive knowledge_attack (c : com) (sl : sec_level) (cstep : csemantics) (tobs : trace)
    : mem -> Prop :=
  | known_mem : forall d m r' m' k' t t0 t1 t2,
      cstep Normal d (c, reg_init, m, []) (r', m', k') t ->
      t = t0 ++ t1 ++ t2 ->
      tobs_sec_level sl tobs = tobs_sec_level sl t1 ->
      knowledge_attack c sl cstep tobs m.

  (* XXX need to enforce that all U are unset? *)
  Inductive knowledge_ind (m: mem) (g: sec_spec) (U: set condition) (sl : sec_level) :
    mem -> Prop :=
  | ind_mem : forall m' l,
      sec_level_le (cur (g l) U) sl ->
      m l = m' l ->
      knowledge_ind m g U sl m'.

  (* XXX check that quantifying over all mds is ok. I think it is... as long as one md exists
     s.t. the conditions hold, m' is an esc_mem *)
  Inductive knowledge_esc (m0 m: mem) (estep: esemantics) (e: esc_hatch) :
    mem -> Prop :=
  | esc_mem : forall m' d v md,
      estep md d (e, reg_init, m0, []) v ->
      estep md d (e, reg_init, m, []) v ->
      estep md d (e, reg_init, m', []) v ->
      knowledge_esc m0 m estep e m'.

  Definition cnd_unset (m: mem) (cnd: condition) : Prop := m (Cnd cnd) = Vnat 0.
  Definition cnd_set (m: mem) (cnd: condition) : Prop := m (Cnd cnd) = Vnat 1.
                
  (* XXX This thing with e and csemantics is a little weird. Probably want to
     define one that encapsulates both, but I'm not sure how...
   *)
  Inductive secure_prog (sl: sec_level) (g: sec_spec) (cstep: csemantics) (estep: esemantics) :
    com -> Prop :=
  | secure : forall c tobs mhead t''
                      m0 d thd ttl cterm
                      tobs_hd tobs_tl mind cnd U mknown
                      ttobs_hd ttobs_tl mdecl e,
      (* begin with memory event *)
      tobs = Mem mhead :: t'' ->
      cstep Normal d (c, reg_init, m0, []) cterm (thd ++ tobs ++ ttl) ->
      (* intersection over [tobs]_mem all memories in ind_sl with no set conditions *)
      tobs = tobs_hd ++ [Mem mind] ++ tobs_tl ->
      cnd_set mind cnd -> ~In cnd U /\ cnd_unset mind cnd -> In cnd U ->
      knowledge_ind m0 g U sl mknown ->
      (* intersection over [tobs]_esc *)
      thd ++ tobs = ttobs_hd ++ [Decl e mdecl] ++ ttobs_tl ->
      knowledge_esc m0 mdecl estep e mknown ->
      (* knowledge_attack has to include all the above, so whenever the above holds,
         so must knowledge_attack *)
      knowledge_attack c sl cstep tobs mknown ->
      secure_prog sl g cstep estep c.

End Security.
End ImpE.
