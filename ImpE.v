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
  | Ebinop : exp -> exp -> (nat -> nat -> nat) -> exp
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

  Inductive forall_subexp (P: exp -> Prop) : exp -> Prop :=
  | FAnat : forall n,
      P (Enat n) -> forall_subexp P (Enat n)
  | FAvar : forall x,
      P (Evar x) -> forall_subexp P (Evar x)
  | FAbinop : forall e1 e2 op,
      P (Ebinop e1 e2 op) ->
      forall_subexp P e1 ->
      forall_subexp P e2 ->
      forall_subexp P (Ebinop e1 e2 op)
  | FAloc : forall l,
      P (Eloc l) -> forall_subexp P (Eloc l)
  | FAderef : forall e,
      P (Ederef e) ->
      forall_subexp P e ->
      forall_subexp P (Ederef e)
  | FAisunset : forall cnd,
      P (Eisunset cnd) ->
      forall_subexp P (Eisunset cnd)
  | FAlambda : forall md c,
      P (Elambda md c) ->
      forall_subexp' P c ->
      forall_subexp P (Elambda md c)

  with forall_subexp' (P: exp -> Prop) : com -> Prop :=
  | FAskip :
      forall_subexp' P Cskip
  | FAassign : forall x e,
      forall_subexp P e ->
      forall_subexp' P (Cassign x e)
  | FAdeclassify : forall x e,
      forall_subexp P e ->
      forall_subexp' P (Cdeclassify x e)
  | FAupdate : forall e1 e2,
      forall_subexp P e1 ->
      forall_subexp P e2 ->
      forall_subexp' P (Cupdate e1 e2)
  | FAoutput : forall e sl,
      forall_subexp P e ->
      forall_subexp' P (Coutput e sl)
  | FAcall : forall e,
      forall_subexp P e ->
      forall_subexp' P (Ccall e)
  | FAset : forall cnd,
      forall_subexp' P (Cset cnd)
  | FAif : forall e c1 c2,
      forall_subexp P e ->
      forall_subexp' P c1 ->
      forall_subexp' P c2 ->
      forall_subexp' P (Cif e c1 c2)
  | FAwhile : forall e c,
      forall_subexp P e ->
      forall_subexp' P c ->
      forall_subexp' P (Cwhile e c)
  | FAseq : forall coms,
      Forall (fun c => forall_subexp' P c) coms ->
      forall_subexp' P (Cseq coms)
  | FAenclave : forall i c,
      forall_subexp' P c ->
      forall_subexp' P (Cenclave i c)
  | FAkill : forall i,
      forall_subexp' P (Ckill i).

  Definition exp_novars : exp -> Prop :=
    forall_subexp (fun e => match e with
                            | Evar _ => False
                            | _ => True
                            end).

   Ltac auto_decide :=
    try match goal with
    | [x : nat, y : nat |- _] => destruct (Nat.eq_dec x y)
    | [x : var, y : var |- _] => destruct (Nat.eq_dec x y)
    | [x : condition, y : condition |- _] => destruct (Nat.eq_dec x y)
    | _ => idtac
    end; [left; now subst | right; congruence].

  Lemma exp_decidable : forall e1 e2 : exp, {e1 = e2} + {e1 <> e2}.
  Proof. (*
    Print exp_ind.
    intro; induction e1; destruct e2; try (right; discriminate).
    1-2: auto_decide.
    1-2: destruct IHe1_1 with (e2:=e2_1); destruct IHe1_2 with (e2:=e2_2); subst; auto;
      right; congruence.
    destruct l, l0; try (right; discriminate); auto_decide.
    destruct IHe1 with (e2:=e2); [left; now subst | right; congruence].
    auto_decide.
    (* Lambdas require that commands are decidable... :( *)*)
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
         | Ebinop e1 e2 _ => set_union mode_prog_decidable (chi_exp e1) (chi_exp e2)
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

  Definition enc_equiv (c1 c2 : com) := chi c1 = chi c2 -> Prop.

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

  Inductive event : Type :=
  | Decl : exp -> mem -> event
  | Mem : mem -> event
  | Out : sec_level -> val -> event
  | ANonEnc : com -> event
  | AEnc : forall c c' : com, enc_equiv c c'-> event
  | Emp: event.
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
  | Estep_nat : forall md d ecfg n,
      ecfg_exp ecfg = Enat n ->
      estep md d ecfg (Vnat n)
  | Estep_loc : forall md d ecfg l,
      ecfg_exp ecfg = Eloc l ->
      estep md d ecfg (Vloc l)
  | Estep_lambda : forall md d ecfg c,
      ecfg_exp ecfg = Elambda md c ->
      estep md d ecfg (Vlambda md c)
  | Estep_var : forall md d ecfg x v,
      ecfg_exp ecfg = Evar x ->
      ecfg_reg ecfg x = v ->
      estep md d ecfg v
  | Estep_binop : forall md d ecfg e1 e2 op n1 n2,
      ecfg_exp ecfg = Ebinop e1 e2 op ->
      estep md d (ecfg_update_exp ecfg e1) (Vnat n1) ->
      estep md d (ecfg_update_exp ecfg e2) (Vnat n2) ->
      estep md d ecfg (Vnat (op n1 n2))
  | Estep_deref : forall md d ecfg e r m k l v,
      ecfg = (Ederef e, r, m, k) ->
      estep md d (e, r, m, k) (Vloc l) ->
      m l = v ->
      mode_access_ok md d l k ->
      estep md d ecfg v
  | Estep_isunset : forall md d ecfg cnd v res,
      ecfg_exp ecfg = Eisunset cnd ->
      estep md d (ecfg_update_exp ecfg (Ederef (Eloc (Cnd cnd)))) v ->
      (v = Vnat 0 /\ res = Vnat 1) \/ (v = Vnat 1 /\ res = Vnat 0) ->
      estep md d ecfg res.
  Hint Constructors estep.

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
  | Cstep_seq_hd : forall md d ccfg hd tl r m k tr r' m' k' tr' t,
      ccfg_com ccfg = Cseq (hd::tl) ->
      cstep md d (ccfg_update_com hd ccfg) (r, m, k) tr ->
      cstep md d (Cseq tl, r, m, k) (r', m', k') tr' ->
      t = tr ++ tr' ->
      cstep md d ccfg (r', m', k') t
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
  Hint Constructors cstep.

  Inductive cstep_n_chaos : csemantics :=
  | Nchaos_cstep : forall md d ccfg cterm t,
      cstep md d ccfg cterm t -> cstep_n_chaos md d ccfg cterm t
  | Nchaos_chaos : forall d ccfg cterm c' t' (HEncEq : enc_equiv (ccfg_com ccfg) c'),
      cstep Normal d (c', ccfg_reg ccfg, ccfg_mem ccfg, ccfg_kill ccfg) cterm t' ->
      cstep_n_chaos Normal d ccfg cterm
                    (Mem (ccfg_mem ccfg) :: AEnc (ccfg_com ccfg) c' HEncEq :: t').

  Inductive cstep_e_chaos : set enclave -> csemantics :=
  | Echaos_cstep : forall I md d ccfg cterm t,
      cstep md d ccfg cterm t -> cstep_e_chaos I md d ccfg cterm t
  | Echaos_chaos : forall I d ccfg cterm c' t',
      (* XXX: is there really no built-in subset definition? *)
      (forall e, set_In e I -> set_In e (ccfg_kill ccfg)) ->
      cstep Normal d (c', ccfg_reg ccfg, ccfg_mem ccfg, ccfg_kill ccfg) cterm t' ->
      cstep_e_chaos I Normal d ccfg cterm
                    (Mem (ccfg_mem ccfg) :: ANonEnc c' :: t').
End Semantics.

(*******************************************************************************
*
* TYPING
*
*******************************************************************************)

Section Typing.
  (* FIXME: we might want to change contexts to be defined in terms of
     finite maps instead of functions. *)
  Inductive base_type : Type :=
  | Tnat : base_type
  | Tcond : mode -> base_type
  | Tref : type -> mode -> ref_type -> base_type
  | Tlambda (G: context) (k:set enclave) (u:set condition) (p: policy)
            (md: mode) (G': context) (k':set enclave) : base_type
                           
  with type : Type :=
  | Typ : base_type -> policy -> type
                                            
  with context : Type :=
  | Cntxt (var_cntxt: var -> option type)
          (loc_cntxt: location -> option (type * ref_type)) : context.
                                      
  Definition var_context (G: context) : var -> option type :=
    match G with Cntxt vc _ => vc end.
  
  Definition loc_context (G: context) : location -> option (type * ref_type) :=
    match G with Cntxt _ lc => lc end.

  Inductive var_in_dom (G: context) : var -> type -> Prop :=
  | Var_in_dom : forall x t,
      var_context G x = Some t ->
      var_in_dom G x t.

  Inductive loc_in_dom (G: context) : location -> type -> ref_type -> Prop :=
  | Loc_in_dom : forall l t rt,
      loc_context G l = Some (t, rt) ->
      loc_in_dom G l t rt.

  Definition forall_var (G: context) (P: var -> type -> Prop) : Prop :=
    forall x t, var_in_dom G x t -> P x t.

  Definition forall_loc (G: context)
             (P: location -> type -> ref_type -> Prop) : Prop :=
    forall l t rt,
      loc_in_dom G l t rt -> P l t rt.

  Definition forall_dom (G: context)
             (P: var -> type -> Prop)
             (Q: location -> type -> ref_type -> Prop) : Prop :=
    forall_var G P /\ forall_loc G Q.

  Inductive type_le : type -> type -> Prop :=
  | Type_le : forall s1 s2 p1 p2,
      base_type_le s1 s2 ->
      policy_le p1 p2 ->
      type_le (Typ s1 p1) (Typ s2 p2)

  with base_type_le : base_type -> base_type -> Prop :=
  | Base_type_le_refl : forall s, base_type_le s s
  | Base_type_le_lambda : forall G1 G1' G2 G2' k u p1 p2 md k',
      policy_le p2 p1 ->
      context_le G2 G1 ->
      context_le G1' G2' ->
      base_type_le (Tlambda G1 k u p1 md G1' k')
                   (Tlambda G2 k u p2 md G2' k')

  with context_le : context -> context -> Prop :=
  | Context_le : forall G1 G2,
      (forall x t,
          var_in_dom G1 x t -> exists t',
            var_in_dom G2 x t' /\ type_le t t') ->
      (forall x t,
          var_in_dom G2 x t -> exists t', var_in_dom G1 x t') ->
      (forall l t rt,
          loc_in_dom G1 l t rt -> exists t',
            loc_in_dom G2 l t' rt /\ type_le t t') ->
      (forall l t rt,
          loc_in_dom G2 l t rt -> exists t', loc_in_dom G1 l t' rt) ->
      context_le G1 G2.

  Definition context_wt (G: context) (d: loc_mode) : Prop :=
    forall_loc G (fun l t _ =>
                    let (_, p) := t in
                    forall p0,
                      pdenote p p0 ->
                      policy0_le p0 (LevelP L) \/
                      (p0 <> (LevelP T) /\ exists i, d l = Encl i)) /\
    forall_var G (fun x t =>
                    let (_, p) := t in
                    forall p0,
                      pdenote p p0 -> p0 <> LevelP T).
  
  Definition is_var_low_context (G: context) : Prop :=
    forall_var G (fun _ t => let (_, p) := t in
                             forall p0,
                               pdenote p p0 ->
                               p0 = LevelP L).

  Definition all_loc_immutable (e: exp) (G: context) : Prop :=
    forall_subexp (fun e =>
                     match e with
                     | Eloc (Cnd _) => False
                     | Eloc (Not_cnd l) => forall t rt,
                         loc_context G (Not_cnd l) = Some (t, rt) ->
                         rt = Immut
                     | Eisunset _ => False
                     | _ => True
                     end) e.

  Definition loc_in_exp (e: exp) (G: context) (l: location) : Prop :=
    forall_subexp (fun e =>
                     match e with
                     | Eloc l => True
                     | _ => False
                     end) e.

  (* XXX need this for using List.nth... maybe better option *)
  Definition mt := Cntxt (fun _ => None) (fun _ => None).
  
  (* FIXME: don't have subsumption rule *)
  Inductive exp_type : mode -> context -> loc_mode -> exp -> type -> Prop :=
  | ETnat : forall md g d n,
      exp_type md g d (Enat n) (Typ Tnat low)
  | ETvar : forall md g d x t,
      var_context g x = Some t -> exp_type md g d (Evar x) t
  | ETcnd : forall md g d a md',
      let l := Cnd a in
      d l = md' ->
      exp_type md g d (Eloc l) (Typ (Tcond md') low)
  | ETloc : forall md g d a md' t rt,
      let l := Not_cnd a in
      d l = md' ->
      loc_context g l = Some (t, rt) ->
      exp_type md g d (Eloc l) (Typ (Tref t md' rt) low)
  | ETderef : forall md g d e md' s p q rt,
      exp_type md g d e (Typ (Tref (Typ s p) md' rt) q) ->
      md' = Normal \/ md = md' ->
      exp_type md g d (Ederef e) (Typ s (JoinP p q))
  | ETunset : forall md g d cnd md',
      md' = d (Cnd cnd) ->
      md' = Normal \/ md = md' ->
      exp_type md g d (Eisunset cnd) (Typ Tnat low)
  | ETlambda : forall md g d c p k u g' g'' k',
      com_type p md g' k u d c g'' k' ->
      exp_type md g d (Elambda md c)
               (Typ (Tlambda g' k u p md g'' k') low)
  | ETbinop : forall md g d e1 e2 p q op,
      exp_type md g d e1 (Typ Tnat p) ->
      exp_type md g d e2 (Typ Tnat q) ->
      exp_type md g d (Ebinop e1 e2 op) (Typ Tnat (JoinP p q))

  with com_type : policy -> mode -> context -> set enclave ->
                  set condition -> loc_mode -> com ->
                  context -> set enclave -> Prop :=
  | CTskip : forall pc md g d k u,
      mode_alive md k ->
      com_type pc md g k u d Cskip g k
  | CTkill : forall i g d k u k',
      mode_alive (Encl i) k ->
      k' = set_add Nat.eq_dec i k ->
      com_type low Normal g k u d (Ckill i) g k'
  | CTassign : forall pc md g k u d x e s p vc lc vc' g',
      exp_type md g d e (Typ s p) ->
      ~pdenote (JoinP pc p) (LevelP T) ->
      policy_le (JoinP pc p) low \/ md <> Normal ->
      mode_alive md k ->
      g = Cntxt vc lc ->
      vc' = update vc x (Some (Typ s (JoinP pc p))) ->
      g' = Cntxt vc' lc ->
      com_type pc md g k u d (Cassign x e) g' k
  | CTdeclassify : forall md g k u d x e s p vc lc vc',
      exp_type md g d e (Typ s p) ->
      ~pdenote p (LevelP T) ->
      mode_alive md k ->
      exp_novars e ->
      all_loc_immutable e g ->
      vc' = update vc x (Some (Typ s low)) ->
      com_type low md g k u d (Cdeclassify x e) (Cntxt vc' lc) k
  | CTupdate : forall pc md g k u d e1 e2 s p md' q p',
      exp_type md g d e1 (Typ (Tref (Typ s p) md' Mut) q) ->
      exp_type md g d e2 (Typ s p') ->
      policy_le (JoinP (JoinP p' q) pc) p ->
      md' = Normal \/ md = md' ->
      mode_alive md k ->
      ~pdenote p (LevelP T) ->
      ~pdenote p' (LevelP T) ->
      ~pdenote q (LevelP T) ->
      com_type pc md g k u d (Cupdate e1 e2) g k
  | CToutput : forall pc md g k u d e l s p p0 pc0,
      exp_type md g d e (Typ s p) ->
      mode_alive md k ->
      ~pdenote p (LevelP T) ->
      pdenote p p0 ->
      pdenote pc pc0 ->
      sec_level_le (sec_level_join (cur p0 u) (cur pc0 u)) l ->
      com_type pc md g k u d (Coutput e l) g k
  | CTset : forall md g k u d cnd md',
      md' = d (Cnd cnd) ->
      ~set_In cnd u ->
      md' = Normal \/ md = md' ->
      mode_alive md k ->
      com_type low md g k u d (Cset cnd) g k
  | CTifunset : forall pc md g k u d cnd c1 c2 g' k',
      exp_type md g d (Eisunset cnd) (Typ Tnat low) ->
      com_type pc md g k (set_add Nat.eq_dec cnd u) d c1 g' k' ->
      com_type pc md g k u d c2 g' k' ->
      com_type pc md g k u d (Cif (Eisunset cnd) c1 c2) g' k'
  | CTifelse : forall pc md g k u d e c1 c2 pc' p g' k',
      com_type pc' md g k u d c1 g' k' ->
      com_type pc' md g k u d c2 g' k' ->
      exp_type md g d e (Typ Tnat p) ->
      policy_le (JoinP pc p) pc' ->
      policy_le p low \/ md <> Normal ->
      ~pdenote p (LevelP T) ->
      com_type pc md g k u d (Cif e c1 c2) g' k' 
  | CTenclave : forall pc g k u d i c' g' k',
      com_type pc (Encl i) g k nil d c' g' k' ->
      is_var_low_context g' ->
      com_type pc Normal g k u d (Cenclave i c') g' k'
  .
               (*
  | CTwhile : forall pc md g k u d c e p pc',
      exp_type md g d e (Typ Tnat p) ->
      com_type pc' md g k u d c g k ->
      policy_le (policy_join pc p) pc' ->
      policy_le p (LevelP L) \/ md <> Normal ->
      p <> LevelP T ->
      com_type pc md g k u d (Cwhile e c) g k
  | CTseq : forall pc md G K U d coms Gs Ks G' K',
      length Gs = length coms + 1 ->
      length Ks = length coms + 1 ->
      nth 0 Ks [] = K ->
      nth 0 Gs mt = G ->
      (forall (i: nat),
          i < length coms ->
          com_type pc md (nth i Gs mt) (nth i Ks []) U d (nth i coms Cskip)
                   (nth (i + 1) Gs mt) (nth (i + 1) Ks [])) ->
      G' = nth (length coms) Gs mt ->
      K' = nth (length coms) Ks [] ->
      com_type pc md G K U d (Cseq coms) G' K'
  | CTcall : forall pc md G u d e Gm km Gp kp Gout q p,
      exp_type md G d e (Typ (Tlambda Gm km u p md Gp kp) q) ->
      policy_le (policy_join pc q) p ->
      q <> LevelP T ->
      u = nil \/ md <> Normal ->
      forall_dom Gm
                 (fun x t => exists t', var_in_dom G x t' /\ type_le t' t)
                 (fun l t rt => exists t',
                      loc_in_dom G l t' rt /\ type_le t' t) ->
      forall_dom Gp
                 (fun x t => exists t', var_in_dom Gout x t' /\ type_le t' t)
                 (fun l t rt => exists t',
                      loc_in_dom Gout l t' rt /\ type_le t' t) ->
      forall_dom G
                 (fun x t =>
                    (forall t', ~var_in_dom Gp x t') ->
                    var_in_dom Gout x t)
                 (fun l t rt =>
                    (forall t' rt', ~loc_in_dom Gp l t' rt') ->
                    loc_in_dom Gout l t rt) ->
      com_type pc md G km u d (Ccall e) Gout kp.
  Hint Constructors exp_type com_type.
  *)
End Typing.
(*

(*******************************************************************************
*
* SECURITY
*
*******************************************************************************)

Section Security.
  Definition esc_hatch : Type := exp.
  
  Definition tobs_sec_level (sl: sec_level) : trace -> trace :=
    filter (fun event => match event with
                         | Out sl' v => sec_level_le_compute sl' sl
                         | AEnc c c' enc_equiv => true
                         | ANonEnc c => true
                         | _ => false                           
                         end).
   
  (* XXX I think it might be easier to use definitions instead of inductive
     types (don't get the error about not being able to find an instance
     for all the quantified variables *)
  Definition knowledge_attack (c: com) (sl: sec_level) (cstep: csemantics)
             (tobs: trace) (m: mem) : Prop :=
    forall d r' m' k' t t0 t1 t2,
      cstep Normal d (c, reg_init, m, []) (r', m', k') t ->
      t = t0 ++ t1 ++ t2 ->
      tobs_sec_level sl tobs = tobs_sec_level sl t1.

  (* XXX need to enforce that all U are unset? *)
  Definition knowledge_ind (m: mem) (g: sec_spec) (U: set condition)
             (sl: sec_level) (m': mem) : Prop :=
    forall l, sec_level_le (cur (g l) U) sl -> m l = m' l.

  Definition knowledge_esc (m0 m: mem) (estep: esemantics) (e: esc_hatch)
             (m': mem) : Prop :=
    exists md, forall d v,
        estep md d (e, reg_init, m0, []) v /\
        estep md d (e, reg_init, m, []) v ->
        estep md d (e, reg_init, m', []) v.

  Definition cnd_unset (m: mem) (cnd: condition) : Prop := m (Cnd cnd) = Vnat 0.
  Definition cnd_set (m: mem) (cnd: condition) : Prop := m (Cnd cnd) = Vnat 1.
                
  (* XXX This thing with e and csemantics is a little weird. Probably want to
     define one that encapsulates both, but I'm not sure how...
   *)
  Definition secure_prog (sl: sec_level) (g: sec_spec)
             (cstep: csemantics) (estep: esemantics) (c: com) : Prop :=
    forall m0 r m k d t tobs t' mknown,
      cstep Normal d (c, reg_init, m0, []) (r, m, k) (t ++ tobs ++ t') ->
      (exists m'' t'', tobs = Mem m'' :: t'') ->
      (forall mind U,
          In (Mem mind) tobs ->
          (forall cnd, cnd_unset mind cnd <-> In cnd U) ->
          knowledge_ind m0 g U sl mknown) ->
      (forall mdecl e,
          In (Decl e mdecl) (t ++ tobs) ->
          knowledge_esc m0 mdecl estep e mknown) ->
      knowledge_attack c sl cstep tobs mknown.
End Security.

Section Guarantees.

  Definition corresponds (G: context) (g: sec_spec) : Prop :=
    (forall l p bt rt, g l = p -> (loc_context G) l = Some (Typ bt p, rt))
    /\ (forall x, (var_context G) x = Some (Typ Tnat (LevelP L))).
  
  Definition g_prime (d: loc_mode) (g: sec_spec) (I: set enclave) : sec_spec :=
    fun l => match (d l) with
             | Encl i => if (set_mem Nat.eq_dec i I) then g l else LevelP L
             | _ => LevelP L
             end.
      
  Lemma secure_passive : forall g G G' K' d c,
    well_formed_spec g ->
    corresponds G g ->
    context_wt G d ->
    com_type (LevelP L) Normal G nil nil d c G' K' ->
    secure_prog L g cstep estep c.
  Proof.
    intros. unfold secure_prog. intros.
    unfold knowledge_attack.
    intros.
  Admitted.

  Lemma secure_n_chaos : forall g G G' K' d c,
      well_formed_spec g ->
      corresponds G g ->
      context_wt G d ->
      com_type (LevelP L) Normal G nil nil d c G' K' ->
      secure_prog L g cstep_n_chaos estep c.
  Proof.
  Admitted.

  Lemma secure_e_chaos : forall g G G' K' d c I,
      well_formed_spec g ->
      corresponds G g ->
      context_wt G d ->
      com_type (LevelP L) Normal G nil nil d c G' K' ->
      secure_prog H (g_prime d g I) (cstep_e_chaos I) estep c.
  Proof.
  Admitted.
End Guarantees.
*)
