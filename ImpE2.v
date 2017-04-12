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
(* XXX NOTE: name conflicts will occur *)
Require Import ImpE.

(*******************************************************************************
*
* SYNTAX
*
*******************************************************************************)

Section Syntax.
  Inductive exp2 : Type :=
  | Enat2 : nat -> exp2
  | Evar2 : var -> exp2
  | Eplus2 : exp2 -> exp2 -> exp2
  | Emult2 : exp2 -> exp2 -> exp2
  | Eloc2 : location -> exp2
  | Ederef2 : exp2 -> exp2
  | Eisunset2 : condition -> exp2
  | Elambda2 : mode -> com2 -> exp2
                                   
  with com2 : Type :=
  | Cskip2 : com2
  | Cassign2 : var -> exp2 -> com2
  | Cdeclassify2 : var -> exp2 -> com2
  | Cupdate2 : exp2 -> exp2 -> com2
  | Coutput2 : exp2 -> sec_level -> com2
  | Ccall2 : exp2 -> com2
  | Cset2 : condition -> com2
  | Cenclave2 : enclave -> com2 -> com2
  | Ckill2 : enclave -> com2
  | Cseq2 : list com2 -> com2
  | Cif2 : exp2 -> com2 -> com2 -> com2
  | Cwhile2 : exp2 -> com2 -> com2.

  Inductive val2 : Type :=
  | Vlambda2 : mode -> com2 -> val2
  | Vnat2 : nat -> val2
  | Vloc2 : location -> val2
  | Vpair2 : val2 -> val2 -> val2.

  Function forall_subexp2 (e: exp2) (P: exp2 -> Prop) : Prop :=
    P e /\
    match e with
    | Eplus2 e1 e2 => forall_subexp2 e1 P /\ forall_subexp2 e2 P
    | Emult2 e1 e2 => forall_subexp2 e1 P /\ forall_subexp2 e2 P
    | Ederef2 e' => forall_subexp2 e' P
    | Elambda2 _ c => forall_subexp2' c P
    | _ => True
    end
  with forall_subexp2' (c: com2) (P: exp2 -> Prop) : Prop :=
    match c with
    | Cassign2 _ e => forall_subexp2 e P
    | Cdeclassify2 _ e => forall_subexp2 e P
    | Cupdate2 e1 e2 => forall_subexp2 e1 P /\ forall_subexp2 e2 P
    | Ccall2 e => forall_subexp2 e P
    | Cenclave2 _ c' => forall_subexp2' c' P
    | Cseq2 cs => fold_left (fun acc c => forall_subexp2' c P /\ acc) cs True
    | Cif2 e c1 c2 =>
      forall_subexp2 e P /\ forall_subexp2' c1 P /\ forall_subexp2' c2 P
    | Cwhile2 e c' => forall_subexp2 e P /\ forall_subexp2' c' P
    | _ => True
    end.

   Ltac auto_decide :=
    try match goal with
    | [x : nat, y : nat |- _] => destruct (Nat.eq_dec x y)
    | [x : var, y : var |- _] => destruct (Nat.eq_dec x y)
    | [x : condition, y : condition |- _] => destruct (Nat.eq_dec x y)
    | _ => idtac
    end; [left; now subst | right; congruence].

  Definition exp2_novars (e: exp2) : Prop :=
    forall_subexp2 e (fun e =>
                       match e with
                       | Evar2 _ => False
                       | _ => True
                       end).
 
  Lemma com2_decidable : forall c1 c2 : com2, {c1 = c2} + {c1 <> c2}.
  Admitted.

  (* XXX I feel like it should be easy to prove this...? *)
  Lemma val2_decidable : forall v1 v2 : val2, {v1 = v2} + {v1 <> v2}.
  Proof.
    intros.
    destruct v1, v2; try (right; discriminate).
    destruct (mode_decidable m m0); destruct (com2_decidable c c0); subst;
    [left; auto | | | ]; right; congruence.
    auto_decide.
    destruct l, l0; try (right; discriminate); auto_decide.
  Admitted.

End Syntax.

(*******************************************************************************
*
* SEMANTICS
*
*******************************************************************************)

Section Semantics.
  Definition reg2 : Type := register val2.
  Definition reg_init2 : reg2 := fun x => Vnat2 0.
  Definition mem2 : Type := memory val2.
  Inductive kill2 : Type :=
  | KSingle: set enclave -> kill2
  | KPair: kill2 -> kill2 -> kill2.

  Inductive event2 : Type :=
  | Emp : event2
  | Decl : exp2 -> mem2 -> event2
  | Mem : mem2 -> event2
  | Out : sec_level -> val2 -> event2
  | ANonEnc : com2 -> event2
  (* XXX: need to add enc equiv definition for com2 *)
  | AEnc : forall c c' : com2, (*enc_equiv c c'*) event2
  | EPair : event2 -> event2 -> event2.
  Definition trace2 : Type := list event2.

  (* Mode is only alive if it is alive in both of the kill sets in a pair *)
  (* XXX: not sure if this definition is right but it seems reasonable *)
  Function mode_alive2 (md : mode) (k : kill2) :=
    match md with
    | Normal => True
    | Encl i =>
      match k with
      | KSingle ks => ~set_In i ks
      | KPair ks1 ks2 => mode_alive2 md ks1 /\ mode_alive2 md ks2
      end
    end.
  
  Definition mode_access_ok2 (md : mode) (d : loc_mode) (l : location) (k : kill2) :=
    let lmd := d l in
    match lmd with
    | Normal => True
    | Encl _ => md = lmd /\ mode_alive2 lmd k
    end.
  
  Definition merge_reg (r1 r2: reg2) :=
    fun x => if val2_decidable (r1 x) (r2 x) then r1 x
             else Vpair2 (r1 x) (r2 x).
  Definition merge_mem (m1 m2: mem2) :=
    fun l => if val2_decidable (m1 l) (m2 l) then m1 l
             else m2 l.
  Definition tracepair_len (t: trace2 * trace2) := length (fst t) + length (snd t).
  Function merge_trace (t: trace2 * trace2) {measure tracepair_len t} :=
    match fst t, snd t with
    | a1::tl1, a2::tl2 => EPair a1 a2 :: (merge_trace (tl1, tl2))
    | a1::tl1, [] => EPair a1 Emp :: merge_trace (tl1, [])
    | [], a2::tl2 => EPair Emp a2 :: merge_trace ([], tl2)
    | _, _ => []
    end.
  Proof. all: intros; unfold tracepair_len; rewrite teq, teq0; simpl; omega. Qed.
  Definition merge_kill (k1 k2: kill2) := KPair k1 k2.
  
  Definition project_value (v : val2) (is_left : bool) : val2 :=
    match v with
    | Vpair2 v1 v2 => if is_left then v1 else v2
    | _ => v
    end.
  
  Definition project_reg (r: reg2) (is_left : bool): reg2 :=
    fun x => match r x with
             | Vpair2 v1 v2 => if is_left then v1 else v2
             | _ => r x
          end.

  Definition project_mem (m: mem2) (is_left : bool): mem2 :=
    fun x => match m x with
          | Vpair2 v1 v2 => if is_left then v1 else v2
          | _ => m x
          end.

  Definition project_kill (k: kill2) (is_left : bool) : kill2 :=
    match k with
    | KPair ks1 ks2 => if is_left then ks1 else ks2
    | _ => k
    end.

  Function project_trace (t: trace2) (is_left : bool) : trace2 :=
    match t with
    | [] => []
    | hd :: tl =>
      let tl_proj := (project_trace tl is_left) in
      match hd with
      | Mem m => Mem (project_mem m is_left) :: tl_proj
      | Decl e m => Decl e (project_mem m is_left) :: tl_proj
      | Out l v => Out l (project_value v is_left) :: tl_proj
      | ANonEnc _ | AEnc _ _ => hd :: tl_proj
      | EPair e1 e2 => if is_left then e1 :: tl_proj else e2 :: tl_proj
      | _ => []
      end
    end.
  
  Definition econfig2 : Type := exp2 * reg2 * mem2 * kill2.
  Definition ecfg_exp2 (ecfg: econfig2) : exp2 :=
    match ecfg with (e, _, _, _) => e end.
  Definition ecfg_reg2 (ecfg: econfig2) : reg2 :=
    match ecfg with (_, r, _, _) => r end.
  Definition ecfg_mem2 (ecfg: econfig2) : mem2 :=
    match ecfg with (_, _, m, _) => m end.
  Definition ecfg_update_exp2 (ecfg: econfig2) (e: exp2) : econfig2 :=
    match ecfg with (_, r, m, k) => (e, r, m, k) end.
  Definition esemantics2 : Type := mode -> loc_mode -> econfig2 -> val2 -> Prop.

  Inductive estep2 : esemantics2 :=
  | Estep2_nat : forall md d ecfg n,
      ecfg_exp2 ecfg = Enat2 n ->
      estep2 md d ecfg (Vnat2 n)
  | Estep2_loc : forall md d ecfg l,
      ecfg_exp2 ecfg = Eloc2 l ->
      estep2 md d ecfg (Vloc2 l)
  | Estep2_lambda : forall md d ecfg c,
      ecfg_exp2 ecfg = Elambda2 md c ->
      estep2 md d ecfg (Vlambda2 md c)
  | Estep2_var : forall md d ecfg x v,
      ecfg_exp2 ecfg = Evar2 x ->
      ecfg_reg2 ecfg x = v ->
      estep2 md d ecfg v
  | Estep2_plus : forall md d ecfg e1 e2 n1 n2,
      ecfg_exp2 ecfg = Eplus2 e1 e2 ->
      estep2 md d (ecfg_update_exp2 ecfg e1) (Vnat2 n1) ->
      estep2 md d (ecfg_update_exp2 ecfg e2) (Vnat2 n2) ->
      estep2 md d ecfg (Vnat2 (n1 + n2))
  | Estep2_mult : forall md d ecfg e1 e2 n1 n2,
      ecfg_exp2 ecfg = Emult2 e1 e2 ->
      estep2 md d (ecfg_update_exp2 ecfg e1) (Vnat2 n1) ->
      estep2 md d (ecfg_update_exp2 ecfg e2) (Vnat2 n2) ->
      estep2 md d ecfg (Vnat2 (n1 * n2))
  | Estep2_deref : forall md d ecfg e r m k l v,
      ecfg = (Ederef2 e, r, m, k) ->
      estep2 md d (e, r, m, k) (Vloc2 l) ->
      m l = v ->
      mode_access_ok2 md d l k ->
      estep2 md d ecfg v
  | Estep2_isunset : forall md d ecfg cnd v res,
      ecfg_exp2 ecfg = Eisunset2 cnd ->
      estep2 md d (ecfg_update_exp2 ecfg (Ederef2 (Eloc2 (Cnd cnd)))) v ->
      (v = Vnat2 0 /\ res = Vnat2 1) \/ (v <> Vnat2 0 /\ res = Vnat2 0) ->
      estep2 md d ecfg res.

  (* Semantics for commands. *)
  Definition cconfig2 : Type := com2 * reg2 * mem2 * kill2.
  Definition cterm2 : Type := reg2 * mem2 * kill2.
  Definition ccfg_com2 (ccfg: cconfig2) : com2 :=
    match ccfg with (c, _, _, _) => c end.
  Definition ccfg_reg2 (ccfg: cconfig2) : reg2 :=
    match ccfg with (_, r, _, _) => r end.
  Definition ccfg_mem2 (ccfg: cconfig2) : mem2 :=
    match ccfg with (_, _, m, _) => m end.
  Definition ccfg_kill2 (ccfg: cconfig2) : kill2 :=
    match ccfg with (_, _, _, k) => k end.
  Definition ccfg_update_mem2 (ccfg: cconfig2) (l: location) (v: val2) : mem2 := 
    fun loc => if locations_eq loc l then v
               else (ccfg_mem2 ccfg) loc.
  Definition ccfg_update_reg2 (ccfg: cconfig2) (x: var) (v: val2) : reg2 :=
    fun var => if var =? x then v
               else (ccfg_reg2 ccfg) var.
  Definition ccfg_to_ecfg2 (e: exp2) (ccfg : cconfig2) : econfig2 :=
    (e, (ccfg_reg2 ccfg), (ccfg_mem2 ccfg), (ccfg_kill2 ccfg)).
  Definition ccfg_update_com2 (c: com2) (ccfg : cconfig2) : cconfig2 :=
    (c, (ccfg_reg2 ccfg), (ccfg_mem2 ccfg), (ccfg_kill2 ccfg)).
  Definition csemantics2 : Type := mode -> loc_mode -> cconfig2 -> cterm2 -> trace2 -> Prop.  

  Inductive cstep2 : csemantics2 := 
  | Cstep2_skip : forall md d ccfg,
      cstep2 md d ccfg (ccfg_reg2 ccfg, ccfg_mem2 ccfg, ccfg_kill2 ccfg) []
  | Cstep2_assign : forall md d ccfg x e v r',
      ccfg_com2 ccfg = Cassign2 x e ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) v ->
      r' = ccfg_update_reg2 ccfg x v ->
      mode_alive2 md (ccfg_kill2 ccfg) ->
      cstep2 md d ccfg (r', ccfg_mem2 ccfg, ccfg_kill2 ccfg) []
  | Cstep2_declassify : forall md d ccfg x e v r',
      ccfg_com2 ccfg = Cdeclassify2 x e ->
      exp2_novars e ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) v ->
      r' = ccfg_update_reg2 ccfg x v ->
      mode_alive2 md (ccfg_kill2 ccfg) ->
      cstep2 md d ccfg (r', ccfg_mem2 ccfg, ccfg_kill2 ccfg) [Decl e (ccfg_mem2 ccfg)]
  | Cstep2_update : forall md d ccfg e1 e2 l v m',
      ccfg_com2 ccfg = Cupdate2 e1 e2 ->
      estep2 md d (ccfg_to_ecfg2 e1 ccfg) (Vloc2 l) ->
      estep2 md d (ccfg_to_ecfg2 e2 ccfg) v ->
      mode_alive2 md (ccfg_kill2 ccfg) ->
      mode_access_ok2 md d l (ccfg_kill2 ccfg) ->
      is_Not_cnd l ->
      m' = ccfg_update_mem2 ccfg l v ->
      cstep2 md d ccfg (ccfg_reg2 ccfg, m', ccfg_kill2 ccfg) []
  | Cstep2_output : forall md d ccfg e sl v,
      ccfg_com2 ccfg = Coutput2 e sl ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) v ->
      sl = L \/ sl = H ->
      mode_alive2 md (ccfg_kill2 ccfg) ->
      cstep2 md d ccfg (ccfg_reg2 ccfg, ccfg_mem2 ccfg, ccfg_kill2 ccfg)
            [Mem (ccfg_mem2 ccfg); Out sl v]
  | Cstep2_call : forall md d ccfg e c r' m' k' tr,
      ccfg_com2 ccfg = Ccall2 e ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (Vlambda2 md c) ->
      cstep2 md d (ccfg_update_com2 c ccfg) (r', m', k') tr ->
      cstep2 md d ccfg (r', m', k') tr
  | Cstep2_cset : forall md d ccfg c m',
      ccfg_com2 ccfg = Cset2 c ->
      mode_access_ok2 md d (Cnd c) (ccfg_kill2 ccfg) ->
      m' = ccfg_update_mem2 ccfg (Cnd c) (Vnat2 1) ->
      mode_alive2 md (ccfg_kill2 ccfg) ->      cstep2 md d ccfg (ccfg_reg2 ccfg, m', ccfg_kill2 ccfg) [Mem m']
  | Cstep2_enclave : forall md d ccfg enc c r' m' k' tr,
    md = Normal ->
    ccfg_com2 ccfg = Cenclave2 enc c ->
    cstep2 (Encl enc) d (c, ccfg_reg2 ccfg, ccfg_mem2 ccfg, ccfg_kill2 ccfg) (r', m', k') tr ->
    cstep2 md d ccfg (r', m', k') tr
  | Cstep2_seq_nil : forall md d ccfg,
      ccfg_com2 ccfg = Cseq2 [] ->
      cstep2 md d ccfg (ccfg_reg2 ccfg, ccfg_mem2 ccfg, ccfg_kill2 ccfg) []
  | Cstep2_seq_hd : forall md d ccfg hd tl r m k tr r' m' k' tr',
      ccfg_com2 ccfg = Cseq2 (hd::tl) ->
      cstep2 md d (ccfg_update_com2 hd ccfg) (r, m, k) tr ->
      cstep2 md d (Cseq2 tl, r, m, k) (r', m', k') tr' ->
      cstep2 md d ccfg (r', m', k') (tr++tr')
  | Cstep2_if : forall md d ccfg e c1 c2 n r' m' k' tr,
      ccfg_com2 ccfg = Cif2 e c1 c2 ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (Vnat2 n) ->
      ~(n = 0) ->
      cstep2 md d (ccfg_update_com2 c1 ccfg) (r', m', k') tr ->
      cstep2 md d ccfg (r', m', k') tr
  | Cstep2_else : forall md d ccfg e c1 c2 n r' m' k' tr,
      ccfg_com2 ccfg = Cif2 e c1 c2 ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (Vnat2 n) ->
      (n = 0) ->
      cstep2 md d (ccfg_update_com2 c2 ccfg) (r', m', k') tr ->
      cstep2 md d ccfg (r', m', k') tr
  | Cstep2_if_div : forall md d ccfg e c1 c2 n1 n2 r1 m1 k1 t1 r2 m2 k2 t2,
      ccfg_com2 ccfg = Cif2 e c1 c2 ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (Vpair2 (Vnat2 n1) (Vnat2 n2)) ->
      let cleft := (match n1 with
                    | 0 => c2
                    | _ => c1 end) in
      cstep2 md d (cleft, project_reg (ccfg_reg2 ccfg) true,
                   project_mem (ccfg_mem2 ccfg) true, project_kill (ccfg_kill2 ccfg) true)
             (r1, m1, k1) t1 ->
      let cright := (match n2 with
                     | 0 => c2
                     | _ => c1 end) in
      cstep2 md d (cright, project_reg (ccfg_reg2 ccfg) false,
                   project_mem (ccfg_mem2 ccfg) false, project_kill (ccfg_kill2 ccfg) false)
             (r2, m2, k2) t2 ->
      cstep2 md d ccfg (merge_reg r1 r2, merge_mem m1 m2, merge_kill k1 k2) (merge_trace (t1, t2))
  | Cstep_while_t : forall md d ccfg e c v r m k tr r' m' k' tr',
      ccfg_com2 ccfg = Cwhile2 e c ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) v ->
      ~(v = (Vnat2 0)) ->
      cstep2 md d (ccfg_update_com2 c ccfg) (r, m, k) tr ->
      cstep2 md d (ccfg_update_com2 (Cwhile2 e c) ccfg) (r', m', k') tr' ->
      cstep2 md d ccfg (r', m', k') (tr++tr')
  | Cstep_while_f : forall md d ccfg e c,
      ccfg_com2 ccfg = Cwhile2 e c ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (Vnat2 0) ->
      mode_alive2 md (ccfg_kill2 ccfg) ->
      cstep2 md d ccfg (ccfg_reg2 ccfg, ccfg_mem2 ccfg, ccfg_kill2 ccfg) []
  (* XXX add in while-div and call-div *)
  (* XXX: add in set add for pairs
  | Cstep_kill : forall md d ccfg enc,
      md = Normal ->
      ccfg_com2 ccfg = Ckill2 enc ->
      mode_alive2 (Encl enc) (ccfg_kill2 ccfg) ->
      cstep2 md d ccfg (ccfg_reg2 ccfg, ccfg_mem2 ccfg, set_add Nat.eq_dec enc (ccfg_kill2 ccfg)) []*).
End Semantics.
(*
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
  | Tlambda (G: context) (k:set enclave) (u:set condition) (p: sec_policy)
            (md: mode) (G': context) (k':set enclave) : base_type
                           
  with type : Type :=
  | Typ : base_type -> sec_policy -> type
                                            
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
                    p <> LevelP T /\ (p = LevelP H -> exists i, d l = Encl i)).
  
  Definition is_var_low_context (G: context) : Prop :=
    forall_var G (fun _ t => let (_, p) := t in p = LevelP L).

  Definition all_loc_immutable (e: exp2) (G: context) : Prop :=
    forall_subexp2 e (fun e =>
                       match e with
                       | Eloc (Cnd _) => False
                       | Eloc (Not_cnd l) => forall t rt,
                           loc_context G (Not_cnd l) = Some (t, rt) ->
                           rt = Immut
                       | _ => True
                       end).

  (* FIXME: don't have subsumption rule *)
  Inductive exp2_type : mode -> context -> loc_mode -> exp2 -> type -> Prop :=
  | ETnat : forall md g d n,
      exp2_type md g d (Enat n) (Typ Tnat (LevelP L))
  | ETvar : forall md g d x t,
      var_context g x = Some t -> exp2_type md g d (Evar x) t
  | ETcnd : forall md g d a md',
      let l := Cnd a in
      d l = md' ->
      exp2_type md g d (Eloc l) (Typ (Tcond md') (LevelP L))
  | ETloc : forall md g d a md' t rt,
      let l := Not_cnd a in
      d l = md' ->
      loc_context g l = Some (t, rt) ->
      exp2_type md g d (Eloc l) (Typ (Tref t md' rt) (LevelP L))
  | ETderef : forall md g d e md' s p rt q,
      exp2_type md g d e (Typ (Tref (Typ s p) md' rt) q) ->
      md' = Normal \/ md' = md ->
      exp2_type md g d (Ederef e) (Typ s (policy_join p q))
  | ETunset : forall md g d cnd md',
      md' = d (Cnd cnd) ->
      md' = Normal \/ md' = md ->
      exp2_type md g d (Eisunset cnd) (Typ Tnat (LevelP L))
  | ETlambda : forall md g d c p k u g' k',
      com2_type p md g k u d c g' k' ->
      exp2_type md g d (Elambda md c) (Typ (Tlambda g k u p md g' k') (LevelP L))
  | ETplus : forall md g d e1 e2 p q,
      exp2_type md g d e1 (Typ Tnat p) ->
      exp2_type md g d e2 (Typ Tnat q) ->
      exp2_type md g d (Eplus e1 e2) (Typ Tnat (policy_join p q))
  | ETmult : forall md g d e1 e2 p q,
      exp2_type md g d e1 (Typ Tnat p) ->
      exp2_type md g d e2 (Typ Tnat q) ->
      exp2_type md g d (Emult e1 e2) (Typ Tnat (policy_join p q))

  with com2_type : sec_policy -> mode -> context -> set enclave ->
                  set condition -> loc_mode -> com2 ->
                  context -> set enclave -> Prop :=
  | CTskip : forall pc md g d k u,
      mode_alive md k ->
      com2_type pc md g k u d Cskip g k
  | CTkill : forall i g d k u,
      mode_alive (Encl i) k ->
      com2_type (LevelP L) Normal g k u d (Ckill i) g (set_add Nat.eq_dec i k)
  | CTassign : forall pc md g k u d x e s p q vc lc vc',
      exp2_type md g d e (Typ s p) ->
      q = policy_join p pc ->
      q <> LevelP T ->
      policy_le q (LevelP L) \/ md <> Normal ->
      mode_alive md k ->
      g = Cntxt vc lc ->
      vc' = (fun y => if y =? x then Some (Typ s q) else vc y) ->
      com2_type pc md g k u d (Cassign x e) (Cntxt vc' lc) k
  | CTdeclassify : forall md g k u d x e s p vc lc vc',
      exp2_type md g d e (Typ s p) ->
      p <> LevelP T ->
      mode_alive md k ->
      exp2_novars e ->
      all_loc_immutable e g ->
      vc' = (fun y => if y =? x then Some (Typ s (LevelP L)) else vc y) ->
      com2_type (LevelP L) md g k u d (Cdeclassify x e) (Cntxt vc' lc) k
  | CToutput : forall pc md g k u d e l s p,
      exp2_type md g d e (Typ s p) ->
      mode_alive md k ->
      p <> LevelP T ->
      sec_level_le (sec_level_join (cur p u) (cur pc u)) l ->
      com2_type pc md g k u d (Coutput e l) g k
  | CTupdate : forall pc md g k u d e1 e2 s p md' q p',
      exp2_type md g d e1 (Typ (Tref (Typ s p) md' Mut) q) ->
      exp2_type md g d e2 (Typ s p') ->
      policy_le (policy_join (policy_join p' q) pc) p ->
      md' = Normal \/ md' = md ->
      mode_alive md k ->
      p <> LevelP T ->
      p' <> LevelP T ->
      q <> LevelP T ->
      com2_type pc md g k u d (Cupdate e1 e2) g k
  | Tset : forall md g k u d cnd md',
      md' = d (Cnd cnd) ->
      ~set_In cnd u ->
      md' = Normal \/ md' = md ->
      mode_alive md k ->
      com2_type (LevelP L) md g k u d (Cset cnd) g k
  | Tifunset : forall pc md g k u d cnd c1 c2 g' k',
      exp2_type md g d (Eisunset cnd) (Typ Tnat (LevelP L)) ->
      com2_type pc md g k (set_add Nat.eq_dec cnd u) d c1 g' k' ->
      com2_type pc md g k u d c2 g' k' ->
      com2_type pc md g k u d (Cif (Eisunset cnd) c1 c2) g' k'
  | Tifelse : forall pc md g k u d e c1 c2 pc' p g' k',
      ~(exists cnd, e = Eisunset cnd) ->
      com2_type pc' md g k u d c1 g' k' ->
      com2_type pc' md g k u d c2 g' k' ->
      exp2_type md g d e (Typ Tnat p) ->
      policy_le (policy_join pc p) pc' ->
      policy_le p (LevelP L) \/ md <> Normal ->
      p <> LevelP T ->
      com2_type pc md g k u d (Cif e c1 c2) g' k'
  | Tenclave : forall pc g k u d c i c' g' k',
      c = Cenclave i c' ->
      com2_type pc (Encl i) g k nil d c' g' k' ->
      is_var_low_context g' ->
      com2_type pc Normal g k u d c g' k'
  | Twhile : forall pc md g k u d c e p pc',
      exp2_type md g d e (Typ Tnat p) ->
      com2_type pc' md g k u d c g k ->
      policy_le (policy_join pc p) pc' ->
      policy_le p (LevelP L) \/ md <> Normal ->
      p <> LevelP T ->
      com2_type pc md g k u d (Cwhile e c) g k
  | Tseq : forall pc md g k u d c rest g' k' gn kn,
      com2_type pc md g k u d c g' k' ->
      com2_type pc md g' k' u d (Cseq rest) gn kn ->
      com2_type pc md g k u d (Cseq (c :: rest)) gn kn
  | Tseqnil : forall pc md g k u d,
      com2_type pc md g k u d (Cseq []) g k
  | Tcall : forall pc md G u d e Gm km Gp kp Gout q p,
      exp2_type md G d e (Typ (Tlambda Gm km u p md Gp kp) q) ->
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
      com2_type pc md G km u d (Ccall e) Gout kp.
  
End Typing.

Section Security.
  Inductive protected : sec_policy -> set condition -> Prop :=
  | level_high: forall S, protected (LevelP H) S
  | level_top: forall S, protected (LevelP T) S
  | erase_high: forall cnd S sl pf,
      protected (ErasureP H cnd sl pf) S
  | erase_low: forall cnd S sl pf,
      set_In cnd S -> protected (ErasureP L cnd sl pf) S.
      
  Definition overlap (tr tobs: trace) :=
  | tobs is entirely contained in tr => tobs
  | tobs is after tr => empty
  | overlap with beginning of tobs => beginning of tobs
                                                    
  Lemma eq_overlap_tobs (m1 m2: mem) (tobs: trace) :
    forall md d c k r' m' k' tr1 tr2,
    cstep md d (c, reg_init, m1, k) (r', m', k') tr1 ->
    cstep md d (c, reg_init, m2, k) (r', m', k') tr2 ->
    tobs_sec_level L (overlap tr1 tobs) = tobs_sec_level L (overlap tr2 tobs).
      
End Security.
 *)

(*******************************************************************************
*
* ADEQUACY
*
*******************************************************************************)
Section Adequacy.

  Definition not_pair_val (v : val2) : Prop :=
    match v with
    | Vpair2 _ _ => False
    | _ => True
    end.
  
  Definition no_nest_val (v : val2) : Prop :=
    match v with
    | Vpair2 v1 v2 => (not_pair_val v1) /\ (not_pair_val v2)
    | _ => True
    end.

  Definition kill_wf (k : kill2) : Prop :=
    match k with
    | KPair (KSingle _) (KSingle _) => True
    | KSingle _ => True
    | _ => False
    end.

  Definition reg_wf (r : reg2) : Prop :=
    forall x, no_nest_val (r x).

  Definition mem_wf (m : mem2) : Prop :=
    forall x, no_nest_val (m x).

  (* XXX: thought I needed this for exp_output_wf, didn't use it. Might still be useful...? *)
  Lemma estep2_deterministic : forall md d e r m k v1 v2,
    estep2 md d (e, r, m, k) v1 ->
    estep2 md d (e, r, m, k) v2 ->
    v1 = v2.
  Proof.
    intros; revert H0; revert v2.
    induction H; intros; destruct ecfg as [[[e' r'] m'] k']; simpl in *; try rewrite H in H0.
    1-3: inversion H0; subst; try discriminate; simpl in H1; congruence.
    inversion H1; subst; try discriminate; simpl in *; congruence.
    1-2: rewrite H in H2; inversion H2; try discriminate; simpl in *;
      assert (e1 = e0) by congruence; assert (e2 = e3) by congruence;
        subst; apply IHestep2_1 in H4; apply IHestep2_2 in H5;
          assert (n1 = n0) by congruence; assert (n2 = n3) by congruence; now subst.
    - rewrite H in H3; inversion H3; subst; try discriminate; simpl in *.
      assert (e0 = e1) by congruence.
      assert (r0 = r1) by congruence.
      assert (m0 = m1) by congruence.
      assert (k0 = k1) by congruence.
      subst. apply IHestep2 in H5. assert (l = l0) by congruence; now subst.
    -  rewrite H in H2; inversion H2; subst; try discriminate; simpl in *.
       assert (cnd = cnd0) by congruence; subst.
       apply IHestep2 in H4.
       destruct H1; destruct H5; destruct_conjs; subst; auto; congruence.
  Qed.      
  
  Lemma impe2_exp_output_wf : forall md d ecfg v,
      estep2 md d ecfg v ->
      mem_wf (ecfg_mem2 ecfg) ->
      reg_wf (ecfg_reg2 ecfg) ->
      no_nest_val v.
  Proof.
    intros.
    induction H; simpl; auto.
    - unfold reg_wf in H1; now rewrite <- H2.
    - rewrite H in H0; unfold mem_wf in H0; simpl in *; now rewrite <- H3.
    - destruct H3; destruct_conjs; subst; now simpl.
  Qed.
      
  Lemma impe2_output_wf : forall md d ccfg r' m' K' t,
          reg_wf (ccfg_reg2 ccfg) ->
          mem_wf (ccfg_mem2 ccfg) ->
          cstep2 md d ccfg (r', m', K') t ->
          reg_wf r' /\ mem_wf m' /\ kill_wf K'.
  Proof.
  Admitted.

  
  
    
  (* XXX this theorem statement doesn't work because the projection functions return back
     the xxx2 types for ImpE2 where we need the types for IMPE... *)
Lemma impe2_sound : forall md d c r m K r' m' K' t,
    cstep2 md d (c, r, m, K) (r', m', K') t ->
    (cstep md d (c, project_reg r true, project_mem m true, project_kill K true)
           (project_reg r' true, project_mem m' true, project_kill K' true) project_trace t true) /\
    (cstep md d (c, project_reg r false, project_mem m false, project_kill K false)
           (project_reg r' false, project_mem m' true, project_kill K' false) project_trace t false) *)
  
End Adequacy.