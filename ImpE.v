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
  | Eadd : exp -> exp -> exp
  | Eloc : location -> exp
  | Ederef : exp -> exp
  | Elambda : mode -> com -> exp
                                   
  with com : Type :=
  | Cskip : com
  | Cassign : var -> exp -> com
  | Cdeclassify : var -> exp -> com
  | Cupdate : exp -> exp -> com
  | Coutput : exp -> sec_level -> com
  | Ccall : exp -> com
  | Cenclave : enclave -> com -> com
  | Cseq : list com -> com
  | Cif : exp -> com -> com -> com
  | Cwhile : exp -> com -> com.

  Inductive val : Type :=
  | Vlambda : mode -> com -> val
  | Vnat : nat -> val
  | Vloc : location -> val.

  Function forall_subexp (e: exp) (P: exp -> Prop) : Prop :=
    P e /\
    match e with
    | Eadd e1 e2 => forall_subexp e1 P /\ forall_subexp e2 P
    | Ederef e' => forall_subexp e' P
    | Elambda _ c => forall_subexp' c P
    | _ => True
    end
  with forall_subexp' (c: com) (P: exp -> Prop) : Prop :=
    match c with
    | Cassign _ e => forall_subexp e P
    | Cdeclassify _ e => forall_subexp e P
    | Cupdate e1 e2 => forall_subexp e1 P /\ forall_subexp e2 P
    | Ccall e => forall_subexp e P
    | Cenclave _ c' => forall_subexp' c' P
    | Cseq cs => fold_left (fun acc c => forall_subexp' c P /\ acc) cs True
    | Cif e c1 c2 =>
      forall_subexp e P /\ forall_subexp' c1 P /\ forall_subexp' c2 P
    | Cwhile e c' => forall_subexp e P /\ forall_subexp' c' P
    | _ => True
    end.

  Definition exp_novars (e: exp) : Prop :=
    forall_subexp e (fun e =>
                       match e with
                       | Evar _ => False
                       | _ => True
                       end).
  
End Syntax.

Section Induction.
  Variable P : com -> Type.
  Variable P0: exp -> Type.
  
  Inductive Forall' (Q : com -> Type) : list com -> Type :=
  | Forall_nil' : Forall' Q nil
  | Forall_cons' : forall x l, Q x -> Forall' Q l -> Forall' Q (x::l).

  Hypothesis Enat_case : forall n, P0 (Enat n).
  Hypothesis Evar_case : forall x, P0 (Evar x).
  Hypothesis Eadd_case : forall e1 e2,
      P0 e1 -> P0 e2 -> P0 (Eadd e1 e2).
  Hypothesis Eloc_case : forall l, P0 (Eloc l).
  Hypothesis Ederef_case : forall e,
      P0 e -> P0 (Ederef e).
  Hypothesis Elambda_case : forall md c,
      P c -> P0 (Elambda md c).

  Hypothesis Cskip_case : P Cskip.
  Hypothesis Cassign_case : forall x e,
      P0 e -> P (Cassign x e).  
  Hypothesis Cdeclassify_case : forall x e,
      P0 e -> P (Cdeclassify x e).
  Hypothesis Cupdate_case : forall e1 e2,
      P0 e1 -> P0 e2 -> P (Cupdate e1 e2).
  Hypothesis Coutput_case : forall e sl,
      P0 e -> P (Coutput e sl).
  Hypothesis Ccall_case : forall e,
      P0 e -> P (Ccall e).
  Hypothesis Cenclave_case : forall enc c,
      P c -> P (Cenclave enc c).
  Hypothesis Cseq_case : forall coms,
      Forall' P coms -> P (Cseq coms).
  Hypothesis Cif_case : forall e c1 c2,
      P0 e -> P c1 -> P c2 -> P (Cif e c1 c2).
  Hypothesis Cwhile_case : forall e c,
      P0 e -> P c -> P (Cwhile e c).

  Fixpoint com_rect' (c: com) : P c :=
    match c with
    | Cskip => Cskip_case
    | Cassign x e => Cassign_case x e (exp_rect' e)
    | Cdeclassify x e => Cdeclassify_case x e (exp_rect' e)
    | Cupdate e1 e2 => Cupdate_case e1 e2 (exp_rect' e1) (exp_rect' e2)
    | Coutput e sl => Coutput_case e sl (exp_rect' e)
    | Ccall e => Ccall_case e (exp_rect' e)
    | Cenclave enc c => Cenclave_case enc c (com_rect' c)
    | Cseq coms =>
      Cseq_case coms
                ((fix com_list_rect (coms: list com) : Forall' P coms :=
                    match coms with
                    | [] => Forall_nil' P
                    | h :: t => Forall_cons' P h t (com_rect' h) (com_list_rect t)
                    end) coms)
    | Cif e c1 c2 =>
      Cif_case e c1 c2 (exp_rect' e) (com_rect' c1) (com_rect' c2)
    | Cwhile e c => Cwhile_case e c (exp_rect' e) (com_rect' c)
    end
      
  with
  exp_rect' (e: exp) : P0 e :=
    match e with
    | Enat n => Enat_case n
    | Evar x => Evar_case x
    | Eadd e1 e2 => Eadd_case e1 e2 (exp_rect' e1) (exp_rect' e2)
    | Eloc l => Eloc_case l
    | Ederef e => Ederef_case e (exp_rect' e)
    | Elambda md c => Elambda_case md c (com_rect' c)
    end.
  
End Induction.

Section Decidability.

  Ltac auto_decide :=
    try match goal with
        | [x : nat, y : nat |- _] => destruct (Nat.eq_dec x y)
        | [x : var, y : var |- _] => destruct (Nat.eq_dec x y)
        | [x : enclave, y : enclave |- _] => destruct (Nat.eq_dec x y)
        | [x : location, y : location |- _] => destruct (Nat.eq_dec x y)
        | _ => idtac            
        end; [left; now subst | right; congruence].

   Ltac easy_dec :=
     subst; auto; right; congruence.

  Lemma mode_decidable : forall m1 m2 : mode, {m1 = m2} + {m1 <> m2}.
  Proof.
    intros; destruct m1; destruct m2; try (right; discriminate).
    - left; auto.
    - destruct (Nat.eq_dec e e0); [left; now subst | right; congruence].
  Qed.
   
   Lemma exp_decidable : forall (e1 e2 : exp), {e1 = e2} + {e1 <> e2}.
  Proof.
    intro.
    induction e1 using exp_rect' with
    (P := fun c1 =>
            forall c2, {c1 = c2} + {c1 <> c2}); intros.
    1-6: destruct e2; try (right; discriminate).
    7-14,16: destruct c2; try (right; discriminate).
    1-2, 4: auto_decide.
    - destruct IHe1_1 with e2_1; destruct IHe1_2 with e2_2; easy_dec.
    - destruct IHe1 with e2; easy_dec.
    - destruct IHe1 with c0; destruct (mode_decidable md m); easy_dec.
    - auto.
    - destruct IHe1 with e; subst; [auto_decide | right; congruence].
    - destruct IHe1 with e; subst; [auto_decide | right; congruence].
    - destruct IHe1_1 with e; destruct IHe1_2 with e0; easy_dec.
    - destruct s; destruct sl; destruct IHe1 with e; easy_dec.
    - destruct IHe1 with e; easy_dec.
    - destruct IHe1 with c2; subst; [auto_decide | right; congruence].
    - generalize l; induction coms; intros; destruct l0; try (right; discriminate); auto.
      inversion X; subst.
      destruct X0 with c; try (right; congruence).
      apply IHcoms with (l := l0) in X1.
      destruct X1; subst.
      + left; inversion e0; subst; auto.
      + right; congruence.
    - destruct IHe1 with e; destruct IHe0 with c2; easy_dec.
    - destruct c0; try (right; discriminate).
      destruct IHe1 with e; destruct IHe0 with c0_1; destruct IHe2 with c0_2; easy_dec.
  Qed.
  
  Lemma com_decidable : forall (c1 c2 : com), {c1 = c2} + {c1 <> c2}.
  Proof.
    intro.
    induction c1 using com_rect' with
    (P0 := fun e1 =>
             forall e2, {e1 = e2} + {e1 <> e2}); intros.
    1-2, 4-6: destruct e2; try (right; discriminate).
    7-16: destruct c2; try (right; discriminate).
    1-3: auto_decide.
    - destruct IHc1 with e2; easy_dec.
    - destruct IHc1 with c; destruct (mode_decidable md m); easy_dec.
    - destruct e0; try (right; discriminate);
        destruct IHc1 with e0_1; destruct IHc0 with e0_2; easy_dec.
    - auto.
    - destruct IHc1 with e0; subst; [auto_decide | right; congruence].
    - destruct IHc1 with e0; subst; [auto_decide | right; congruence].
    - destruct IHc1 with e; destruct IHc0 with e0; easy_dec.
    - destruct s; destruct sl; destruct IHc1 with e0; easy_dec.
    - destruct IHc1 with e0; easy_dec.
    - destruct IHc1 with c2; subst; [auto_decide | right; congruence].
    - generalize l; induction coms; intros; destruct l0; try (right; discriminate); auto.
      inversion X; subst.
      destruct X0 with c; try (right; congruence).
      apply IHcoms with (l := l0) in X1.
      destruct X1; subst.
      + left; inversion e0; subst; auto.
      + right; congruence.
    - destruct IHc1_1 with e0; destruct IHc1_2 with c2_1; destruct IHc1_3 with c2_2; easy_dec.
    - destruct IHc1 with e0; destruct IHc0 with c2; easy_dec.
  Qed.
  
  Lemma val_decidable : forall (v1 v2 : val), {v1 = v2} + {v1 <> v2}.
  Proof.
    intro.
    induction v1; intros; destruct v2; try (right; discriminate); try auto_decide.
    destruct (mode_decidable m m0); destruct (com_decidable c c0); easy_dec.
  Qed.
      
  Lemma prog_decidable : forall p1 p2 : (com + exp), {p1 = p2} + {p1 <> p2}.
  Proof.
    intros; destruct p1; destruct p2; try (right; discriminate);
      [destruct (com_decidable c c0) | destruct (exp_decidable e e0)]; easy_dec.
  Qed.

  Lemma mode_prog_decidable : forall ep1 ep2 : (mode * (com + exp)), {ep1 = ep2} + {ep1 <> ep2}.
  Proof.
    intros; destruct ep1, ep2; destruct (mode_decidable m m0); destruct (prog_decidable s s0);
      easy_dec.
  Qed.
  
End Decidability.

(*******************************************************************************
*
* ENCLAVE EQUIVALENCE
*
*******************************************************************************)

Section Enclave_Equiv.
  Fixpoint chi (c : com) : set (mode * (com + exp)) :=
  let chi_exp :=
      (fix chi_exp (e : exp) : set (mode * (com + exp)) :=
         match e with
         | Eadd e1 e2 => set_union mode_prog_decidable (chi_exp e1) (chi_exp e2)
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
  Parameter g0: sec_spec.
  Parameter immutable_locs: sec_spec -> set location.

  Definition reg : Type := register val.
  Definition reg_init : reg := fun x => Vnat 0.
  Definition mem : Type := memory val.
  Definition loc_mode : Type := location -> mode.


  Inductive event : Type :=
  | Decl : exp -> mem -> event
  | Mem : mem -> event
  | Out : sec_level -> val -> event
  | Update : mem -> location -> val -> event
  | Assign : reg -> var -> val -> event
  | ANonEnc : com -> event
  | AEnc : forall c c' : com, enc_equiv c c'-> event
  | Emp: event.
  Definition trace : Type := list event.

  Definition mode_access_ok (md: mode) (d: loc_mode) (l: location) :=
    let lmd := d l in
    match lmd with
    | Normal => True
    | Encl _ => md = lmd
    end.
  
  Definition econfig : Type := exp * reg * mem.
  Definition ecfg_exp (ecfg: econfig) : exp :=
    match ecfg with (e, _, _) => e end.
  Definition ecfg_reg (ecfg: econfig) : reg :=
    match ecfg with (_, r, _) => r end.
  Definition ecfg_update_exp (ecfg: econfig) (e: exp) : econfig :=
    match ecfg with (_, r, m) => (e, r, m) end.
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
  | Estep_add : forall md d ecfg e1 e2 n1 n2,
      ecfg_exp ecfg = Eadd e1 e2 ->
      estep md d (ecfg_update_exp ecfg e1) (Vnat n1) ->
      estep md d (ecfg_update_exp ecfg e2) (Vnat n2) ->
      estep md d ecfg (Vnat (n1 + n2))
  | Estep_deref : forall md d ecfg e r m l v,
      ecfg = (Ederef e, r, m) ->
      estep md d (e, r, m) (Vloc l) ->
      m l = v ->
      mode_access_ok md d l ->
      estep md d ecfg v.
  Hint Constructors estep.

  (* Semantics for commands. *)
  Definition cconfig : Type := com * reg * mem              .
  Definition cterm : Type := reg * mem              .
  Definition ccfg_com (ccfg: cconfig) : com :=
    match ccfg with (c, _, _) => c end.
  Definition ccfg_reg (ccfg: cconfig) : reg :=
    match ccfg with (_, r, _) => r end.
  Definition ccfg_mem (ccfg: cconfig) : mem :=
    match ccfg with (_, _, m) => m end.
  Definition ccfg_update_mem (ccfg: cconfig) (l: location) (v: val) : mem := 
    fun loc => if loc =? l then v
               else (ccfg_mem ccfg) loc.
  Definition ccfg_update_reg (ccfg: cconfig) (x: var) (v: val) : reg :=
    fun var => if var =? x then v
               else (ccfg_reg ccfg) var.
  Definition ccfg_to_ecfg (e: exp) (ccfg : cconfig) : econfig :=
    (e, (ccfg_reg ccfg), (ccfg_mem ccfg)).
  Definition ccfg_update_com (c: com) (ccfg : cconfig) : cconfig :=
    (c, (ccfg_reg ccfg), (ccfg_mem ccfg)).
  Definition csemantics : Type := mode -> loc_mode -> cconfig -> cterm -> trace -> Prop.  

  (* XXX couldn't figure out a way to not have to introduce forall md d ccfg everywhere.. *)
  Inductive cstep : csemantics := 
  | Cstep_skip : forall md d ccfg,
      ccfg_com ccfg = Cskip ->
      cstep md d ccfg (ccfg_reg ccfg, ccfg_mem ccfg) []
  | Cstep_assign : forall md d ccfg x e v r',
      ccfg_com ccfg = Cassign x e ->
      estep md d (ccfg_to_ecfg e ccfg) v ->
      r' = ccfg_update_reg ccfg x v ->
      cstep md d ccfg (r', ccfg_mem ccfg) [Assign (ccfg_reg ccfg) x v]
  | Cstep_declassify : forall md d ccfg x e v r',
      ccfg_com ccfg = Cdeclassify x e ->
      exp_novars e ->
      estep md d (ccfg_to_ecfg e ccfg) v ->
      r' = ccfg_update_reg ccfg x v ->
      cstep md d ccfg (r', ccfg_mem ccfg) [Decl e (ccfg_mem ccfg)]
  | Cstep_update : forall md d ccfg e1 e2 l v m',
      ccfg_com ccfg = Cupdate e1 e2 ->
      estep md d (ccfg_to_ecfg e1 ccfg) (Vloc l) ->
      estep md d (ccfg_to_ecfg e2 ccfg) v ->
      m' = ccfg_update_mem ccfg l v ->
      cstep md d ccfg (ccfg_reg ccfg, m') [Update (ccfg_mem ccfg) l v]
  | Cstep_output : forall md d ccfg e sl v,
      ccfg_com ccfg = Coutput e sl ->
      estep md d (ccfg_to_ecfg e ccfg) v ->
      sl = L \/ sl = H ->
      cstep md d ccfg (ccfg_reg ccfg, ccfg_mem ccfg) [Mem (ccfg_mem ccfg); Out sl v]
  | Cstep_call : forall md d ccfg e c r' m' tr,
      ccfg_com ccfg = Ccall e ->
      estep md d (ccfg_to_ecfg e ccfg) (Vlambda md c) ->
      cstep md d (ccfg_update_com c ccfg) (r', m') tr ->
      cstep md d ccfg (r', m') tr
  | Cstep_enclave : forall md d ccfg enc c r' m' tr,
    md = Normal ->
    ccfg_com ccfg = Cenclave enc c ->
    cstep (Encl enc) d (c, ccfg_reg ccfg, ccfg_mem ccfg) (r', m') tr ->
    cstep md d ccfg (r', m') tr
  | Cstep_seq_nil : forall md d ccfg,
      ccfg_com ccfg = Cseq [] ->
      cstep md d ccfg (ccfg_reg ccfg, ccfg_mem ccfg) []
  | Cstep_seq_hd : forall md d ccfg hd tl r m tr r' m' tr' t,
      ccfg_com ccfg = Cseq (hd::tl) ->
      cstep md d (ccfg_update_com hd ccfg) (r, m) tr ->
      cstep md d (Cseq tl, r, m) (r', m') tr' ->
      t = tr ++ tr' ->
      cstep md d ccfg (r', m') t
  | Cstep_if : forall md d ccfg e c1 c2 r' m' tr,
      ccfg_com ccfg = Cif e c1 c2 ->
      estep md d (ccfg_to_ecfg e ccfg) (Vnat 1) ->
      cstep md d (ccfg_update_com c1 ccfg) (r', m') tr ->
      cstep md d ccfg (r', m') tr
  | Cstep_else : forall md d ccfg e c1 c2 r' m' tr,
      ccfg_com ccfg = Cif e c1 c2 ->
      estep md d (ccfg_to_ecfg e ccfg) (Vnat 0) ->
      cstep md d (ccfg_update_com c2 ccfg) (r', m') tr ->
      cstep md d ccfg (r', m') tr
  | Cstep_while_t : forall md d ccfg e c r m tr r' m' tr',
      ccfg_com ccfg = Cwhile e c ->
      estep md d (ccfg_to_ecfg e ccfg) (Vnat 1) ->
      cstep md d (ccfg_update_com c ccfg) (r, m) tr ->
      cstep md d (Cwhile e c,r,m) (r', m') tr' ->
      cstep md d ccfg (r', m') (tr++tr')
  | Cstep_while_f : forall md d ccfg e c,
      ccfg_com ccfg = Cwhile e c ->
      estep md d (ccfg_to_ecfg e ccfg) (Vnat 0) ->
      cstep md d ccfg (ccfg_reg ccfg, ccfg_mem ccfg) []
  .
  Hint Constructors cstep.

  Inductive cstep_n_chaos : csemantics :=
  | Nchaos_cstep : forall md d ccfg cterm t,
      cstep md d ccfg cterm t -> cstep_n_chaos md d ccfg cterm t
  | Nchaos_chaos : forall d ccfg cterm c' t' (HEncEq : enc_equiv (ccfg_com ccfg) c'),
      cstep Normal d (c', ccfg_reg ccfg, ccfg_mem ccfg) cterm t' ->
      cstep_n_chaos Normal d ccfg cterm
                    (Mem (ccfg_mem ccfg) :: AEnc (ccfg_com ccfg) c' HEncEq :: t').
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
  | Tref : type -> mode -> ref_type -> base_type
  | Tlambda (G: var -> option type) (p: sec_level) (md: mode) (G': var -> option type) : base_type
                                                                     
  with type : Type :=
       | Typ : base_type -> sec_level -> type.

  Definition context : Type := var -> option type.
  Parameter Loc_Contxt : location -> option (type * ref_type).
  
  Lemma var_in_dom_dec : forall (G : context) x, {exists t, G x = Some t} + {G x = None}.
  Proof.
    intros. destruct G. simpl. 
    left; now exists t. right; auto.
  Qed.
                     
  Lemma loc_in_dom_dec : forall l, {exists t rt, Loc_Contxt l = Some (t, rt)}
                                     + {Loc_Contxt l = None}.
  Proof.
    intros. simpl. destruct (Loc_Contxt l). destruct p.
    left; exists t; exists r; auto. right; auto.
  Qed.
      
  Definition forall_loc (P: location -> type -> ref_type -> Prop) : Prop :=
    forall l t rt, Loc_Contxt l = Some (t, rt) -> P l t rt.

  Definition forall_dom (G: context) (P: var -> type -> Prop) : Prop :=
       forall x t, G x = Some t -> P x t.

  Inductive type_le : type -> type -> Prop :=
  | Type_le : forall s1 s2 p1 p2,
      base_type_le s1 s2 ->
      sec_level_le p1 p2 ->
      type_le (Typ s1 p1) (Typ s2 p2)

  with base_type_le : base_type -> base_type -> Prop :=
  | Base_type_le_refl : forall s, base_type_le s s
  | Base_type_le_lambda : forall G1 G1' G2 G2' p1 p2 md,
      sec_level_le p2 p1 ->
      context_le G2 G1 ->
      context_le G1' G2' ->
      base_type_le (Tlambda G1 p1 md G1')
                   (Tlambda G2 p2 md G2')

  with context_le : context -> context -> Prop :=
  (* for right now, let's not assume that the domains are equal *)
  | Context_le : forall G1 G2,
      (forall x t,
          G1 x = Some t ->
          (* G2 must either not use the variable or have a greater type *)
          (G2 x = None \/ exists t', G2 x = Some t' /\ type_le t t')) ->
      (forall x t',
          G2 x = Some t' -> exists t, G1 x = Some t /\ type_le t t') ->
      context_le G1 G2.
  
  Lemma context_le_refl : forall G, context_le G G.
  Proof.
    intros. apply Context_le. intros. right; exists t; destruct t; auto.
    split; auto. apply Type_le. apply Base_type_le_refl. apply sec_level_le_refl.
    intros; exists t'; split; auto; destruct t'; auto.
    apply Type_le. apply Base_type_le_refl. apply sec_level_le_refl.
  Qed.
  
  Definition context_wt (G: context) (d: loc_mode) : Prop :=
    forall_loc (fun l t _ =>
                  let (_, p) := t in
                  (p = H -> exists i, d l = Encl i)).
  
  Definition is_var_low_context (G: context) : Prop :=
    forall_dom G (fun _ t => let (_, p) := t in p = L).

  Function loc_in_exp (e: exp) (l: location) : Prop :=
    match e with
    | Eloc l' => l = l'
    | Ederef e' => loc_in_exp e' l
    | Eadd e1 e2 => loc_in_exp e1 l \/ loc_in_exp e2 l
    | _ => False
    end.

  Definition exp_locs_immutable (e: exp) :=
    forall_subexp e (fun e =>
                       match e with
                       | Eloc n => set_In n (immutable_locs g0)
                       | _ => True
                       end).
      
  Inductive val_type : mode -> context -> loc_mode -> val -> type -> Prop :=
  | VTnat: forall md g d n q,
      val_type md g d (Vnat n) (Typ Tnat q) 
  | VTloc: forall md g d l md' t rt q,
      d l = md' ->
      Loc_Contxt l = Some (t, rt) ->
      val_type md g d (Vloc l) (Typ (Tref t md' rt) q)
  | VTlambda : forall md g d c p g' g'' q md0,
      com_type p md g' d c g'' ->
      val_type md0 g d (Vlambda md c) (Typ (Tlambda g' p md g'') q)
  | VTvar : forall md g d x r bt p v,
      g x = Some (Typ bt p) ->
      r x = v ->
      val_type md g d v (Typ bt p)
  | VTmem : forall md g d md' p rt q m l v bt,
      m l = v ->
      val_type md g d (Vloc l) (Typ (Tref (Typ bt p) md' rt) q) ->
      val_type md g d v (Typ bt (sec_level_join p q))
  | VTbinop : forall md g d n1 n2 p q op,
      val_type md g d (Vnat n1) (Typ Tnat p) ->
      val_type md g d (Vnat n2) (Typ Tnat q) ->
      val_type md g d (Vnat (op n1 n2)) (Typ Tnat (sec_level_join p q))

  with exp_type : mode -> context -> loc_mode -> exp -> type -> Prop :=
  | ETnat : forall md g d n,
      exp_type md g d (Enat n) (Typ Tnat (L))
  | ETvar : forall md g d x t,
      g x = Some t ->
      exp_type md g d (Evar x) t
  | ETloc : forall md g d l md' t rt,
      d l = md' ->
      Loc_Contxt l = Some (t, rt) ->
      exp_type md g d (Eloc l) (Typ (Tref t md' rt) (L))
  | ETderef : forall md g d e md' s p rt q,
      exp_type md g d e (Typ (Tref (Typ s p) md' rt) q) ->
      md' = Normal \/ md' = md ->
      exp_type md g d (Ederef e) (Typ s (sec_level_join p q))
  | ETlambda : forall md g d c p g' g'',
      com_type p md g' d c g''->
      exp_type md g d (Elambda md c) (Typ (Tlambda g' p md g'') (L))
  | ETadd : forall md g d e1 e2 p q,
      exp_type md g d e1 (Typ Tnat p) ->
      exp_type md g d e2 (Typ Tnat q) ->
      exp_type md g d (Eadd e1 e2) (Typ Tnat (sec_level_join p q))

  with com_type : sec_level -> mode -> context -> loc_mode -> com -> context -> Prop :=
  | CTskip : forall pc md g d,
      com_type pc md g d Cskip g
  | CTassign : forall pc md g d x e s p q vc',
      exp_type md g d e (Typ s p) ->
      q = sec_level_join p pc ->
      sec_level_le q (L) \/ md <> Normal ->
      vc' = (fun y => if y =? x then Some (Typ s q) else g y) ->
      com_type pc md g d (Cassign x e) (vc')
  | CTdeclassify : forall md g d x e s p vc',
      exp_type md g d e (Typ s p) ->
      exp_novars e ->
      exp_locs_immutable e ->
      vc' = (fun y => if y =? x then Some (Typ s (L)) else g y) ->
      com_type (L) md g d (Cdeclassify x e) (vc')
  | CToutput : forall pc md g d e l s p,
      exp_type md g d e (Typ s p) ->
      sec_level_le (sec_level_join p pc) l ->
      com_type pc md g d (Coutput e l) g
  | CTupdate : forall pc md g d e1 e2 s p md' q p',
      exp_type md g d e1 (Typ (Tref (Typ s p) md' Mut) q) ->
      exp_type md g d e2 (Typ s p') ->
      sec_level_le (sec_level_join (sec_level_join p' q) pc) p ->
      md' = Normal \/ md' = md ->
      com_type pc md g d (Cupdate e1 e2) g
  | Tifelse : forall pc md g d e c1 c2 pc' p g',
      com_type pc' md g d c1 g' ->
      com_type pc' md g d c2 g' ->
      exp_type md g d e (Typ Tnat p) ->
      sec_level_le (sec_level_join pc p) pc' ->
      sec_level_le p (L) \/ md <> Normal ->
      com_type pc md g d (Cif e c1 c2) g'
  | Tenclave : forall pc g d c i c' g',
      c = Cenclave i c' ->
      com_type pc (Encl i) g d c' g' ->
      is_var_low_context g' ->
      com_type pc Normal g d c g'
  | Twhile : forall pc md g d c e p pc',
      exp_type md g d e (Typ Tnat p) ->
      com_type pc' md g d c g ->
      sec_level_le (sec_level_join pc p) pc' ->
      sec_level_le p L \/ md <> Normal ->
      com_type pc md g d (Cwhile e c) g
  | Tseq : forall pc md g d c rest g' gn,
      com_type pc md g d c g' ->
      com_type pc md g' d (Cseq rest) gn ->
      com_type pc md g d (Cseq (c :: rest)) gn
  | Tseqnil : forall pc md g d,
      com_type pc md g d (Cseq []) g
  | Tcall : forall pc md G d e Gm Gp Gout q p,
      exp_type md G d e (Typ (Tlambda Gm p md Gp) q) ->
      sec_level_le (sec_level_join pc q) p ->
      context_le G Gm ->
      context_le Gp Gout ->
      forall_dom G (fun x t => (Gp x = None) -> Gout x = Some t) ->
      com_type pc md G d (Ccall e) Gout.

  Hint Constructors exp_type.
  Hint Constructors val_type.
  Hint Constructors com_type.
End Typing.

Section Axioms.
  Parameter minit : mem.
  
  Axiom No_Pointers : forall (m: mem) l l', m l <> Vloc l'.

  Definition meminit_wf minit d := forall l,
      match minit l with
      | Vlambda md c => forall Gm p Gp q rt,
                        Loc_Contxt l = Some (Typ (Tlambda Gm p md Gp) q, rt) ->
                        com_type p md Gm d c Gp
      | Vloc l => False
      | Vnat n => True
      end.

  Axiom wf_minit : forall d, meminit_wf minit d.

  Axiom Initial_State: forall d r' m',
      exists c md tr, cstep md d (c,reg_init,minit) (r',m') tr.

  (* These next three axioms should follow from the statement of initial state above *)
  Axiom Reg_Exp_Lambda : forall (r : reg) d x md c G Gm Gp p q,
      r x = Vlambda md c /\ G x = Some (Typ (Tlambda Gm p md Gp) q)
      <-> exists md', exp_type md' G d (Elambda md c)
                                 (Typ (Tlambda Gm p md Gp) L).

  Axiom Reg_Exp_Loc : forall (r : reg) d x l G s p md' rt q,
      r x = Vloc l /\ G x = Some (Typ (Tref (Typ s p) md' rt) q) <->
      exists md,
        exp_type md G d (Eloc l) (Typ (Tref (Typ s p) md' rt) L) /\ d l = md'.

  Axiom Mem_Exp_Lambda : forall (m : mem) d l md c G Gm Gp p q rt,
      m l = Vlambda md c /\ Loc_Contxt l = Some (Typ (Tlambda Gm p md Gp) q, rt) <->
      minit l = Vlambda md c \/
      (exists md',
          exp_type md' G d (Elambda md c) (Typ (Tlambda Gm p md Gp) L)).

  Axiom subsumption : forall pc1 pc2 md d G1 G1' G2 G2' c,
      com_type pc1 md G1 d c G1' ->
      sec_level_le pc2 pc1 ->
      context_le G2 G1 ->
      context_le G1' G2' ->
      (* XXX not including well-typed contexts *)
      com_type pc2 md G2 d c G2'.

End Axioms.





