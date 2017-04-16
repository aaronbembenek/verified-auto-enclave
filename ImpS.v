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

Section Syntax.
  Inductive exp : Type :=
  | Enat : nat -> exp
  | Evar : var -> exp
  | Ebinop : exp -> exp -> (nat -> nat -> nat) -> exp
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

  Function forall_subexp (e: exp) (P: exp -> Prop) : Prop :=
    P e /\
    match e with
    | Ebinop e1 e2 _ => forall_subexp e1 P /\ forall_subexp e2 P
    | Ederef e' => forall_subexp e' P
    | Elambda c => forall_subexp' c P
    | _ => True
    end
  with forall_subexp' (c: com) (P: exp -> Prop) : Prop :=
    match c with
    | Cassign _ e => forall_subexp e P
    | Cdeclassify _ e => forall_subexp e P
    | Cupdate e1 e2 => forall_subexp e1 P /\ forall_subexp e2 P
    | Ccall e => forall_subexp e P
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

Section Typing.
  Inductive ref_type : Set :=
  | Mut
  | Immut.

  (* FIXME: we might want to change contexts to be defined in terms of
     finite maps instead of functions. *)
  Inductive base_type : Type :=
  | Tnat : base_type
  | Tcond : base_type
  | Tref : type -> ref_type -> base_type
  | Tlambda (G: context) (U: set condition) (p: sec_policy)
            (G': context) : base_type
                           
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

  Inductive exp_wt : context -> exp -> type -> Prop :=
  | STnat : forall G n,
      exp_wt G (Enat n) (Typ Tnat (LevelP L))
  | STcond : forall G x,
      exp_wt G (Eloc (Cnd x)) (Typ Tcond (LevelP L))
  | STvar : forall G x t,
      var_context G x = Some t ->
      exp_wt G (Evar x) t
  | STloc : forall G x t rt,
      loc_context G (Not_cnd x) = Some (t, rt) ->
      exp_wt G (Eloc (Not_cnd x)) (Typ (Tref t rt) (LevelP L))
  | STderef : forall G e s p q rt,
      exp_wt G e (Typ (Tref (Typ s p) rt) q) ->
      exp_wt G (Ederef e) (Typ s (policy_join p q))
  | STisunset : forall G x,
      exp_wt G (Eisunset x) (Typ Tnat (LevelP L))
  | STlambda : forall p G U c G' G'',
      com_wt p G' U c G'' ->
      exp_wt G (Elambda c) (Typ (Tlambda G' U p G'') (LevelP L))
  | STbinop : forall G e1 e2 p q op,
      exp_wt G e1 (Typ Tnat p) ->
      exp_wt G e1 (Typ Tnat q) ->
      exp_wt G (Ebinop e1 e2 op) (Typ Tnat (policy_join p q))

  with com_wt : sec_policy -> context -> set condition -> com ->
                context -> Prop :=
  .
End Typing.
