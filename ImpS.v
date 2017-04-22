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
  | Elambda : prog -> exp
                                   
  with com : Type :=
  | Cskip : com
  | Cassign : var -> exp -> com
  | Cdeclassify : var -> exp -> com
  | Cupdate : exp -> exp -> com
  | Coutput : exp -> sec_level -> com
  | Ccall : exp -> com
  | Cset : condition -> com
  | Cif : exp -> prog -> prog -> com
  | Cwhile : exp -> prog -> com

  with prog: Type :=
  | Prog : list com -> prog.

  Section Induction.
    Variable P : com -> Prop.
    Variable P0 : exp -> Prop.
    Variable P1 : prog -> Prop.

    Hypothesis Enat_case : forall n, P0 (Enat n).
    Hypothesis Evar_case : forall x, P0 (Evar x).
    Hypothesis Ebinop_case : forall e1 e2 op,
        P0 e1 -> P0 e2 -> P0 (Ebinop e1 e2 op).
    Hypothesis Eloc_case : forall l, P0 (Eloc l).
    Hypothesis Ederef_case : forall e,
        P0 e -> P0 (Ederef e).
    Hypothesis Eisunset_case : forall cnd, P0 (Eisunset cnd).
    Hypothesis Elambda_case : forall c,
        P1 c -> P0 (Elambda c).
    
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
    Hypothesis Cset_case : forall cnd, P (Cset cnd).
    Hypothesis Cif_case : forall e c1 c2,
        P0 e -> P1 c1 -> P1 c2 -> P (Cif e c1 c2).
    Hypothesis Cwhile_case : forall e c,
        P0 e -> P1 c -> P (Cwhile e c).

    Hypothesis Prog_case : forall coms,
        Forall P coms -> P1 (Prog coms).

    Fixpoint com_ind' (c: com) : P c :=
      match c with
      | Cskip => Cskip_case
      | Cassign x e => Cassign_case x e (exp_ind' e)
      | Cdeclassify x e => Cdeclassify_case x e (exp_ind' e)
      | Cupdate e1 e2 => Cupdate_case e1 e2 (exp_ind' e1) (exp_ind' e2)
      | Coutput e sl => Coutput_case e sl (exp_ind' e)
      | Ccall e => Ccall_case e (exp_ind' e)
      | Cset cnd => Cset_case cnd
      | Cif e c1 c2 =>
        Cif_case e c1 c2 (exp_ind' e) (prog_ind' c1) (prog_ind' c2)
      | Cwhile e c => Cwhile_case e c (exp_ind' e) (prog_ind' c)
      end

    with exp_ind' (e: exp) : P0 e :=
      match e with
      | Enat n => Enat_case n
      | Evar x => Evar_case x
      | Ebinop e1 e2 op => Ebinop_case e1 e2 op (exp_ind' e1) (exp_ind' e2)
      | Eloc l => Eloc_case l
      | Ederef e => Ederef_case e (exp_ind' e)
      | Eisunset cnd => Eisunset_case cnd
      | Elambda c => Elambda_case c (prog_ind' c)
      end

    with prog_ind' (p: prog) : P1 p :=
      match p with
      | Prog coms =>
        Prog_case coms
                  ((fix com_list_ind (coms: list com) : Forall P coms :=
                      match coms with
                      | [] => Forall_nil P
                      | h :: t => Forall_cons h (com_ind' h) (com_list_ind t)
                      end) coms)
      end.                                                
  End Induction.

  Inductive val : Type :=
  | Vlambda : com -> val
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
  | FAlambda : forall c,
      P (Elambda c) ->
      forall_subexp'' P c ->
      forall_subexp P (Elambda c)

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
      forall_subexp'' P c1 ->
      forall_subexp'' P c2 ->
      forall_subexp' P (Cif e c1 c2)
  | FAwhile : forall e c,
      forall_subexp P e ->
      forall_subexp'' P c ->
      forall_subexp' P (Cwhile e c)

  with forall_subexp'' (P: exp -> Prop) : prog -> Prop :=
  | FAprog : forall coms,
      Forall (fun c => forall_subexp' P c) coms ->
      forall_subexp'' P (Prog coms).

  Definition exp_novars : exp -> Prop :=
    forall_subexp (fun e => match e with
                            | Evar _ => False
                            | _ => True
                            end).
End Syntax.

Section Typing.
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

  Definition all_loc_immutable (e: exp) (G: context) : Prop :=
    forall_subexp (fun e =>
                     match e with
                     | Eloc (Cnd _) => False
                     | Eloc (Not_cnd l) => forall t rt,
                         loc_context G (Not_cnd l) = Some (t, rt) -> rt = Immut
                     | Eisunset _ => False
                     | _ => True
                     end) e.

  Inductive type_le : type -> type -> Prop :=
  | Type_le : forall s1 s2 p1 p2,
      base_type_le s1 s2 ->
      policy_le p1 p2 ->
      type_le (Typ s1 p1) (Typ s2 p2)

  with base_type_le : base_type -> base_type -> Prop :=
  | Base_type_le_refl : forall s, base_type_le s s
  | Base_type_le_lambda : forall G1 G1' G2 G2' U p1 p2,
      policy_le p2 p1 ->
      context_le G2 G1 ->
      context_le G1' G2' ->
      base_type_le (Tlambda G1 U p1 G1')
                   (Tlambda G2 U p2 G2')

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

  (* XXX need this for using List.nth... maybe better option *)
  Definition mt := Cntxt (fun _ => None) (fun _ => None).
  
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
      prog_wt p G' U c G'' ->
      exp_wt G (Elambda c) (Typ (Tlambda G' U p G'') (LevelP L))
  | STbinop : forall G e1 e2 p q op,
      exp_wt G e1 (Typ Tnat p) ->
      exp_wt G e2 (Typ Tnat q) ->
      exp_wt G (Ebinop e1 e2 op) (Typ Tnat (policy_join p q))

  with com_wt : sec_policy -> context -> set condition -> com ->
                context -> Prop :=
  | STskip : forall pc G U,
      com_wt pc G U Cskip G
  | STassign : forall pc U x e s p q vc lc vc',
      vc x = Some (Typ s q) ->
      exp_wt (Cntxt vc lc) e (Typ s p) ->
      policy_join pc p <> LevelP T ->
      vc' = (fun y => if y =? x
                      then Some (Typ s (policy_join pc p))
                      else vc y) ->
      com_wt pc (Cntxt vc lc) U (Cassign x e) (Cntxt vc' lc)
  | STdeclassify : forall U x e s q p vc lc vc',
      vc x = Some (Typ s q) ->
      exp_wt (Cntxt vc lc) e (Typ s p) ->
      p <> LevelP T ->
      exp_novars e ->
      all_loc_immutable e (Cntxt vc lc) ->
      vc' = (fun y => if y =? x
                      then Some (Typ s (LevelP L))
                      else vc y) ->
      com_wt (LevelP L) (Cntxt vc lc) U (Cdeclassify x e) (Cntxt vc' lc)
  | STupdate : forall G e1 s p q e2 p' pc U,
      exp_wt G e1 (Typ (Tref (Typ s p) Mut) q) ->
      exp_wt G e2 (Typ s p') ->
      policy_le (policy_join (policy_join p' q) pc) p ->
      p <> LevelP T ->
      p' <> LevelP T ->
      q <> LevelP T ->
      com_wt pc G U (Cupdate e1 e2) G
  | STsetcnd : forall G U cnd,
      ~set_In cnd U ->
      com_wt (LevelP L) G U (Cset cnd) G
  | SToutput : forall pc G U e s p l,
      exp_wt G e (Typ s p) ->
      p <> LevelP T ->
      sec_level_le (sec_level_join (cur p U) (cur pc U)) l ->
      com_wt pc G U (Coutput e l) G
  | STifunset : forall pc G U cnd c1 c2 G',
      exp_wt G (Eisunset cnd) (Typ Tnat (LevelP L)) ->
      prog_wt pc G (set_add Nat.eq_dec cnd U) c1 G' ->
      prog_wt pc G U c2 G' ->
      com_wt pc G U (Cif (Eisunset cnd) c1 c2) G'
  | STifelse : forall pc G U e c1 c2 pc' G' p,
      (forall cnd, e <> Eisunset cnd) ->
      exp_wt G e (Typ Tnat p) ->
      prog_wt pc' G U c1 G' ->
      prog_wt pc' G U c2 G' ->
      policy_le (policy_join pc p) pc' ->
      p <> LevelP T ->
      com_wt pc G U (Cif e c1 c2) G'
  | STwhile : forall pc G U e c p pc',
      exp_wt G e (Typ Tnat p) ->
      prog_wt pc' G U c G ->
      policy_le (policy_join pc p) pc' ->
      p <> LevelP T ->
      com_wt pc G U (Cwhile e c) G
  | STcall : forall pc G U e Gout Gplus Gminus p q,
      exp_wt G e (Typ (Tlambda Gminus U p Gplus) q) ->
      policy_le (policy_join pc q) p ->
      q <> LevelP T ->
      forall_dom Gminus
                 (fun x t => exists t', var_in_dom G x t' /\ type_le t' t)
                 (fun l t rt => exists t',
                      loc_in_dom G l t' rt /\ type_le t' t) ->
      forall_dom Gplus
                 (fun x t => exists t', var_in_dom Gout x t' /\ type_le t' t)
                 (fun l t rt => exists t',
                      loc_in_dom Gout l t' rt /\ type_le t' t) ->
      forall_dom G
                 (fun x t =>
                    (forall t', ~var_in_dom Gplus x t') ->
                    var_in_dom Gout x t)
                 (fun l t rt =>
                    (forall t' rt', ~loc_in_dom Gplus l t' rt') ->
                    loc_in_dom Gout l t rt) ->
      com_wt pc G U (Ccall e) Gout

  with prog_wt : sec_policy -> context -> set condition -> prog ->
                 context -> Prop :=
  | STprog : forall pc G U coms (Gs: list context),
      (* There might be a better way to write this with a function
         that recurses over the list of commands. *)
      length Gs = length coms + 1 ->
      nth 0 Gs mt = G ->
      (forall (i: nat),
          i < length coms ->
          com_wt pc (nth i Gs mt) U (nth i coms Cskip) (nth (i + 1) Gs mt)) ->
      prog_wt pc G U (Prog coms) (nth (length coms) Gs mt).

  Scheme exp_wt_mut := Induction for exp_wt Sort Prop
  with com_wt_mut := Induction for com_wt Sort Prop
  with prog_wt_mut := Induction for prog_wt Sort Prop.
End Typing.
