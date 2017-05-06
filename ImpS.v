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
  | Tlambda (G: context) (U: set condition) (p: policy)
            (G': context) : base_type
                           
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

  Definition is_var_low_context (G: context) : Prop :=
    forall_var G (fun _ t => let (_, p) := t in policy_le p low).

  Inductive ederiv : Type :=
  | Ederiv_none : ederiv
  | Ederiv_e1 : type -> ederiv -> ederiv
  | Ederiv_e2: type -> ederiv -> type -> ederiv -> ederiv
  | Ederiv_prog : pderiv -> ederiv

  with cderiv : Type :=
  | Cderiv_none : cderiv
  | Cderiv_e1 : type -> ederiv -> cderiv
  | Cderiv_e2 : type -> ederiv -> type -> ederiv -> cderiv
  | Cderiv_e1_prog2 : type -> ederiv -> pderiv -> pderiv -> cderiv
  | Cderiv_e1_p_prog1 : type -> ederiv -> policy -> pderiv -> cderiv
  | Cderiv_e1_p_prog2 : type -> ederiv -> policy -> pderiv -> pderiv -> cderiv

  with pderiv : Type :=
  | Pderiv : list context -> list cderiv -> pderiv.
  
  Inductive all_loc_immutable : exp -> type -> ederiv -> context -> Prop :=
  | Inat : forall n t drv G,
      all_loc_immutable (Enat n) t drv G
  | Ivar : forall x t G drv,
      (forall t', var_context G x = Some t' -> type_ali t') ->
      all_loc_immutable (Evar x) t drv G
  | Ibinop : forall e1 e2 op t1 drv1 t2 drv2 t G,
      all_loc_immutable e1 t1 drv1 G ->
      all_loc_immutable e2 t2 drv2 G ->
      all_loc_immutable (Ebinop e1 e2 op) t (Ederiv_e2 t1 drv1 t2 drv2) G
  | Iloc : forall G l t drv,
      (forall t' rt,
          loc_context G (Not_cnd l) = Some (t', rt) ->
          rt = Immut /\ type_ali t') ->
      all_loc_immutable (Eloc (Not_cnd l)) t drv G
  | Ideref : forall G e t' drv t,
      all_loc_immutable e t' drv G ->
      all_loc_immutable (Ederef e) t (Ederiv_e1 t' drv) G
  | Ilambda : forall Gm U p Gp q c drv G,
      type_ali (Typ (Tlambda Gm U p Gp) q) ->
      all_loc_immutable (Elambda c) (Typ (Tlambda Gm U p Gp) q) drv G

  with type_ali : type -> Prop :=
  | TInat : forall p, type_ali (Typ Tnat p)
  | TIref : forall rt t p,
      rt = Immut ->
      type_ali t ->
      type_ali (Typ (Tref t rt) p)
  | TIlambda : forall Gm U p Gp q,
      (forall l t rt,
          loc_context Gm l = Some (t, rt) ->
          rt = Immut) ->
      (forall l t rt,
          loc_context Gm l = Some (t, rt) ->
          type_ali t) ->
      type_ali (Typ (Tlambda Gm U p Gp) q).
                     (*
  Definition all_loc_immutable (e: exp) (G: context) : Prop :=
    forall_subexp (fun e =>
                     match e with
                     | Eloc (Cnd _) => False
                     | Eloc (Not_cnd l) => forall t rt,
                         loc_context G (Not_cnd l) = Some (t, rt) -> rt = Immut
                     | Eisunset _ => False
                     | _ => True
                     end) e.
*)

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
  
  Definition mt := Cntxt (fun _ => None) (fun _ => None).
  
  Inductive exp_wt : context -> exp -> type -> ederiv -> Prop :=
  | STnat : forall G n,
      exp_wt G (Enat n) (Typ Tnat low) Ederiv_none
  | STcond : forall G x,
      exp_wt G (Eloc (Cnd x)) (Typ Tcond low) Ederiv_none
  | STvar : forall G x t,
      var_context G x = Some t ->
      exp_wt G (Evar x) t Ederiv_none
  | STloc : forall G x t rt,
      loc_context G (Not_cnd x) = Some (t, rt) ->
      exp_wt G (Eloc (Not_cnd x)) (Typ (Tref t rt) low) Ederiv_none
  | STderef : forall G e s p q rt drv,
      exp_wt G e (Typ (Tref (Typ s p) rt) q) drv ->
      exp_wt G (Ederef e) (Typ s (JoinP p q))
             (Ederiv_e1 (Typ (Tref (Typ s p) rt) q) drv)
  | STisunset : forall G x,
      exp_wt G (Eisunset x) (Typ Tnat low) Ederiv_none
  | STbinop : forall G e1 e2 p q op drv1 drv2,
      exp_wt G e1 (Typ Tnat p) drv1 ->
      exp_wt G e2 (Typ Tnat q) drv2 ->
      exp_wt G (Ebinop e1 e2 op) (Typ Tnat (JoinP p q))
             (Ederiv_e2 (Typ Tnat p) drv1 (Typ Tnat q) drv2)
  | STlambda : forall p G U c G' G'' drv,
      prog_wt p G' U c G'' drv ->
      exp_wt G (Elambda c) (Typ (Tlambda G' U p G'') low) (Ederiv_prog drv)

  with com_wt : policy -> context -> set condition -> com ->
                context -> cderiv -> Prop :=
  | STskip : forall pc G U,
      com_wt pc G U Cskip G Cderiv_none
  | STassign : forall pc U x e s p vc lc vc' drv,
      vc x = Some (Typ s (JoinP pc p)) ->
      exp_wt (Cntxt vc lc) e (Typ s p) drv ->
      ~pdenote (JoinP pc p) (LevelP T) ->
      vc' = update vc x (Some (Typ s (JoinP pc p))) ->
      com_wt pc (Cntxt vc lc) U (Cassign x e) (Cntxt vc' lc)
             (Cderiv_e1 (Typ s p) drv)
  | STdeclassify : forall U x e s q p vc lc vc' drv,
      vc x = Some (Typ s q) ->
      exp_wt (Cntxt vc lc) e (Typ s p) drv ->
      ~pdenote p (LevelP T) ->
      exp_novars e ->
      all_loc_immutable e (Typ s p) drv (Cntxt vc lc) ->
      vc' = update vc x (Some (Typ s low)) ->
      com_wt low (Cntxt vc lc) U (Cdeclassify x e) (Cntxt vc' lc)
             (Cderiv_e1 (Typ s p) drv)
  | STupdate : forall G e1 s p q e2 p' pc U drv1 drv2,
      exp_wt G e1 (Typ (Tref (Typ s p) Mut) q) drv1 ->
      exp_wt G e2 (Typ s p') drv2 ->
      policy_le (JoinP (JoinP p' q) pc) p ->
      ~pdenote p (LevelP T) ->
      ~pdenote p' (LevelP T) ->
      ~pdenote q (LevelP T) ->
      com_wt pc G U (Cupdate e1 e2) G
             (Cderiv_e2 (Typ (Tref (Typ s p) Mut) q) drv1
                        (Typ s p') drv2)
   | SToutput : forall pc G U e s p l p0 pc0 drv,
      exp_wt G e (Typ s p) drv ->
      ~pdenote p (LevelP T) ->
      pdenote p p0 ->
      pdenote pc pc0 ->
      sec_level_le (sec_level_join (cur p0 U) (cur pc0 U)) l ->
      com_wt pc G U (Coutput e l) G (Cderiv_e1 (Typ s p) drv)
  | STsetcnd : forall G U cnd,
      ~set_In cnd U ->
      com_wt low G U (Cset cnd) G Cderiv_none
  | STifunset : forall pc G U cnd c1 c2 G' drv pdrv1 pdrv2,
      exp_wt G (Eisunset cnd) (Typ Tnat low) drv ->
      prog_wt pc G (set_add Nat.eq_dec cnd U) c1 G' pdrv1 ->
      prog_wt pc G U c2 G' pdrv2 ->
      com_wt pc G U (Cif (Eisunset cnd) c1 c2) G'
             (Cderiv_e1_prog2 (Typ Tnat low) drv pdrv1 pdrv2)
  | STifelse : forall pc G U e c1 c2 pc' G' p drv pdrv1 pdrv2,
      exp_wt G e (Typ Tnat p) drv ->
      prog_wt pc' G U c1 G' pdrv1 ->
      prog_wt pc' G U c2 G' pdrv2 ->
      policy_le (JoinP pc p) pc' ->
      ~pdenote p (LevelP T) ->
      com_wt pc G U (Cif e c1 c2) G'
             (Cderiv_e1_p_prog2 (Typ Tnat p) drv pc' pdrv1 pdrv2)
  | STwhile : forall pc G U e c p pc' drv pdrv,
      exp_wt G e (Typ Tnat p) drv ->
      prog_wt pc' G U c G pdrv ->
      policy_le (JoinP pc p) pc' ->
      ~pdenote p (LevelP T) ->
      com_wt pc G U (Cwhile e c) G
             (Cderiv_e1_p_prog1 (Typ Tnat p) drv pc' pdrv)
  | STcall : forall pc G U e Gout Gplus Gminus p q drv,
      exp_wt G e (Typ (Tlambda Gminus U p Gplus) q) drv ->
      policy_le (JoinP pc q) p ->
      ~pdenote q (LevelP T) ->
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
             (Cderiv_e1 (Typ (Tlambda Gminus U p Gplus) q) drv)

  with prog_wt : policy -> context -> set condition -> prog ->
                 context -> pderiv -> Prop :=
  | STprog : forall pc G U coms (Gs: list context) drvs,
      length Gs = length coms + 1 ->
      length drvs = length coms ->
      nth 0 Gs mt = G ->
      (forall (i: nat),
          i < length coms ->
          com_wt pc (nth i Gs mt) U (nth i coms Cskip) (nth (i + 1) Gs mt)
                 (nth i drvs Cderiv_none)) ->
      prog_wt pc G U (Prog coms) (last Gs mt)
              (Pderiv Gs drvs).
End Typing.
