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
Require Import Logic.FunctionalExtensionality.
Require Import Common.
Require ImpE.
Require ImpS.

Module S := ImpS.
Module E := ImpE.

Section TypeTrans.
  Definition subdom {A B C: Type} (f: A -> option B) (g: A -> option C) :=
    forall x,
      match f x with
      | Some _ => exists y, g x = Some y
      | None => True
      end.
  
  Inductive btrans : S.base_type -> E.loc_mode -> E.base_type -> Prop :=
  | Btrans_nat : forall d, btrans S.Tnat d E.Tnat
  | Btrans_cond : forall d md, btrans S.Tcond d (E.Tcond md)
  | Btrans_ref : forall d s s' p md rt,
      btrans s d s' ->
      btrans (S.Tref (S.Typ s p) rt) d (E.Tref (E.Typ s' p) md rt)
  | Btrans_lambda : forall Gm G'm Gp G'p d U p Km Kp md,
      context_trans Gm d G'm ->
      context_trans Gp d G'p ->
      btrans (S.Tlambda Gm U p Gp) d (E.Tlambda G'm Km U p md G'p Kp)

  with ttrans : S.type -> E.loc_mode -> E.type -> Prop :=
  | Ttrans : forall s p s' d,
      btrans s d s' ->
      ttrans (S.Typ s p) d (E.Typ s' p)

  with context_trans : S.context -> E.loc_mode -> E.context -> Prop :=
  | Gtrans : forall G d G',
      subdom (S.var_context G) (E.var_context G') ->
      subdom (S.loc_context G) (E.loc_context G') ->
      subdom (E.var_context G') (S.var_context G) ->
      subdom (E.loc_context G') (S.loc_context G) ->
      S.forall_var G (fun x t =>
                        exists t',
                          ttrans t d t' /\ E.var_in_dom G' x t') ->
      S.forall_loc G (fun x t rt =>
                        exists t',
                          ttrans t d t' /\ E.loc_in_dom G' x t' rt) ->
      S.forall_loc G (fun x t rt =>
                        let (s, p) := t in
                        forall p0,
                          pdenote p p0 ->
                          policy0_le p0 (LevelP L) \/
                          d x <> E.Normal) ->
      context_trans G d G'.
End TypeTrans.

Section TransDef.
  Inductive exp_trans : S.context -> S.exp -> S.type -> S.ederiv ->
                        E.mode -> E.context -> E.loc_mode -> E.exp ->
                        E.type -> Prop :=
  | TRnat : forall sG n p md eG d drv,
      exp_trans sG (S.Enat n) (S.Typ S.Tnat p) drv
                md eG d (E.Enat n) (E.Typ E.Tnat p)
  | TRvar : forall sG x t t' eG md d drv,
      ttrans t d t' ->
      E.var_context eG x = Some t' ->
      exp_trans sG (S.Evar x) t drv
                md eG d (E.Evar x) t'
  | TRcnd : forall sG cnd p d md md' eG drv,
      d (Cnd cnd) = md' ->
      exp_trans sG (S.Eloc (Cnd cnd)) (S.Typ S.Tcond p) drv
                md eG d (E.Eloc (Cnd cnd)) (E.Typ (E.Tcond md') p)
  | TRisunset : forall sG cnd md' md eG d p drv,
      d (Cnd cnd) = md' ->
      md' = E.Normal \/ md = md' ->
      exp_trans sG (S.Eisunset cnd) (S.Typ S.Tnat p) drv
                md eG d (E.Eisunset cnd) (E.Typ E.Tnat p)
  | TRloc : forall sG l t rt (q: sec_level) t' md' md eG d q drv,
      ttrans (S.Typ (S.Tref t rt) q) d (E.Typ (E.Tref t' md' rt) q) ->
      E.loc_context eG (Not_cnd l) = Some (t', rt) ->
      d (Not_cnd l) = md' ->
      exp_trans sG (S.Eloc (Not_cnd l)) (S.Typ (S.Tref t rt) q) drv
                md eG d (E.Eloc (Not_cnd l)) (E.Typ (E.Tref t' md' rt) q)
  | TRderef : forall sG (eG: E.context) e s p s' q md eG d e' md' rt drv,
      exp_trans sG e (S.Typ (S.Tref (S.Typ s p) rt) q) drv
                md eG d e' (E.Typ (E.Tref (E.Typ s' p) md' rt) q) ->
      md' = E.Normal \/ md = md' ->
      exp_trans sG (S.Ederef e) (S.Typ s (JoinP p q))
                (S.Ederiv_single (S.Typ (S.Tref (S.Typ s p) rt) q) drv)
                md eG d (E.Ederef e')
                (E.Typ s' (JoinP p q))
  | TRop : forall sG op e1 s p s' md eG d e1' e2 q e2' drv1 drv2,
      exp_trans sG e1 (S.Typ s p) drv1 md eG d e1' (E.Typ s' p) ->
      exp_trans sG e2 (S.Typ s q) drv2 md eG d e2' (E.Typ s' q) ->
      exp_trans sG (S.Ebinop e1 e2 op)
                (S.Typ s (JoinP p q))
                (S.Ederiv_double (S.Typ s p) drv1 (S.Typ s q) drv2)
                md eG d (E.Ebinop e1' e2' op)
                (E.Typ s' (JoinP p q))
  | TRlambda : forall sG sGm sGp (U: set condition) p d eG eGm Km
                      md eGp Kp c c' q drv,
      btrans (S.Tlambda sGm U p sGp) d (E.Tlambda eGm Km U p md eGp Kp) ->
      prog_trans p sGm U c sGp md eGm Km d c' eGp Kp ->
      E.is_var_low_context eGp \/ md <> E.Normal ->
      exp_trans sG (S.Elambda c) (S.Typ (S.Tlambda sGm U p sGp) q) drv
                md eG d (E.Elambda md c')
                (E.Typ (E.Tlambda eGm Km U p md eGp Kp) q)

  with com_trans : policy -> S.context -> set condition -> S.com ->
                   S.context -> E.mode -> E.context -> set E.enclave ->
                   E.loc_mode -> E.com -> E.context -> set E.enclave ->
                   Prop :=
  | TRskip : forall pc sG eG U md K d,
      S.com_wt pc sG U S.Cskip sG ->     
      context_trans sG d eG ->
      E.mode_alive md K ->
      com_trans pc sG U S.Cskip sG
                md eG K d E.Cskip eG K
  | TRassign : forall pc sG sG' U x e e' md eG K d eG' q s s' drv,
      S.com_wt pc sG U (S.Cassign x e) sG' ->
      context_trans sG d eG ->
      exp_trans sG e (S.Typ s q) drv md eG d e' (E.Typ s' q) ->
      policy_le (JoinP pc q) (liftp (LevelP L)) \/ md <> E.Normal ->
      E.mode_alive md K ->
      eG' = E.Cntxt (update (E.var_context eG) x (Some (E.Typ s' (JoinP pc q))))
                    (E.loc_context eG) ->
      sG' = S.Cntxt (update (S.var_context sG) x (Some (S.Typ s (JoinP pc q))))
                    (S.loc_context sG) ->
      com_trans pc sG U (S.Cassign x e) sG'
                md eG K d (E.Cassign x e') eG' K
      
  with prog_trans : policy -> S.context -> set condition -> S.prog ->
                    S.context -> E.mode -> E.context -> set E.enclave ->
                    E.loc_mode -> E.com -> E.context -> set E.enclave ->
                    Prop :=
  | TRprog : forall p sGm U c sGp md eGm Km d c' eGp Kp,
      prog_trans p sGm U c sGp md eGm Km d c' eGp Kp.     

  Scheme exp_trans_mut := Induction for exp_trans Sort Prop
  with com_trans_mut := Induction for com_trans Sort Prop
  with prog_trans_mut := Induction for prog_trans Sort Prop.
End TransDef.

Section TransLemmas.
  Hint Constructors btrans ttrans context_trans.
  Lemma trans_exp_ttrans : forall sG e t md eG d e' t' drv,
      exp_trans sG e t drv md eG d e' t' ->
      ttrans t d t'.
  Proof.
    intros. induction H; eauto.
    - inversion IHexp_trans. inversion H4. now constructor.
    - inversion IHexp_trans1. now constructor.
  Qed.

  Lemma trans_exp_btrans : forall sG e s p md eG d e' s' q drv,
      exp_trans sG e (S.Typ s p) drv md eG d e' (E.Typ s' q) ->
      btrans s d s'.
  Proof.
    intros. apply trans_exp_ttrans in H. now inversion H.
  Qed.
End TransLemmas.

Section TransProof.
  Hint Constructors E.exp_type E.com_type.

  Lemma com_trans_sound : forall pc sG U c sG' md eG K d c' eG' K',
      S.com_wt pc sG U c sG' ->
      com_trans pc sG U c sG' md eG K d c' eG' K' ->
      E.com_type pc md eG K U d c' eG' K'.
  Proof.
    intros.
    induction H0 using com_trans_mut with
    (P:=fun sG e t drv md eG d e' t'
            (et:exp_trans sG e t drv md eG d e' t') =>
          S.exp_wt sG e t drv ->
          E.exp_type md eG d e' t')
    (P1:=fun pc sG U c sG' md eG K d c' eG' K'
            (ct:prog_trans pc sG U c sG' md eG K d c' eG' K') =>
          S.prog_wt pc sG U c sG' ->
          E.com_type pc md eG K U d c' eG' K'); eauto.
    1-7: inversion H; subst; eauto.
    (* Expressions *)
    - eapply E.ETunset; intuition.
    - eapply E.ETderef with (md':=md') (rt:=rt); intuition.
    - eapply trans_exp_btrans in e.
      inversion e. subst. constructor; eauto.
    (* Commands. *)
  Admitted.
  
End TransProof.