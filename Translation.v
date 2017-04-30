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

  Inductive process_seq_output (coms: list E.com) (md0: E.mode)
            (mds: list E.mode) (Gs: list E.context) (Ks: list (set E.enclave)):
    list E.com -> list E.context -> list (set E.enclave) -> Prop :=
  | PSO0 :
      Forall (fun md => md = md0) mds ->
      process_seq_output coms md0 mds Gs Ks coms Gs Ks
  | PSO1 : forall mds' coms' coms'' c G1 G2 Gs' K1 K2 Ks' Gs'' Ks'',
      md0 = E.Normal ->
      mds = E.Normal :: mds' ->
      coms = c :: coms' ->
      Gs = G1 :: G2 :: Gs' ->
      Ks = K1 :: K2 :: Ks' ->
      process_seq_output coms' md0 mds' (G2 :: Gs') (K2 :: Ks')
                         coms'' (G2 :: Gs'') (K2 :: Ks'') ->
      process_seq_output coms md0 mds Gs Ks
                         (c :: coms'') (G1 :: G2 :: Gs'') (K1 :: K2 :: Ks'')
  | PSO2: forall j mds1 mds2 c coms' coms1 coms2 Gs1 Gs2 Ks1 Ks2
                 Gs2' Ks2' K1 K2 G1 G2,
      md0 = E.Normal ->
      mds = mds1 ++ mds2 ->
      Forall (fun md => md = E.Encl j) mds ->
      nth 0 mds2 E.Normal <> E.Encl j ->
      coms = coms1 ++ coms2 ->
      length coms1 = length mds1 ->
      Gs = G1 :: Gs1 ++ G2 :: Gs2 ->
      length Gs1 = length mds1 ->
      Ks = K1 :: Ks1 ++ K2 :: Ks2 ->
      length Ks1 = length mds1 ->
      c = E.Cenclave j (E.Cseq coms1) ->
      process_seq_output coms2 md0 mds2 (G2 :: Gs2) (K2 :: Ks2)
                         coms' (G2 :: Gs2') (K2 :: Ks2') ->
      process_seq_output coms md0 mds Gs Ks
                         (c :: coms') (G1 :: G2 :: Gs2') (K1 :: K2 :: Ks2').
  (* XXX need a base case for [] *)
  
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
                (S.Ederiv_e1 (S.Typ (S.Tref (S.Typ s p) rt) q) drv)
                md eG d (E.Ederef e')
                (E.Typ s' (JoinP p q))
                
  | TRop : forall sG op e1 s p s' md eG d e1' e2 q e2' drv1 drv2,
      exp_trans sG e1 (S.Typ s p) drv1 md eG d e1' (E.Typ s' p) ->
      exp_trans sG e2 (S.Typ s q) drv2 md eG d e2' (E.Typ s' q) ->
      exp_trans sG (S.Ebinop e1 e2 op)
                (S.Typ s (JoinP p q))
                (S.Ederiv_e2 (S.Typ s p) drv1 (S.Typ s q) drv2)
                md eG d (E.Ebinop e1' e2' op)
                (E.Typ s' (JoinP p q))
                
  | TRlambda : forall sG sGm sGp (U: set condition) p d eG eGm Km
                      md eGp Kp c c' q pdrv,
      btrans (S.Tlambda sGm U p sGp) d (E.Tlambda eGm Km U p md eGp Kp) ->
      prog_trans p sGm U c sGp pdrv md eGm Km d c' eGp Kp ->
      E.is_var_low_context eGp \/ md <> E.Normal ->
      exp_trans sG (S.Elambda c) (S.Typ (S.Tlambda sGm U p sGp) q)
                (S.Ederiv_prog pdrv)
                md eG d (E.Elambda md c')
                (E.Typ (E.Tlambda eGm Km U p md eGp Kp) q)

  with com_trans : policy -> S.context -> set condition -> S.com ->
                   S.context -> S.cderiv ->
                   E.mode -> E.context -> set E.enclave ->
                   E.loc_mode -> E.com -> E.context -> set E.enclave ->
                   Prop :=
  | TRskip : forall pc sG eG U md K d drv,  
      context_trans sG d eG ->
      E.mode_alive md K ->
      com_trans pc sG U S.Cskip sG drv
                md eG K d E.Cskip eG K
                
  | TRassign : forall pc sG sG' U x e e' md eG K d eG' q s s' drv,
      context_trans sG d eG ->
      exp_trans sG e (S.Typ s q) drv md eG d e' (E.Typ s' q) ->
      policy_le (JoinP pc q) (liftp (LevelP L)) \/ md <> E.Normal ->
      E.mode_alive md K ->
      eG' = E.Cntxt (update (E.var_context eG) x (Some (E.Typ s' (JoinP pc q))))
                    (E.loc_context eG) ->
      sG' = S.Cntxt (update (S.var_context sG) x (Some (S.Typ s (JoinP pc q))))
                    (S.loc_context sG) ->
      com_trans pc sG U (S.Cassign x e) sG' (S.Cderiv_e1 (S.Typ s q) drv)
                md eG K d (E.Cassign x e') eG' K
                
  | TRdeclassify : forall pc sG sG' U x e e' md eG K d eG' q s s' drv,
      context_trans sG d eG ->
      exp_trans sG e (S.Typ s q) drv md eG d e' (E.Typ s' q) ->
      policy_le (JoinP pc q) (liftp (LevelP L)) \/ md <> E.Normal ->
      E.mode_alive md K ->
      eG' = E.Cntxt (update (E.var_context eG) x (Some (E.Typ s' low)))
                    (E.loc_context eG) ->
      sG' = S.Cntxt (update (S.var_context sG) x (Some (S.Typ s low)))
                    (S.loc_context sG) ->
      com_trans pc sG U (S.Cdeclassify x e) sG' (S.Cderiv_e1 (S.Typ s q) drv)
                md eG K d (E.Cdeclassify x e') eG' K
                
  | TRupdate : forall pc sG U e1 e2 md eG K d e1' e2'
                      p q p' s s' drv1 drv2 md' rt,
      context_trans sG d eG ->
      exp_trans sG e1 (S.Typ (S.Tref (S.Typ s p) rt) q) drv1
                md eG d e1' (E.Typ (E.Tref (E.Typ s' p) md' rt) q) ->
      exp_trans sG e2 (S.Typ s p') drv2
                md eG d e2' (E.Typ s' p') ->
      md' = E.Normal \/ md = md' ->
      E.mode_alive md K ->
      com_trans pc sG U (S.Cupdate e1 e2) sG
                (S.Cderiv_e2 (S.Typ (S.Tref (S.Typ s p) rt) q) drv1
                             (S.Typ s p') drv2)
                md eG K d (E.Cupdate e1' e2') eG K
                
  | TRoutput : forall pc sG U e md eG K d e' p l drv s' s,
      exp_trans sG e (S.Typ s p) drv
                md eG d e' (E.Typ s' p) ->
      context_trans sG d eG ->
      E.mode_alive md K ->
      com_trans pc sG U (S.Coutput e l) sG (S.Cderiv_e1 (S.Typ s p) drv)
                md eG K d (E.Coutput e' l) eG K
                
  | TRset : forall sG U cnd md' md eG K d drv,
      d (Cnd cnd) = md' ->
      md' = E.Normal \/ md = md' ->
      E.mode_alive md K ->
      com_trans low sG U (S.Cset cnd) sG drv
                md eG K d (E.Cset cnd) eG K

  | TRifunset : forall pc sG U cnd c1 c2 sG' md eG K d c1' c2' eG' K'
                       pdrv1 pdrv2 drv,
      context_trans sG d eG ->
      exp_trans sG (S.Eisunset cnd) (S.Typ S.Tnat low) drv
                md eG d (E.Eisunset cnd) (E.Typ E.Tnat low) ->
      prog_trans pc sG (set_add (Nat.eq_dec) cnd U) c1 sG' pdrv1
                 md eG K d c1' eG' K' ->
      prog_trans pc sG U c2 sG' pdrv2
                 md eG K d c2' eG' K' ->
      E.mode_alive md K ->
      md <> E.Normal ->
      com_trans pc sG U (S.Cif (S.Eisunset cnd) c1 c2) sG'
                (S.Cderiv_e1_prog2 (S.Typ S.Tnat low) drv pdrv1 pdrv2)
                md eG K d (E.Cif (E.Eisunset cnd) c1' c2') eG' K'

  | TRifelse : forall pc sG U e e' c1 c2 c1' c2' sG'
                      md eG K d eG' K' drv p pc' pdrv1 pdrv2,
      context_trans sG d eG ->
      exp_trans sG e (S.Typ S.Tnat p) drv md eG d e' (E.Typ E.Tnat p) ->
      prog_trans pc' sG U c1 sG' pdrv1
                 md eG K d c1' eG' K' ->
      prog_trans pc' sG U c2 sG' pdrv2
                 md eG K d c2' eG' K' ->
      policy_le (JoinP pc p) pc' ->
      (S.is_var_low_context sG' /\ policy_le p low) \/ md <> E.Normal ->
      E.mode_alive md K ->
      com_trans pc sG U (S.Cif e c1 c2) sG'
                (S.Cderiv_e1_p_prog2 (S.Typ S.Tnat p) drv pc' pdrv1 pdrv2)
                md eG K d (E.Cif e' c1' c2') eG' K'

  | TRwhile : forall pc sG U e e' c c' pdrv
                     md eG K d drv p pc',
      context_trans sG d eG ->
      exp_trans sG e (S.Typ S.Tnat p) drv md eG d e' (E.Typ E.Tnat p) ->
      prog_trans pc' sG U c sG pdrv md eG K d c' eG K ->
      (S.is_var_low_context sG /\ policy_le p low) \/ md <> E.Normal ->
      E.mode_alive md K ->
      policy_le pc pc' ->
      com_trans pc sG U (S.Cwhile e c) sG
                (S.Cderiv_e1_p_prog1 (S.Typ S.Tnat p) drv pc' pdrv)
                md eG K d (E.Cwhile e' c') eG K

  | TRcall : forall pc sG U e sGout sGminus sGplus
                    md e' d p K K' eG eGout eGminus eGplus drv q,
      context_trans sG d eG ->
      context_trans sGout d eGout ->
      exp_trans sG e (S.Typ (S.Tlambda sGminus U p sGplus) q) drv
                md eG d e'
                (E.Typ (E.Tlambda eGminus K U p md eGplus K') q) ->
      E.forall_dom eGminus
                 (fun x t => exists t', E.var_in_dom eG x t' /\ E.type_le t' t)
                 (fun l t rt => exists t',
                      E.loc_in_dom eG l t' rt /\ E.type_le t' t) ->
      E.forall_dom eGplus
                 (fun x t => exists t', E.var_in_dom eGout x t' /\ E.type_le t' t)
                 (fun l t rt => exists t',
                      E.loc_in_dom eGout l t' rt /\ E.type_le t' t) ->
      E.forall_dom eG
                 (fun x t =>
                    (forall t', ~E.var_in_dom eGplus x t') ->
                    E.var_in_dom eGout x t)
                 (fun l t rt =>
                    (forall t' rt', ~E.loc_in_dom eGplus l t' rt') ->
                    E.loc_in_dom eGout l t rt) ->
      E.mode_alive md K ->
      U = nil \/ md <> E.Normal ->
      com_trans pc sG U (S.Ccall e) sGout
                (S.Cderiv_e1 (S.Typ (S.Tlambda sGminus U p sGplus) q) drv)
                md eG K d (E.Ccall e') eGout K'
      
  with prog_trans : policy -> S.context -> set condition -> S.prog ->
                    S.context -> S.pderiv ->
                    E.mode -> E.context -> set E.enclave ->
                    E.loc_mode -> E.com -> E.context -> set E.enclave ->
                    Prop :=
  | TRprog : forall d sGs eGs drvs mds Ks (*K's*) coms coms' coms'' md0
                    U pc eGs' mds' Ks',
      length eGs = length coms + 1 ->
      length sGs = length coms + 1 ->
      length mds = length coms + 1 ->
      length Ks = length coms + 1 ->
      length coms' = length coms ->
      (forall (i: nat),
          i < length eGs ->
          context_trans (nth i sGs S.mt) d (nth i eGs E.mt)) ->
      (forall (i: nat),
          i < length coms ->
          com_trans pc (nth i sGs S.mt) U (nth i coms S.Cskip)
                    (nth (i + 1) sGs S.mt) (nth i drvs S.Cderiv_none)
                    (nth i mds' E.Normal) (nth i eGs E.mt)
                    (nth i Ks []) d (nth i coms' E.Cskip)
                    (nth (i + 1) eGs E.mt)
                    (nth (i + 1) Ks [])) ->
      (forall (i: nat),
          i < length mds' ->
          (nth i mds' E.Normal <> E.Normal /\
           nth i mds' E.Normal <> nth (i + 1) mds' E.Normal ->
           E.is_var_low_context (nth i eGs E.mt))) ->
      mds = md0 :: mds' ->
      md0 = E.Normal \/
      (forall i, i < length mds -> (nth i mds E.Normal) = md0) ->
      U = [] \/ md0 <> E.Normal ->
      (*sG0 = nth 0 sGs S.mt ->
      sGn = last sGs S.mt ->
      eG0 = nth 0 eGs E.mt ->
      K0 = nth 0 Ks [] ->
      eGn = last eGs' E.mt ->
      Kn = last Ks [] -> *)
      (*process_seq_output coms' md0 (skipn 1 mds) eGs coms'' eGs' -> *)
      process_seq_output coms' md0 mds' eGs Ks coms'' eGs' Ks' ->
      prog_trans pc (nth 0 sGs S.mt) U (S.Prog coms) (last sGs S.mt)
                 (S.Pderiv sGs drvs)
                 md0 (nth 0 eGs' E.mt) (nth 0 Ks' []) d (E.Cseq coms'')
                 (last eGs' E.mt) (last Ks' []).

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

  Hint Constructors E.forall_subexp E.forall_subexp'.
       
  Lemma trans_pres_exp_novars : forall e sG t drv md eG d e' t',
      exp_trans sG e t drv md eG d e' t' ->
      S.exp_novars e ->
      E.exp_novars e'.
  Proof.
    unfold S.exp_novars.
    remember (fun e : S.exp =>
                match e with
                | S.Evar _ => False
                | _ => True
                end) as Ps.
    unfold E.exp_novars.
    remember (fun e : E.exp =>
                match e with
                | E.Evar _ => False
                | _ => True
                end) as Pe.
    induction e using S.exp_ind' with
    (P:=fun c =>
          forall pc sG U sG' drv md eG K d c' eG' K'
                 (Htrans: com_trans pc sG U c sG' drv md eG K d c' eG' K')
                 (HPs: S.forall_subexp' Ps c),
            E.forall_subexp' Pe c')
      (P0:=fun e =>
             forall sG t drv md eG d e' t'
                    (Htrans: exp_trans sG e t drv md eG d e' t')
                    (HPs: S.forall_subexp Ps e),
               E.forall_subexp Pe e')
      (P1:=fun c =>
             forall pc sG U sG' md eG K d c' eG' K' drv
                    (Htrans: prog_trans pc sG U c sG' drv md eG K d c' eG' K')
                    (HPs: S.forall_subexp'' Ps c),
               E.forall_subexp' Pe c');
      intros; inversion Htrans; subst; try constructor; auto;
        inversion HPs; eauto.
    subst. admit. (* induction H21.
    - rewrite Forall_forall. intros.
      eapply In_nth with (d:=E.Cskip) in H10.
      destruct H10 as [ i [ Hilen Hx ] ].
      assert (i < length coms) by omega.
      apply nth_In with (d:=S.Cskip) in H10.
      rewrite Forall_forall in H.
      assert (i < length coms) by omega.
      apply H8 in H12.
      rewrite Forall_forall in H1.
      eapply H with (c':=nth i coms0 E.Cskip) in H10; eauto.
      now rewrite Hx in H10. *)
    (*- admit.
    - admit. *)
  Admitted.

  Lemma trans_pres_all_loc_immutable : forall e sG t drv md eG d e' t',
      exp_trans sG e t drv md eG d e' t' ->
      S.all_loc_immutable e sG ->
      context_trans sG d eG ->
      E.all_loc_immutable e' eG.
  Proof.
  Admitted.

  Lemma trans_pres_forall_var : forall sG eG d (Pe: var -> E.type -> Prop),
      context_trans sG d eG ->
      S.forall_var sG (fun x t => forall t', ttrans t d t' -> Pe x t') ->
      E.forall_var eG Pe.
  Proof.
    intros.
    unfold E.forall_var.
    unfold S.forall_var in H0. inversion H. subst.
    intros. unfold subdom in H3.
    inversion H8. subst.
    pose (H3 x) as HsGx.
    rewrite H9 in HsGx.
    destruct HsGx as [ t' HsGx ].
    assert (S.var_in_dom sG x t') by now apply S.Var_in_dom.
    unfold S.forall_var in H5.
    pose H10 as HeG.
    apply H5 in HeG.
    destruct HeG as [ t'0 HeG ].
    destruct HeG. inversion H12. subst.
    rewrite H9 in H13. inversion H13. subst.
    eapply H0; eauto.
  Qed.

  Lemma nth_eq_nth_S_cons {A} i xs (x: A) d :
    nth i xs d = nth (i + 1) (x :: xs) d.
  Proof.
    replace (i + 1) with (S i) by omega. reflexivity.
  Qed.
End TransLemmas.

Section TransProof.
  Hint Constructors E.exp_type E.com_type.

  Lemma process_seq_output_wt' (pc: policy) (md0: E.mode) (mds: list E.mode)
        (Gs: list E.context) (Ks: list (set E.enclave))
        (d: E.loc_mode) (U: set condition) (coms: list E.com)
        (HUmd0: U = [] \/ md0 <> E.Normal) :
    forall comsout Gsout Ksout,
      (forall (i: nat),
          i < length mds ->
          (nth i mds E.Normal <> E.Normal /\
           nth i mds E.Normal <> nth (i + 1) mds E.Normal ->
           E.is_var_low_context (nth i Gs E.mt))) ->
      process_seq_output coms md0 mds Gs Ks comsout Gsout Ksout ->
      length Gs = length coms + 1 ->
      length Ks = length coms + 1 ->
      length mds = length coms ->
      (forall i,
          i < length coms ->
          E.com_type pc (nth i mds E.Normal) (nth i Gs E.mt)
                     (nth i Ks []) U d (nth i coms E.Cskip)
                     (nth (i + 1) Gs E.mt) (nth (i + 1) Ks [])) ->
      length Gsout = length comsout + 1 /\
      length Ksout = length comsout + 1 /\
      (forall i,
          i < length comsout ->
          E.com_type pc md0 (nth i Gsout E.mt) (nth i Ksout []) U d
                     (nth i comsout E.Cskip)
                     (nth (i + 1) Gsout E.mt) (nth (i + 1) Ksout [])).
  Proof.
    intros comsout Gsout Ksout Hmds. intros.
    induction H.
    - split. omega. split. omega.
      intros. pose H4 as H4'. apply H3 in H4'.
      assert (i < length mds) by omega.
      apply nth_In with (d:=E.Normal) in H5.
      rewrite Forall_forall in H.
      apply H in H5. subst. eauto.
    - assert (length (G2 :: Gs') = length coms' + 1).
      {
        rewrite H5 in H0.
        rewrite H6 in H0.
        simpl in *. omega.
      }
      pose H9 as H9'.
      apply IHprocess_seq_output in H9'; eauto.
      destruct_conjs. repeat split.
      + simpl in *. omega.
      + simpl in *. omega.
      + intros. destruct (Nat.eq_dec i 0).
        * subst. simpl. assert (0 < length (c :: coms')) by (simpl; omega).
          apply H3 in H. simpl in H. eauto.
        * apply Nat.neq_0_r in n. destruct n as [ m Hm ].
          rewrite Hm in *. simpl.
          simpl in H13. apply lt_S_n in H13. apply H12 in H13. eauto.
      + intros.
        assert (i + 1 < length mds).
        {
          rewrite H4. simpl. omega.
        }
        apply Hmds in H12.
        rewrite H6 in H12. now rewrite <- nth_eq_nth_S_cons in H12.
        rewrite H4. now repeat rewrite <- nth_eq_nth_S_cons.
      + rewrite H5 in H1. rewrite H7 in H1. simpl in *. omega.
      + subst. simpl in *. omega.
      + intros.
        assert (S i < length coms).
        {
          rewrite H5. simpl. omega.
        }
        apply H3 in H11. subst. simpl in *. eauto.
    - admit.
  Admitted.
  
  Lemma process_seq_output_wt (pc: policy) (md0: E.mode) (mds: list E.mode)
        (Gs: list E.context) (Ks: list (set E.enclave))
        (d: E.loc_mode) (U: set condition) (coms: list E.com) :
    forall comsout Gsout Ksout,
      (forall (i: nat),
          i < length mds ->
          (nth i mds E.Normal <> E.Normal /\
           nth i mds E.Normal <> nth (i + 1) mds E.Normal ->
           E.is_var_low_context (nth i Gs E.mt))) ->
      U = [] \/ md0 <> E.Normal ->
      length Gs = length coms + 1 ->
      length Ks = length coms + 1 ->
      length mds = length coms ->
      (forall i,
          i < length coms ->
          E.com_type pc (nth i mds E.Normal) (nth i Gs E.mt)
                     (nth i Ks []) U d (nth i coms E.Cskip)
                     (nth (i + 1) Gs E.mt) (nth (i + 1) Ks [])) ->
      process_seq_output coms md0 mds Gs Ks comsout Gsout Ksout ->
      E.com_type pc md0 (nth 0 Gsout E.mt) (nth 0 Ksout []) U d
                 (E.Cseq comsout) (last Gsout E.mt) (last Ksout []).
  Proof.
    intros. eapply process_seq_output_wt' in H4; eauto.
    destruct_conjs. subst. eapply E.CTseq; eauto.
  Qed.
  
  Lemma prog_trans_sound : forall pc sG U c sG' md eG K d c' eG' K' drv,
      S.prog_wt pc sG U c sG' drv ->
      prog_trans pc sG U c sG' drv md eG K d c' eG' K' ->
      E.com_type pc md eG K U d c' eG' K'.
  Proof.
    intros.
    induction H0 using prog_trans_mut with
    (P:=fun sG e t drv md eG d e' t'
            (et: exp_trans sG e t drv md eG d e' t') =>
          S.exp_wt sG e t drv ->
          E.exp_type md eG d e' t')
    (P0:=fun pc sG U c sG' drv md eG K d c' eG' K'
            (ct: com_trans pc sG U c sG' drv md eG K d c' eG' K') =>
          S.com_wt pc sG U c sG' drv ->
          E.com_type pc md eG K U d c' eG' K');
      eauto; inversion H; subst; eauto.
    (* Expressions. *)
    - eapply trans_exp_btrans in e.
      inversion e. subst. constructor; eauto.
    (* Commands. *)
    - eapply E.CTassign; eauto. destruct eG. reflexivity.
    - eapply E.CTdeclassify; eauto.
      + eapply trans_pres_exp_novars; eauto.
      + eapply trans_pres_all_loc_immutable; eauto.
    - eapply E.CTifelse; eauto; intuition.
    - eapply E.CTwhile; eauto; intuition.
    (* Programs. *)
    - eapply process_seq_output_wt; eauto; rewrite e3 in *; eauto.
      simpl in e1. omega.
  Qed.
  
End TransProof.