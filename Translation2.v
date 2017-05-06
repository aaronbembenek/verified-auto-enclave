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
  Definition union {A} (xs ys: list A) := (rev ys) ++ xs.

  Lemma union_nil {A} (xs: list A) : union xs [] = xs.
  Proof. reflexivity. Qed.
  
  Inductive process_kill : list E.enclave -> list E.enclave -> E.context ->
                           list E.com -> list E.context ->
                           list (list E.enclave) -> Prop :=
  | PK_nil : forall Kinit G,
      process_kill Kinit [] G [] [G] [Kinit]
  | PK_cons : forall Kinit G K Ks kcoms Ksout Gsout,
      process_kill (K :: Kinit) Ks G kcoms Gsout ((K :: Kinit) :: Ksout) ->
      process_kill Kinit (K :: Ks) G (E.Ckill K :: kcoms)
                   (G :: Gsout) (Kinit :: (K :: Kinit) :: Ksout).

  Inductive process_seq_output (pc: policy) (coms: list E.com) (md0: E.mode)
            (mds: list E.mode) (Gs: list E.context)
            (Ks K's K''s: list (list E.enclave)) :
    list E.com -> list E.context -> list (list E.enclave) -> Prop :=
  | PSO0 :
      Forall (fun md => md = md0) mds ->
      Forall (fun K => K = []) K''s ->
      process_seq_output pc coms md0 mds Gs Ks K's K''s coms Gs
                         (nth 0 Ks [] :: K's)
  | PSO1: forall c coms' K'' K''s2 K' K's2 K1 K2 Ks2 G1 G2 Gs2
                 kcoms pk_Gs pk_Ks Gs3 Ksout coms'' mds',
      pc = low ->
      md0 = E.Normal ->
      mds = E.Normal :: mds' ->
      coms = c :: coms' ->
      K''s = K'' :: K''s2 ->
      K's = K' :: K's2 ->
      Ks = K1 :: K2 :: Ks2 ->
      Gs = G1 :: G2 :: Gs2 ->
      process_kill K' K'' G2 kcoms pk_Gs pk_Ks ->
      process_seq_output pc coms' md0 mds' (G2 :: Gs2) (K2 :: Ks2) K's2 K''s2
                         coms'' (G2 :: Gs3) (K2 :: Ksout) ->
      process_seq_output pc coms md0 mds Gs Ks K's K''s
                         (c :: kcoms ++ coms'')
                         (G1 :: pk_Gs ++ Gs3)
                         (K1 :: pk_Ks ++ Ksout)
  | PSO2: forall j mds1 mds2 c coms' coms1 coms2 Gs1 Gs2
                 Ks1 Ks2 K's2 K''s2 K''s1 K's1
                 Gs2out Ks2out K1 K2 G1 G2 K' K'' kcoms pk_Gs pk_Ks,
      pc = low ->
      md0 = E.Normal ->
      mds = mds1 ++ mds2 ->
      Forall (fun md => md = E.Encl j) mds1 ->
      nth 0 mds2 E.Normal <> E.Encl j ->
      coms = coms1 ++ coms2 ->
      length coms1 = length mds1 ->
      Gs = G1 :: Gs1 ++ G2 :: Gs2 ->
      length (G1 :: Gs1) = length mds1 ->
      Ks = K1 :: Ks1 ++ K2 :: Ks2 ->
      K's = K's1 ++ K' :: K's2 ->
      K''s = K''s1 ++ K'' :: K''s2 ->
      length (K1 :: Ks1) = length mds1 ->
      length (K's1 ++ [K']) = length mds1 ->
      length (K''s1 ++ [K'']) = length mds1 ->
      c = E.Cenclave j (E.Cseq coms1) ->
      process_kill K' K'' G2 kcoms pk_Gs pk_Ks ->
      process_seq_output pc coms2 md0 mds2 (G2 :: Gs2)
                         (K2 :: Ks2) (K's2) (K''s2)
                         coms' (G2 :: Gs2out) (K2 :: Ks2out) ->
      process_seq_output pc coms md0 mds Gs Ks K's K''s
                         (c :: kcoms ++ coms')
                         (G1 :: pk_Gs ++ Gs2out)
                         (K1 :: pk_Ks ++ Ks2out).

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
                   E.mode -> E.context -> list E.enclave ->
                   E.loc_mode -> E.com -> E.context -> list E.enclave ->
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
                    E.mode -> E.context -> list E.enclave ->
                    E.loc_mode -> E.com -> E.context -> list E.enclave ->
                    Prop :=
  | TRprog : forall d sGs eGs drvs mds Ks (*K's*) coms coms' coms'' md0
                    U pc eGs' mds' K's K''s Ksout,
      length eGs = length coms + 1 ->
      length sGs = length coms + 1 ->
      length mds = length coms + 1 ->
      length Ks = length coms ->
      length K's = length coms ->
      length K''s = length coms ->
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
                    (nth i K's [])) ->
      (forall (i: nat),
          (nth i mds' E.Normal <> E.Normal /\
           (nth i mds' E.Normal <> nth (i + 1) mds' E.Normal \/
            nth i K''s [] = []) ->
           E.is_var_low_context (nth (i + 1) eGs E.mt))) ->
      mds = md0 :: mds' ->
      md0 = E.Normal \/ (forall i,
                            i < length mds ->
                            (nth i mds E.Normal) = md0 /\
                            (nth i K''s []) = []) ->
      (forall i,
          i < length Ks - 1 ->
          nth (i + 1) Ks [] = union (nth i K's []) (nth i K''s [])) ->
      (forall i,
          Forall (fun e => ~In e (nth i K's [])) (nth i K''s [])) ->
      (forall i,
          i < length mds' - 1 ->
          nth i mds' E.Normal <> E.Normal /\
          nth i mds' E.Normal = nth (i + 1) mds' E.Normal ->
          nth i K''s [] = []) ->
      Forall (fun K'' => NoDup K'') K''s ->
      U = [] \/ md0 <> E.Normal ->
      (*sG0 = nth 0 sGs S.mt ->
      sGn = last sGs S.mt ->
      eG0 = nth 0 eGs E.mt ->
      K0 = nth 0 Ks [] ->
      eGn = last eGs' E.mt ->
      Kn = last Ks [] -> *)
      (*process_seq_output coms' md0 (skipn 1 mds) eGs coms'' eGs' -> *)
      process_seq_output pc coms' md0 mds' eGs Ks K's K''s coms'' eGs' Ksout ->
      prog_trans pc (nth 0 sGs S.mt) U (S.Prog coms) (last sGs S.mt)
                 (S.Pderiv sGs drvs)
                 md0 (nth 0 eGs' E.mt) (nth 0 Ksout []) d (E.Cseq coms'')
                 (last eGs' E.mt) (last Ksout []).

  Scheme exp_trans_mut := Induction for exp_trans Sort Prop
  with com_trans_mut := Induction for com_trans Sort Prop
  with prog_trans_mut := Induction for prog_trans Sort Prop.
End TransDef.

Section TransLemmas.
  Lemma nth_eq_nth_S_cons {A} i xs (x: A) d :
    nth i xs d = nth (i + 1) (x :: xs) d.
  Proof.
    replace (i + 1) with (S i) by omega. reflexivity.
  Qed.

  Lemma app_cons_helper_app {A} (x: A) xs y ys :
    x :: xs ++ y :: ys = (x :: xs ++ [y]) ++ ys.
  Proof.
    simpl. replace (y :: ys) with ([y] ++ ys) by reflexivity.
    now rewrite app_assoc.
  Qed.

  Lemma app_cons_helper {A} (x: A) xs ys :
    xs ++ x :: ys = (xs ++ [x]) ++ ys.
  Proof.
    rewrite <- app_assoc. now simpl.
  Qed.

  Lemma  last_app {A} (x d: A) xs :
    last (xs ++ [x]) d = x.
    induction xs. reflexivity. simpl.
    remember (xs ++ [x]) as l. destruct l.
    assert (xs ++ [x] <> []).
    {
      destruct xs; simpl; contradict Heql; simpl; discriminate.
    }
    rewrite <- Heql in H. contradict H. reflexivity. auto.
  Qed.

  Lemma nth_app_helper_x {A} (x: A) xs ys d :
    nth (length xs) (xs ++ x :: ys) d = x.
  Proof.
    rewrite app_nth2; auto.
    replace (length xs - length xs) with 0 by omega. reflexivity.
  Qed.

  Lemma nth_app_helper_xs {A} (xs ys: list A) i d :
    nth i ys d = nth (length xs + i) (xs ++ ys) d.
  Proof.
    rewrite app_nth2.
    now replace (length xs + i - length xs) with i by omega.
    omega.
  Qed.

  Lemma exists_snoc {A}: forall (xs: list A),
      length xs > 0 ->
      exists xs' x, xs = xs' ++ [x].
  Proof.
    induction xs; intros. simpl in H. omega.
    destruct xs. exists []. exists a. auto.
    assert (length (a0 :: xs) > 0) by (simpl; omega).
    apply IHxs in H0. destruct_conjs.
    exists (a :: H0). exists H1. rewrite <- app_comm_cons.
    now rewrite H2.
  Qed.

  Lemma x_plus_y_minus_x (x y: nat) :
    x + y - x = y.
  Proof. omega. Qed.

  Lemma x_minus_x (x: nat) :
    x - x = 0.
  Proof. omega. Qed.
  
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
  
  Ltac crush_length := subst; simpl in *; repeat rewrite app_length in *;
                       simpl in *; auto; try omega.


  Lemma pk_exp_novars : forall {G} {Gsout} {Ksout} {Kstokill Kinit} {kcoms},
      process_kill Kinit Kstokill G kcoms Gsout Ksout ->
      Forall (fun c => E.forall_subexp'
                         (fun e => match e with
                                   | E.Evar _ => False
                                   | _ => True
                                   end) c) kcoms.
  Proof.
    intros. induction H.
    - apply Forall_nil.
    - constructor; auto.
  Qed.

 Lemma pso_exp_novars : forall {pc} {coms} {md0} {mds} {Gs}
                               {Ks K's K''s} {coms'} {Gsout} {Ksout},
      process_seq_output pc coms md0 mds Gs Ks K's K''s coms' Gsout Ksout ->
      Forall (fun c => E.forall_subexp'
                         (fun e => match e with
                                   | E.Evar _ => False
                                   | _ => True
                                   end) c) coms ->
      Forall (fun c => E.forall_subexp'
                         (fun e => match e with
                                   | E.Evar _ => False
                                   | _ => True
                                   end) c) coms'.
 Proof.
   intros. induction H; auto.
   - rewrite Forall_forall. intros.
     apply In_nth with (d:=E.Cskip) in H10.
     destruct_conjs. rename H10 into i.
     destruct (Nat.eq_dec i 0). subst.
     rewrite Forall_forall in H0.
     assert (In (nth 0 (c :: coms') E.Cskip) (c :: coms')).
     {
       simpl. left. auto.
     }
     apply H0 in H. simpl in *. auto.
     rewrite Nat.neq_0_r in n.
     destruct n as [m n].
     rewrite n in *. replace (S m) with (m + 1) in H12 by omega.
     rewrite <- nth_eq_nth_S_cons in H12.
     assert (m < length kcoms \/ m >= length kcoms) by omega.
     destruct H10.
     + rewrite app_nth1 in H12 by crush_length. subst.
       apply pk_exp_novars in H8.
       rewrite Forall_forall in H8. apply H8. apply nth_In. auto.
     + rewrite app_nth2 in H12 by crush_length. subst.
       inversion H0. subst. apply IHprocess_seq_output in H3.
       rewrite Forall_forall in H3. apply H3. apply nth_In. crush_length.
   - rewrite Forall_forall. intros.
     apply In_nth with (d:=E.Cskip) in H18.
     destruct_conjs. rename H18 into i.
     destruct (Nat.eq_dec i 0). subst.
     simpl. constructor. constructor.
     rewrite Forall_forall. intros.
     rewrite Forall_forall in H0.
     apply H0. apply in_or_app. tauto.
     rewrite Nat.neq_0_r in n.
     destruct n as [m n].
     rewrite n in *. replace (S m) with (m + 1) in H20 by omega.
     rewrite <- nth_eq_nth_S_cons in H20.
     assert (m < length kcoms \/ m >= length kcoms) by omega.
     destruct H18.
     + rewrite app_nth1 in H20 by crush_length. subst.
       apply pk_exp_novars in H16.
       rewrite Forall_forall in H16. apply H16. apply nth_In. auto.
     + rewrite app_nth2 in H20 by crush_length. subst.
       rewrite Forall_forall in H0.
       assert (forall x, In x coms2 ->
                         E.forall_subexp'
                           (fun e =>
                              match e with
                              | E.Evar _ => False
                              | _ => True
                              end) x).
       {
         intros. apply H0. apply in_or_app. tauto.
       }
       rewrite <- Forall_forall in H.
       apply IHprocess_seq_output in H.
       rewrite Forall_forall in H. apply H. apply nth_In. crush_length.
  Qed.
  
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
    apply (pso_exp_novars H21). subst.
    rewrite Forall_forall.
    intros. apply In_nth with (d:= E.Cskip) in H0.
    destruct H0 as [i [Hilen Hnthi]].
    rewrite Forall_forall in H.
    assert (i < length coms) by crush_length.
    apply H9 in H0. subst.
    assert (In (nth i coms S.Cskip) coms).
    {
      apply nth_In. crush_length.
    }
    apply (H _ H18) in H0. auto.
    rewrite Forall_forall in H11. now apply H11.
  Qed.

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
    
End TransLemmas.

Section TransProof.
  Hint Constructors E.exp_type E.com_type.

  (*
  Lemma pk_Forall_Gsout_eq_G : forall {G} {Gsout} {Ksout}
                                      {Kstokill} {Kinit} {kcoms},
      process_kill Kinit Kstokill G kcoms Gsout Ksout ->
      Forall (fun x => x = G) Gsout.
  Proof.
    intros. induction H; apply Forall_cons; auto.
  Qed.
*)

  Lemma pk_length_Gsout : forall {G} {Gsout} {Ksout} {Kstokill Kinit} {kcoms},
      process_kill Kinit Kstokill G kcoms Gsout Ksout ->
      length Gsout = length kcoms + 1.
  Proof.
    intros. induction H; simpl; auto.
  Qed.

  Lemma pk_last_Gsout : forall {G} {Gsout} {Ksout} {Kstokill Kinit} {kcoms},
      process_kill Kinit Kstokill G kcoms Gsout Ksout ->
      last Gsout E.mt = G.
  Proof.
    intros. induction H. reflexivity.
    simpl in *. destruct Gsout. reflexivity. auto.
  Qed.
  
  Lemma pk_first_Gsout : forall {G} {Gsout} {Ksout} {Kstokill Kinit} {kcoms},
      process_kill Kinit Kstokill G kcoms Gsout Ksout ->
      nth 0 Gsout E.mt = G.
  Proof.
    intros. induction H; reflexivity.
  Qed.

  Lemma pk_first_Gsout_app : forall {G} {Gsout rest} {Ksout}
                                    {Kstokill Kinit} {kcoms},
      process_kill Kinit Kstokill G kcoms Gsout Ksout ->
      nth 0 (Gsout ++ rest) E.mt = G.
  Proof.
    intros. rewrite app_nth1. now rewrite (pk_first_Gsout H).
    rewrite (pk_length_Gsout H). omega.
  Qed.

  Lemma pk_length_Ksout : forall {G} {Gsout} {Ksout} {Kstokill Kinit} {kcoms},
      process_kill Kinit Kstokill G kcoms Gsout Ksout ->
      length Ksout = length kcoms + 1.
    intros. induction H; simpl; auto.
  Qed.

  Lemma pk_last_Ksout : forall {G} {Gsout} {Ksout} {Kstokill Kinit} {kcoms},
      process_kill Kinit Kstokill G kcoms Gsout Ksout ->
      last Ksout [] = union Kinit Kstokill.
  Proof.
    intros. induction H. reflexivity.
    unfold union in *. simpl in *. rewrite <- app_assoc. now simpl.
  Qed.

  Lemma pk_first_Ksout : forall {G} {Gsout} {Ksout} {Kstokill Kinit} {kcoms},
      process_kill Kinit Kstokill G kcoms Gsout Ksout ->
      nth 0 Ksout [] = Kinit.
  Proof.
    intros. induction H; reflexivity.
  Qed.

  Lemma pk_first_Ksout_app : forall {G} {Gsout} {Ksout rest}
                                    {Kstokill Kinit} {kcoms},
      process_kill Kinit Kstokill G kcoms Gsout Ksout ->
      nth 0 (Ksout ++ rest) [] = Kinit.
  Proof.
    intros. rewrite app_nth1. now rewrite (pk_first_Ksout H).
    rewrite (pk_length_Ksout H). omega.
  Qed.

  Lemma pso_length_Gsout : forall {pc} {coms} {md0} {mds} {Gs}
                                  {Ks K's K''s} {coms'} {Gsout} {Ksout},
      process_seq_output pc coms md0 mds Gs Ks K's K''s coms' Gsout Ksout ->
      length Gs = length coms + 1 ->
      length Gsout = length coms' + 1.
    intros. induction H; auto.
    - assert (length (G2 :: Gs2) = length coms' + 1) by
          (subst; simpl in *; omega).
      apply IHprocess_seq_output in H10. simpl in *. repeat rewrite app_length.
      rewrite (pk_length_Gsout H8).
      replace (length Gs3) with (length coms'') by omega. omega.
    - subst. simpl in *. repeat rewrite app_length in *. simpl in *.
      rewrite <- plus_assoc. rewrite <- IHprocess_seq_output.
      rewrite (pk_length_Gsout H16). omega. omega.
  Qed.

  Lemma pso_length_Ksout : forall {pc} {coms} {md0} {mds} {Gs}
                                  {Ks K's K''s} {coms'} {Gsout} {Ksout},
      process_seq_output pc coms md0 mds Gs Ks K's K''s coms' Gsout Ksout ->
      length K's = length coms ->
      length Ksout = length coms' + 1.
  Proof.
    intros. induction H; simpl. omega.
    - assert (length K's2 = length coms') by (subst; simpl in *; omega).
      apply IHprocess_seq_output in H10. simpl in *. repeat rewrite app_length.
      rewrite (pk_length_Ksout H8).
      replace (length Ksout) with (length coms'') by omega. omega.
    - subst. repeat rewrite app_length in *. simpl in *.
      assert (length K's2 = length coms2) by omega.
      apply IHprocess_seq_output in H.
      rewrite (pk_length_Ksout H16). omega.
  Qed.
  
  Lemma process_kill_wt' : forall Kstokill Kinit kcoms Ksout Gsout G U i d,
      process_kill Kinit Kstokill G kcoms Gsout Ksout ->
      Forall (fun e => ~In e Kinit) Kstokill ->
      NoDup Kstokill ->
      i < length kcoms ->
      E.com_type low E.Normal (nth i Gsout E.mt) (nth i Ksout []) U d
                 (nth i kcoms E.Cskip) (nth (i + 1) Gsout E.mt)
                 (nth (i + 1) Ksout []).
  Proof.
    induction Kstokill; intros; inversion H; subst.
    simpl in H2. inversion H2.
    destruct (Nat.eq_dec i 0).
    - rewrite e. simpl. rewrite (pk_first_Gsout H10).
      eapply E.CTkill; eauto. unfold E.mode_alive.
      rewrite Forall_forall in H0. apply H0. now constructor.
    - rewrite Nat.neq_0_r in n. destruct n as [m n].
      eapply IHKstokill with (i:=m) in H10.
      + rewrite n. simpl in *. eauto.
      + rewrite Forall_forall in *. intros.
        destruct (Nat.eq_dec x a). subst.
        rewrite NoDup_cons_iff in H1. tauto.
        rewrite not_in_cons. split; auto.
        apply H0. now apply in_cons.
      + rewrite NoDup_cons_iff in H1. tauto.
      + simpl in H2. omega.
  Qed.

  Ltac crush_length := subst; simpl in *; repeat rewrite app_length in *;
                       simpl in *; auto; try omega.
  
  Lemma process_seq_output_wt' (pc: policy) (md0: E.mode) (mds: list E.mode)
        (Gs: list E.context) (Ks: list (list E.enclave))
        (d: E.loc_mode) (U: set condition) (coms: list E.com) :
    forall comsout Gsout Ksout (K's K''s: list (list E.enclave)),
      (forall i,
          i < length Ks - 1 ->
          nth (i + 1) Ks [] = union (nth i K's []) (nth i K''s [])) ->
      (forall i,
          Forall (fun e => ~In e (nth i K's [])) (nth i K''s [])) ->
      (forall i,
          i < length mds - 1 ->
          nth i mds E.Normal <> E.Normal /\
          nth i mds E.Normal = nth (i + 1) mds E.Normal ->
          nth i K''s [] = []) ->
      (forall (i: nat),
          (nth i mds E.Normal <> E.Normal /\
           (nth i mds E.Normal <> nth (i + 1) mds E.Normal \/
            nth i K''s [] = []) ->
           E.is_var_low_context (nth (i + 1) Gs E.mt))) ->
      process_seq_output pc coms md0 mds Gs Ks K's K''s comsout Gsout Ksout ->
      length Gs = length coms + 1 ->
      length Ks = length coms ->
      length K's = length coms ->
      length K''s = length coms ->
      length mds = length coms ->
      (forall i,
          i < length coms ->
          E.com_type pc (nth i mds E.Normal) (nth i Gs E.mt)
                     (nth i Ks []) U d (nth i coms E.Cskip)
                     (nth (i + 1) Gs E.mt) (nth i K's [])) ->
      U = [] \/ md0 <> E.Normal ->
      Forall (fun K'' => NoDup K'') K''s ->
      (forall i,
          i < length comsout ->
          E.com_type pc md0 (nth i Gsout E.mt) (nth i Ksout []) U d
                     (nth i comsout E.Cskip)
                     (nth (i + 1) Gsout E.mt) (nth (i + 1) Ksout [])).
  Proof.
    intros comsout Gsout Ksout K's K''s Hunion Hinter HK''sempty Hcontext
           Hpso HGslen HKslen HK'slen HK''slen Hmdslen Hwt HU HNoDup.
    induction Hpso; intros.
    - assert (nth i mds E.Normal = md0) as Hmd0.
      {
        rewrite Forall_forall in H. apply H. apply nth_In. omega.
      }
      destruct (Nat.eq_dec i 0).
      + rewrite e. simpl. apply Hwt in H1. now subst.
      + rewrite Nat.neq_0_r in n. destruct n as [m n].
        assert (nth i (nth 0 Ks [] :: K's) = nth m K's) by
            (rewrite n; reflexivity).
        rewrite H2. assert (m < length Ks - 1) by omega.
        assert (m < length K''s) by omega.
        apply Hwt in H1. rewrite Hmd0 in H1.
        assert (nth i Ks [] = nth m K's []).
        {
          apply Hunion in H3.
          replace (nth m K''s []) with ([]:list E.enclave) in H3.
          simpl in H3. replace (m + 1) with i in H3; auto. omega.
          rewrite Forall_forall in H0. symmetry. apply H0. now apply nth_In.
        }
        rewrite <- H5. now rewrite <- nth_eq_nth_S_cons.
    - destruct (Nat.eq_dec i 0).
      + rewrite e. simpl.
        replace (nth 0 (pk_Gs ++ Gs3) E.mt) with G2.
        replace (nth 0 (pk_Ks ++ Ksout) []) with K'.
        assert (0 < length coms) by (rewrite H2; simpl; omega).
        apply Hwt in H9. subst. now simpl in H9.
        * replace (nth 0 (pk_Ks ++ Ksout) []) with (nth 0 pk_Ks []).
          now rewrite (pk_first_Ksout H7).
          symmetry. apply app_nth1. pose (pk_length_Ksout H7). omega.
        * replace (nth 0 (pk_Gs ++Gs3) E.mt) with (nth 0 pk_Gs E.mt).
          now rewrite (pk_first_Gsout H7).
          symmetry. apply app_nth1. pose (pk_length_Gsout H7). omega.
      + rewrite Nat.neq_0_r in n. destruct n as [m n]. rewrite n. simpl.
        assert (m < length kcoms \/ m >= length kcoms) by omega. destruct H9.
        * clear IHHpso.
          replace (nth m (pk_Gs ++ Gs3) E.mt) with (nth m pk_Gs E.mt).
          replace (nth m (pk_Ks ++ Ksout) []) with (nth m pk_Ks []).
          replace (nth m (kcoms ++ coms'') E.Cskip) with
          (nth m kcoms E.Cskip).
          replace (nth (m + 1) (pk_Gs ++ Gs3) E.mt) with
          (nth (m + 1) pk_Gs E.mt).
          replace (nth (m + 1) (pk_Ks ++ Ksout) []) with
          (nth (m + 1) pk_Ks []).
          rewrite H. rewrite H0.
          eapply process_kill_wt'; eauto.
          pose (Hinter 0). rewrite H3 in f. rewrite H4 in f. now simpl.
          rewrite H3 in HNoDup. now apply Forall_inv with (l:=K''s2).
          1-5: symmetry; apply app_nth1.
          1,4: rewrite (pk_length_Ksout H7); omega.
          1,3: rewrite (pk_length_Gsout H7); omega.
          auto.
        * remember (m - length kcoms) as x.
          replace (nth m (pk_Gs ++ Gs3) E.mt) with (nth x (G2 :: Gs3) E.mt).
          replace (nth m (pk_Ks ++ Ksout) []) with (nth x (K2 :: Ksout) []).
          replace (nth m (kcoms ++ coms'') E.Cskip) with
          (nth x coms'' E.Cskip).
          replace (nth (m + 1) (pk_Gs ++ Gs3) E.mt) with
          (nth (x + 1) (G2 :: Gs3) E.mt).
          replace (nth (m + 1) (pk_Ks ++ Ksout) []) with
          (nth (x + 1) (K2 :: Ksout) []).
          
          eapply IHHpso; eauto; subst; clear IHHpso; intros.
          5-9: simpl in *; omega.
          
          assert (i + 1 < length (K1 :: K2 :: Ks2) - 1) by (simpl in *; omega).
          apply Hunion in H0.
          repeat rewrite <- nth_eq_nth_S_cons in H0.
          now rewrite <- nth_eq_nth_S_cons.

          pose (Hinter (i + 1)).
          now repeat rewrite <- nth_eq_nth_S_cons in f.

          assert (i + 1 < length (E.Normal :: mds') - 1) by (simpl; omega).
          apply HK''sempty in H1. now rewrite <- nth_eq_nth_S_cons in H1.
          now repeat rewrite <- nth_eq_nth_S_cons.

          pose (Hcontext (i + 1)).
          repeat rewrite <- nth_eq_nth_S_cons in i0.
          rewrite <- nth_eq_nth_S_cons; auto.
          
          assert (i + 1 < length (c :: coms')) by (simpl; omega).
          apply Hwt in H0.
          repeat rewrite <- nth_eq_nth_S_cons in H0.
          rewrite <- nth_eq_nth_S_cons; auto.

          now inversion HNoDup.

          simpl in H8. rewrite app_length in H8. omega.

          1,4: pose (pk_length_Ksout H7);
            assert (length pk_Ks > 0) by omega;
            apply exists_snoc in H10;
            destruct H10 as [xs [a Hpk_Ks]];
            assert (length xs = length kcoms) by
                (rewrite Hpk_Ks in e;
                 rewrite app_length in e; simpl in e; omega);
            pose (pk_last_Ksout H7); rewrite Hpk_Ks in e0;
              rewrite last_app in e0; subst;
                replace (m - length kcoms + 1) with
                (m + 1 - length kcoms) by omega;
                rewrite <- app_assoc;
                symmetry; rewrite <- H10 in *;
                  assert (0 < length (K1 :: K2 :: Ks2) - 1) by (simpl; omega);
                  apply Hunion in H; simpl in H; rewrite <- H;
                    replace ([K2] ++ Ksout) with (K2 :: Ksout) by (simpl; auto);
                    apply app_nth2; omega.

          1,3: pose (pk_length_Gsout H7);
            assert (length pk_Gs > 0) by omega;
            apply exists_snoc in H10;
            destruct H10 as [xs [a Hpk_Gs]];
            assert (length xs = length kcoms) by
                (rewrite Hpk_Gs in e;
                 rewrite app_length in e; simpl in e; omega);
            pose (pk_last_Gsout H7); rewrite Hpk_Gs in e0;
              rewrite last_app in e0; subst;
                replace (m - length kcoms + 1) with
                (m + 1 - length kcoms) by omega;
                rewrite <- app_assoc;
                replace ([G2] ++ Gs3) with (G2 :: Gs3) by (simpl; auto);
                symmetry; rewrite <- H10 in *;
                  apply app_nth2; omega.

          rewrite Heqx. symmetry. now apply app_nth2.

    - destruct (Nat.eq_dec i 0).
      + subst. simpl. repeat rewrite app_length in *.
        rewrite (pk_first_Gsout_app H15).
        rewrite (pk_first_Ksout_app H15).
        eapply E.CTenclave; eauto.
        eapply E.CTseq with (Gs:=G1 :: Gs1 ++ [G2]) (Ks:=K1 :: K's1 ++ [K']);
          eauto.
        1-2: crush_length.
        
        intros. assert (i < length coms1 + length coms2) by omega.
        apply Hwt in H0.
        assert (nth i (K1 :: Ks1 ++ K2 :: Ks2) [] = nth i (K1 :: K's1) []).
        {
          destruct (Nat.eq_dec i 0). subst. now simpl.
          rewrite Nat.neq_0_r in n. destruct n as [m n].
          subst. replace (S m) with (m + 1) by omega.
          assert (m < length (K1 :: Ks1 ++ K2 :: Ks2) - 1) by crush_length.
          apply Hunion in H1.
          replace (nth m (K''s1 ++ K'' :: K''s2) [])
          with ([]:list E.enclave) in H1.
          replace (nth m (K's1 ++ K' :: K's2) []) with (nth m K's1 []) in H1.
          rewrite union_nil in H1.
          replace (nth (m + 1) (K1 :: K's1) []) with (nth m K's1 []) by
              (rewrite <- nth_eq_nth_S_cons; auto). auto.
          rewrite app_nth1; crush_length. auto.
          symmetry. apply HK''sempty; crush_length.
          rewrite app_nth1; crush_length.
          rewrite app_nth1; crush_length.
          replace (nth m mds1 E.Normal) with (E.Encl j).
          replace (nth (m + 1) mds1 E.Normal) with (E.Encl j).
          intuition. discriminate.
          1-2: rewrite Forall_forall in H2; symmetry; apply H2;
            apply nth_In; crush_length.
        }

        rewrite H1 in H0.
        replace (nth i (mds1 ++ mds2) E.Normal) with (E.Encl j) in H0.
        rewrite app_cons_helper_app in H0.
        rewrite app_nth1 in H0.
        rewrite app_nth1 in H0.
        rewrite app_nth1 in H0.
        replace (nth i (K's1 ++ K' :: K's2) [])
        with (nth i (K's1 ++ [K']) []) in H0.
        replace (nth i (K1 :: K's1 ++ [K']) [])
        with (nth i (K1 :: K's1) []).
        replace (nth (i + 1) (K1 :: K's1 ++ [K']) [])
        with (nth i (K's1 ++ [K']) []).
        replace U with ([]:set condition) in H0. auto.
        
        destruct HU; auto. contradict H1; auto.

        now rewrite <- nth_eq_nth_S_cons.
        rewrite app_comm_cons. symmetry. rewrite app_nth1; crush_length.
        replace (K's1 ++ K' :: K's2) with ((K's1 ++ [K']) ++ K's2) by
            (rewrite <- app_assoc; simpl; auto).
        symmetry. rewrite app_nth1; crush_length.

        1-3: crush_length.

        rewrite app_nth1; crush_length. rewrite Forall_forall in H2.
        symmetry. apply H2. apply nth_In; crush_length.

        1-2: rewrite app_comm_cons; now rewrite last_app.

        pose (Hcontext (length mds1 - 1)).
        replace (length mds1 - 1 + 1) with (length (G1 :: Gs1)) in i
          by crush_length.
        rewrite app_comm_cons in i.
        rewrite nth_app_helper_x in i.
        apply i.
        replace (nth (length mds1 - 1) (mds1 ++ mds2) E.Normal)
        with (E.Encl j).
        replace (length (G1 :: Gs1)) with (length mds1) by crush_length.
        rewrite app_nth2.
        split. intuition. discriminate.
        left. replace (length mds1 - length mds1) with 0 by omega.
        auto. omega.

        rewrite app_nth1.
        rewrite Forall_forall in H2. symmetry. apply H2.
        apply nth_In.
        1-2: simpl in H7; omega.

      + rewrite Nat.neq_0_r in n. destruct n as [m n]. rewrite n. simpl.
        assert (m < length kcoms \/ m >= length kcoms) by omega. destruct H17.
        * clear IHHpso.
          replace (nth m (pk_Gs ++ Gs2out) E.mt) with (nth m pk_Gs E.mt).
          replace (nth m (pk_Ks ++ Ks2out) []) with (nth m pk_Ks []).
          replace (nth m (kcoms ++ coms') E.Cskip) with
          (nth m kcoms E.Cskip).
          replace (nth (m + 1) (pk_Gs ++ Gs2out) E.mt) with
          (nth (m + 1) pk_Gs E.mt).
          replace (nth (m + 1) (pk_Ks ++ Ks2out) []) with
          (nth (m + 1) pk_Ks []).
          rewrite H. rewrite H0.
          eapply process_kill_wt'; eauto. subst.
          pose (Hinter (length K''s1)).
          rewrite nth_app_helper_x in f.
          replace (length K''s1) with (length K's1) in f by crush_length.
          now rewrite nth_app_helper_x in f.
          subst. rewrite Forall_forall in HNoDup.
          apply HNoDup. apply in_or_app. right. constructor. auto.
          all: symmetry; apply app_nth1.
          1,4: rewrite (pk_length_Ksout H15).
          3,5: rewrite (pk_length_Gsout H15).
          all: crush_length.
        * remember (m - length kcoms) as x.
          replace (nth m (pk_Gs ++ Gs2out) E.mt) with (nth x (G2 :: Gs2out) E.mt).
          replace (nth m (pk_Ks ++ Ks2out) []) with (nth x (K2 :: Ks2out) []).
          replace (nth m (kcoms ++ coms') E.Cskip) with (nth x coms' E.Cskip).
          replace (nth (m + 1) (pk_Gs ++ Gs2out) E.mt) with
          (nth (x + 1) (G2 :: Gs2out) E.mt).
          replace (nth (m + 1) (pk_Ks ++ Ks2out) []) with
          (nth (x + 1) (K2 :: Ks2out) []).
          
          eapply IHHpso; eauto; subst; clear IHHpso; intros.
          5-9, 12: crush_length.
          
          assert (length (K1 :: Ks1) + i < length (K1 :: Ks1 ++ K2 :: Ks2) - 1)
            by crush_length.
          apply Hunion in H0.
          rewrite app_comm_cons in H0.
          rewrite app_nth2 in H0.
          replace (length (K1 :: Ks1) + i + 1 - length (K1 :: Ks1))
          with (i + 1) in H0 by omega.
          replace (length (K1 :: Ks1)) with (length (K's1 ++ [K']))
            in H0 by crush_length.
          rewrite app_cons_helper with (ys:=K's2) in H0.
          rewrite app_cons_helper with (ys:=K''s2) in H0.
          rewrite app_nth2 in H0.
          rewrite app_nth2 in H0.
          replace (length (K's1 ++ [K'])) with (length (K''s1 ++ [K'']))
            in H0 by crush_length.
          now rewrite x_plus_y_minus_x in H0.
          1-3: crush_length.

          pose (Hinter (length (K's1 ++ [K']) + i)).
          rewrite app_cons_helper with (ys:=K's2) in f.
          rewrite app_nth2 in f.
          replace (length (K's1 ++ [K'])) with (length (K''s1 ++ [K'']))
            in f by crush_length.
          rewrite app_cons_helper with (ys:=K''s2) in f.
          rewrite app_nth2 in f.
          now rewrite x_plus_y_minus_x in f.
          1-2: crush_length.

          assert (length mds1 + i < length (mds1 ++ mds2) -1) by crush_length.
          apply HK''sempty in H1.
          replace (length mds1) with (length (K''s1 ++ [K'']))
            in H1 by crush_length.
          rewrite app_cons_helper with (ys:=K''s2) in H1.
          rewrite app_nth2 in H1.
          now rewrite x_plus_y_minus_x in H1.
          crush_length.
          rewrite <- plus_assoc.
          repeat rewrite app_nth2. now repeat rewrite x_plus_y_minus_x.
          1-2: crush_length.

          pose (Hcontext (length (mds1) + i)).
          rewrite <- plus_assoc in i0.
          rewrite app_nth2 in i0.
          rewrite app_nth2 in i0.
          repeat rewrite x_plus_y_minus_x in i0.
          replace (length mds1) with (length (K''s1 ++ [K''])) in i0
            by crush_length.
          rewrite app_cons_helper with (ys:= K''s2) in i0.
          rewrite app_nth2 in i0.
          replace (length (K''s1 ++ [K''])) with (length (G1 :: Gs1)) in i0
            by crush_length.
          rewrite app_comm_cons in i0.
          rewrite app_nth2 in i0.
          repeat rewrite x_plus_y_minus_x in i0.
          eapply i0; eauto.
          1-4: crush_length.

          assert (length coms1 + i < length (coms1 ++ coms2)) by crush_length.
          apply Hwt in H0.
          rewrite <- plus_assoc in H0.
          repeat rewrite app_comm_cons in H0.
          rewrite app_cons_helper with (ys:=K's2) in H0.
          rewrite app_nth2 in H0.
          rewrite app_nth2 in H0.
          rewrite app_nth2 in H0.
          rewrite app_nth2 in H0.
          rewrite app_nth2 in H0.
          rewrite app_nth2 in H0.
          replace (length (G1 :: Gs1)) with (length coms1) in H0
            by crush_length.
          replace (length (K1 :: Ks1)) with (length coms1) in H0
            by crush_length.
          replace (length (K's1 ++ [K'])) with (length coms1) in H0
            by crush_length.
          rewrite H5 in H0.
          now repeat rewrite x_plus_y_minus_x in H0.
          1-6: crush_length.

          rewrite Forall_forall in *.
          intros. apply HNoDup.
          apply in_or_app. right.
          now apply in_cons.

          1,4: pose (pk_length_Ksout H15);
            assert (length pk_Ks > 0) by omega;
            apply exists_snoc in H18;
            destruct H18 as [xs [a Hpk_Ks]];
            assert (length xs = length kcoms) by crush_length;
            pose (pk_last_Ksout H15); rewrite Hpk_Ks in e0;
              rewrite last_app in e0; subst;
                replace (m - length kcoms + 1) with
                (m + 1 - length kcoms) by omega;
                rewrite <- app_assoc;
                rewrite app_nth2; rewrite <- H18 in *;
                  assert (length (K1 :: Ks1) - 1 <
                          length (K1 :: Ks1 ++ K2 :: Ks2) - 1) by crush_length;
                  apply Hunion in H;
                  replace (length (K1 :: Ks1) - 1 + 1)
                  with (length (K1 :: Ks1)) in H by crush_length;
                  replace (length (K1 :: Ks1) - 1) with (length K's1) in H
                    by crush_length;
                  rewrite app_comm_cons in H;
                  rewrite app_nth2 in H;
                  rewrite app_nth2 in H;
                  replace (length (K's1)) with (length (K''s1)) in H
                    by crush_length;
                  rewrite app_nth2 in H;
                  repeat rewrite x_minus_x in H; simpl in H; subst; auto;
                    crush_length.

          1,3: pose (pk_length_Gsout H15);
            assert (length pk_Gs > 0) by omega;
            apply exists_snoc in H18;
            destruct H18 as [xs [a Hpk_Gs]];
            assert (length xs = length kcoms) by crush_length;
            pose (pk_last_Gsout H15); rewrite Hpk_Gs in e0;
              rewrite last_app in e0; subst;
                replace (m - length kcoms + 1) with
                (m + 1 - length kcoms) by omega;
                rewrite <- app_assoc;
                rewrite app_nth2; rewrite <- H18 in *; simpl; auto;
                  crush_length.

          rewrite Heqx. symmetry. now apply app_nth2.
  Qed.
  
  Lemma process_seq_output_wt (pc: policy) (md0: E.mode) (mds: list E.mode)
        (Gs: list E.context) (Ks K's K''s: list (list E.enclave))
        (d: E.loc_mode) (U: set condition) (coms: list E.com) :
    forall comsout Gsout Ksout,
      (forall (i: nat),
          (nth i mds E.Normal <> E.Normal /\
           (nth i mds E.Normal <> nth (i + 1) mds E.Normal \/
            nth i K''s [] = []) ->
           E.is_var_low_context (nth (i + 1) Gs E.mt))) ->
      (forall i,
          i < length Ks - 1 ->
          nth (i + 1) Ks [] = union (nth i K's []) (nth i K''s [])) ->
      (forall i,
          Forall (fun e => ~In e (nth i K's [])) (nth i K''s [])) ->
      (forall i,
          i < length mds - 1 ->
          nth i mds E.Normal <> E.Normal /\
          nth i mds E.Normal = nth (i + 1) mds E.Normal ->
          nth i K''s [] = []) ->
      U = [] \/ md0 <> E.Normal ->
      length Gs = length coms + 1 ->
      length Ks = length coms ->
      length K's = length coms ->
      length K''s = length coms ->
      length mds = length coms ->
      Forall (fun K'' => NoDup K'') K''s ->
      (forall i,
          i < length coms ->
          E.com_type pc (nth i mds E.Normal) (nth i Gs E.mt)
                     (nth i Ks []) U d (nth i coms E.Cskip)
                     (nth (i + 1) Gs E.mt) (nth i K's [])) ->
      process_seq_output pc coms md0 mds Gs Ks K's K''s comsout Gsout Ksout ->
      E.com_type pc md0 (nth 0 Gsout E.mt) (nth 0 Ksout []) U d
                 (E.Cseq comsout) (last Gsout E.mt) (last Ksout []).
  Proof.
    intros. eapply E.CTseq; eauto.
    now eapply (pso_length_Gsout H11).
    now eapply (pso_length_Ksout H11).
    intros. eapply process_seq_output_wt' in H4; eauto.
  Qed.
  
  Theorem prog_trans_sound : forall pc sG U c sG' md eG K d c' eG' K' drv,
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
    - eapply process_seq_output_wt; eauto; rewrite e5 in *; auto;
        simpl in e1; omega.
  Qed.
  
End TransProof.