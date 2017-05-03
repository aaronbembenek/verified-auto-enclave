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
  (*
  Fixpoint member (x: E.enclave) xs : bool :=
    match xs with
    | [] => false
    | hd :: tl => if x =? hd then true else member x tl
    end.
  
  Lemma member_iff_In (x: E.enclave) xs :
    member x xs = true <-> In x xs.
  Proof.
    split; intros; induction xs.
    - simpl in H. discriminate.
    - simpl in H. destruct (Nat.eq_dec x a).
      rewrite e. apply in_eq. rewrite <- Nat.eqb_eq in n.
      apply in_cons.
      apply not_true_is_false in n. rewrite n in H. auto.
    - inversion H.
    - destruct (Nat.eq_dec x a). rewrite e.
      simpl. now rewrite <- beq_nat_refl.
      apply in_inv in H. destruct H. contradict n. now rewrite H.
      rewrite <- Nat.eqb_eq in n. apply not_true_is_false in n.
      simpl. rewrite n. auto.
  Qed.
  
  Definition union (xs ys: list E.enclave) := xs ++ ys.
  
  Definition inter (xs: list E.enclave) := filter (fun x => member x xs).*)

  Definition union {A} (xs ys: list A) := (rev ys) ++ xs.
  
  Inductive process_kill : list E.enclave -> list E.enclave -> E.context ->
                           list E.com -> list E.context ->
                           list (list E.enclave) -> Prop :=
  | PK_nil : forall Kinit G,
      process_kill Kinit [] G [] [G] [Kinit]
  | PK_cons : forall Kinit G K Ks kcoms Ksout Gsout,
      process_kill (K :: Kinit) Ks G kcoms Gsout ((K :: Kinit) :: Ksout) ->
      process_kill Kinit (K :: Ks) G (E.Ckill K :: kcoms)
                   (G :: Gsout) (Kinit :: (K :: Kinit) :: Ksout).

      (*
    - repeat split; auto. intros. pose H1 as H1'. apply Hwt in H1'.
      replace (nth i mds E.Normal) with md0 in H1'; auto.
      rewrite Forall_forall in H. symmetry. apply H. rewrite <- Hmdslen in H1.
      now apply nth_In. *) (*
    - repeat split; auto. intros. pose H1 as H1'. apply Hwt in H1'.
      replace (nth i mds E.Normal) with md0 in H1'; auto.
      rewrite Forall_forall in H. symmetry. apply H. rewrite <- Hmdslen in H1.
      now apply nth_In. *)
                   (*       .
  Function process_kill (K: set E.enclave) : list E.com :=
    match K with
    | [] => []
    | k :: K' => E.Ckill k :: process_kill K'
    end.
  *)
  Inductive process_seq_output (coms: list E.com) (md0: E.mode)
            (mds: list E.mode) (Gs: list E.context)
            (Ks Ks' Ks'': list (list E.enclave)) :
    list E.com -> list E.context -> list (list E.enclave) -> Prop :=
  | PSO0 :
      Forall (fun md => md = md0) mds ->
      Forall (fun K => K = []) Ks'' ->
      process_seq_output coms md0 mds Gs Ks Ks' Ks'' coms Gs
                         (nth 0 Ks [] :: Ks'). (*
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
      Forall (fun md => md = E.Encl j) mds1 ->
      nth 0 mds2 E.Normal <> E.Encl j ->
      coms = coms1 ++ coms2 ->
      length coms1 = length mds1 ->
      Gs = G1 :: Gs1 ++ G2 :: Gs2 ->
      length (G1 :: Gs1) = length mds1 ->
      Ks = K1 :: Ks1 ++ K2 :: Ks2 ->
      length (K1 :: Ks1) = length mds1 ->
      c = E.Cenclave j (E.Cseq coms1) ->
      process_seq_output coms2 md0 mds2 (G2 :: Gs2) (K2 :: Ks2)
                         coms' (G2 :: Gs2') (K2 :: Ks2') ->
      process_seq_output coms md0 mds Gs Ks
                         (c :: coms') (G1 :: G2 :: Gs2') (K1 :: K2 :: Ks2').
  *)
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
                    U pc eGs' mds' Ks' Ks'' Ksout,
      length eGs = length coms + 1 ->
      length sGs = length coms + 1 ->
      length mds = length coms + 1 ->
      length Ks = length coms ->
      length Ks' = length coms ->
      length Ks'' = length coms ->
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
                    (nth i Ks' [])) ->
      (forall (i: nat),
          (nth i mds' E.Normal <> E.Normal /\
           (nth i mds' E.Normal <> nth (i + 1) mds' E.Normal \/
            nth i Ks'' [] = []) ->
           E.is_var_low_context (nth (i + 1) eGs E.mt))) ->
      mds = md0 :: mds' ->
      md0 = E.Normal \/ (forall i,
                            i < length mds ->
                            (nth i mds E.Normal) = md0 /\
                            (nth i Ks'' []) = []) ->
      (forall i,
          i < length Ks - 1 ->
          nth (i + 1) Ks [] = union (nth i Ks' []) (nth i Ks'' [])) ->
      (forall i,
          Forall (fun e => ~In e (nth i Ks' [])) (nth i Ks'' [])) ->
      (forall i,
          i < length mds' - 1 ->
          nth i mds' E.Normal <> E.Normal /\
          nth i mds' E.Normal = nth (i + 1) mds' E.Normal ->
          nth i Ks'' [] = []) ->
      U = [] \/ md0 <> E.Normal ->
      (*sG0 = nth 0 sGs S.mt ->
      sGn = last sGs S.mt ->
      eG0 = nth 0 eGs E.mt ->
      K0 = nth 0 Ks [] ->
      eGn = last eGs' E.mt ->
      Kn = last Ks [] -> *)
      (*process_seq_output coms' md0 (skipn 1 mds) eGs coms'' eGs' -> *)
      process_seq_output coms' md0 mds' eGs Ks Ks' Ks'' coms'' eGs' Ksout ->
      prog_trans pc (nth 0 sGs S.mt) U (S.Prog coms) (last sGs S.mt)
                 (S.Pderiv sGs drvs)
                 md0 (nth 0 eGs' E.mt) (nth 0 Ksout []) d (E.Cseq coms'')
                 (last eGs' E.mt) (last Ksout []).

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

  Lemma app_cons_helper {A} (x: A) xs y ys :
    x :: xs ++ y :: ys = (x :: xs ++ [y]) ++ ys.
  Proof.
    simpl. replace (y :: ys) with ([y] ++ ys) by reflexivity.
    now rewrite app_assoc.
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
    
End TransLemmas.

Section TransProof.
  Hint Constructors E.exp_type E.com_type.

  Lemma pk_Forall_Gs_eq_G : forall G Gs Ks Kstokill Kinit kcoms,
      process_kill Kinit Kstokill G kcoms Gs Ks ->
      Forall (fun x => x = G) Gs.
  Proof.
    intros. induction H; apply Forall_cons; auto.
  Qed.

  Lemma pk_length_Gs : forall {G} {Gs} {Ks} {Kstokill} {Kinit} {kcoms},
      process_kill Kinit Kstokill G kcoms Gs Ks ->
      length Gs = length kcoms + 1.
  Proof.
    intros. induction H; simpl; auto.
  Qed.

  Lemma pk_last_Ksout : forall {G} {Gs} {Ks} {Kstokill} {Kinit} {kcoms},
      process_kill Kinit Kstokill G kcoms Gs Ks ->
      last Ks [] = union Kinit Kstokill.
  Proof.
    intros. induction H. reflexivity.
    unfold union in *. simpl in *. rewrite <- app_assoc. now simpl.
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
    - rewrite e. simpl. apply pk_Forall_Gs_eq_G in H10.
      rewrite Forall_forall in H10.
      pose (pk_length_Gs H). simpl in e0.
      assert (0 < length Gsout0) by omega.
      apply nth_In with (d:=E.mt) in H3. apply H10 in H3. rewrite H3.
      eapply E.CTkill. unfold E.mode_alive.
      rewrite Forall_forall in H0. apply H0. now constructor. auto.
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
  
  Lemma process_seq_output_wt' (pc: policy) (md0: E.mode) (mds: list E.mode)
        (Gs: list E.context) (Ks: list (list E.enclave))
        (d: E.loc_mode) (U: set condition) (coms: list E.com) :
    forall comsout Gsout Ksout (Ks' Ks'': list (list E.enclave)),
      (forall i,
          i < length Ks - 1 ->
          nth (i + 1) Ks [] = union (nth i Ks' []) (nth i Ks'' [])) ->
      (forall i,
          Forall (fun e => ~In e (nth i Ks' [])) (nth i Ks'' [])) ->
      (forall i,
          i < length mds - 1 ->
          nth i mds E.Normal <> E.Normal /\
          nth i mds E.Normal = nth (i + 1) mds E.Normal ->
          nth i Ks'' [] = []) ->
      (forall (i: nat),
          (nth i mds E.Normal <> E.Normal /\
           (nth i mds E.Normal <> nth (i + 1) mds E.Normal \/
            nth i Ks'' [] = []) ->
           E.is_var_low_context (nth (i + 1) Gs E.mt))) ->
      process_seq_output coms md0 mds Gs Ks Ks' Ks'' comsout Gsout Ksout ->
      length Gs = length coms + 1 ->
      length Ks = length coms ->
      length Ks' = length coms ->
      length Ks'' = length coms ->
      length mds = length coms ->
      (forall i,
          i < length coms ->
          E.com_type pc (nth i mds E.Normal) (nth i Gs E.mt)
                     (nth i Ks []) U d (nth i coms E.Cskip)
                     (nth (i + 1) Gs E.mt) (nth i Ks' [])) ->
      U = [] \/ md0 <> E.Normal ->
      length Gsout = length comsout + 1 /\
      length Ksout = length comsout + 1 /\
      (forall i,
          i < length comsout ->
          E.com_type pc md0 (nth i Gsout E.mt) (nth i Ksout []) U d
                     (nth i comsout E.Cskip)
                     (nth (i + 1) Gsout E.mt) (nth (i + 1) Ksout [])).
  Proof.
    intros comsout Gsout Ksout Ks' Ks'' Hunion Hinter HKs''empty Hcontext
           Hpso HGslen HKslen HKs'len HKs''len Hmdslen Hwt HU.
    induction Hpso.
    - repeat split; auto.
      rewrite <- HKs'len. simpl. omega.
      intros. assert (nth i mds E.Normal = md0) as Hmd0.
      {
        rewrite Forall_forall in H. apply H. apply nth_In. omega.
      }
      destruct (Nat.eq_dec i 0).
      + rewrite e. simpl. apply Hwt in H1. now subst.
      + rewrite Nat.neq_0_r in n. destruct n as [ m n ].
        assert (nth i (nth 0 Ks [] :: Ks') = nth m Ks') by
            (rewrite n; reflexivity).
        rewrite H2. assert (m < length Ks - 1) by omega.
        assert (m < length Ks'') by omega.
        apply Hwt in H1. rewrite Hmd0 in H1.
        assert (nth i Ks [] = nth m Ks' []).
        {
          apply Hunion in H3.
          replace (nth m Ks'' []) with ([]:list E.enclave) in H3.
          simpl in H3. replace (m + 1) with i in H3; auto. omega.
          rewrite Forall_forall in H0. symmetry. apply H0. now apply nth_In.
        }
        rewrite <- H5. now rewrite <- nth_eq_nth_S_cons.
    Admitted.

  (*
    .
    intro Hunion.
    intro Hinter.
    intro HKs''empty.
    intro 
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
      + intros. (*
        assert (i + 1 < length mds).
        {
          rewrite H4. simpl. omega.
        }
        apply Hmds in H12. *)
        pose (Hmds (i + 1)) as H12.
        rewrite H6 in H12.
        rewrite H4 in H12.
        replace (nth (i + 1) (E.Normal :: mds') E.Normal) with
        (nth i mds' E.Normal) in H12.
        replace (nth (i + 1 + 1) (E.Normal :: mds') E.Normal) with
        (nth (i + 1) mds' E.Normal) in H12.
        apply H12 in H10. now rewrite <- nth_eq_nth_S_cons in H10.
        1-2: now rewrite <- nth_eq_nth_S_cons.
      + rewrite H5 in H1. rewrite H7 in H1. simpl in *. omega.
      + subst. simpl in *. omega.
      + intros.
        assert (S i < length coms).
        {
          rewrite H5. simpl. omega.
        }
        apply H3 in H11. subst. simpl in *. eauto.
    - pose HUmd0 as HUmd0'. eapply IHprocess_seq_output in HUmd0'; eauto;
                              destruct_conjs.
      + repeat split. 1-2: simpl in *; omega.
        intros. destruct (Nat.eq_dec i 0). rewrite e in *. simpl.
        rewrite H13. rewrite H. constructor.
        eapply E.CTseq with (Gs:=G1 :: Gs1 ++ [G2]) (Ks:=K1 :: Ks1 ++ [K2]);
          eauto.
        1-2: rewrite app_comm_cons; rewrite app_length.
        rewrite H10. simpl. omega.
        rewrite H12. simpl. omega.
        intros.
        assert (length coms1 <= length coms).
        {
          rewrite H7. rewrite app_length. omega.
        }
        assert (i0 < length coms) by omega.
        apply H3 in H21. subst.
        assert (nth i0 (mds1 ++ mds2) E.Normal = nth i0 mds1 E.Normal).
        {
          apply app_nth1. omega.
        }
        assert (nth i0 mds1 E.Normal = E.Encl j).
        {
          rewrite Forall_forall in H5.
          assert (i0 < length mds1) by omega.
          apply nth_In with (d:=E.Normal) in H4.
          now apply (H5 _ H4).
        }
        rewrite H in H21. rewrite H4 in H21.
        assert (length (G1 :: Gs1 ++ [G2]) = length (K1 :: Ks1 ++ [K2])).
        {
          repeat rewrite app_comm_cons. repeat rewrite app_length.
          rewrite H10. rewrite H12. reflexivity.
        }
        assert (i0 + 1 < length (G1 :: Gs1 ++ [G2])).
        {
          rewrite app_comm_cons. rewrite app_length.
          rewrite H10. simpl. omega.
        }
        replace (nth i0 (G1 :: Gs1 ++ G2 :: Gs2) E.mt) with
        (nth i0 (G1 :: Gs1 ++ [G2]) E.mt) in H21.
        replace (nth i0 (K1 :: Ks1 ++ K2 :: Ks2) []) with
        (nth i0 (K1 :: Ks1 ++ [K2]) []) in H21.
        rewrite app_nth1 in H21; auto.
        replace (nth (i0 + 1) (G1 :: Gs1 ++ G2 :: Gs2) E.mt) with
        (nth (i0 + 1) (G1 :: Gs1 ++ [G2]) E.mt) in H21.
        replace (nth (i0 + 1) (K1 :: Ks1 ++ K2 :: Ks2) []) with
        (nth (i0 + 1) (K1 :: Ks1 ++ [K2]) []) in H21.
        replace U with ([]:set condition) in H21. auto.
        1: destruct U; auto. destruct HUmd0. discriminate. now contradict H11.
        1-4: rewrite app_comm_cons; rewrite app_cons_helper;
          rewrite <- app_comm_cons; symmetry; apply app_nth1; omega.
        1-2: rewrite app_comm_cons; now rewrite last_app.
        * pose (Hmds (length mds1 - 1)).
          assert (nth (length mds1 - 1) mds E.Normal = E.Encl j).
          {
            simpl in H10.
            replace (nth (length mds1 - 1) mds E.Normal) with
            (nth (length mds1 - 1) mds1 E.Normal).
            rewrite Forall_forall in H5. apply H5.
            apply nth_In. omega.
            rewrite H4. symmetry. apply app_nth1. omega.
          }
          rewrite H19 in i0.
          assert (E.Encl j <> nth (length mds1 - 1 + 1) mds E.Normal).
          {
            rewrite H4.
            replace (nth (length mds1 - 1 + 1) (mds1 ++ mds2) E.Normal) with
            (nth 0 mds2 E.Normal).
            intuition.
            rewrite app_nth2. simpl in H10.
            now replace (length mds1 - 1 + 1 - length mds1) with 0 by omega.
            omega.
          }
          assert (E.Encl j <> E.Normal) by (contradict H; discriminate).
          replace (nth (length mds1 - 1 + 1) Gs E.mt) with G2 in i0.
          apply i0; intuition.
          rewrite H9. replace (length mds1 - 1 + 1) with (length (G1 :: Gs1)).
          symmetry. rewrite app_comm_cons. now rewrite nth_app_helper_x.
          rewrite H10. simpl in H10. omega.
        * rewrite Nat.neq_0_r in n. destruct n as [ m n ].
          replace (S m) with (m + 1) in n by omega.
          rewrite n. repeat rewrite <- nth_eq_nth_S_cons.
          assert (m < length coms').
          {
            rewrite n in H18. simpl in H18. omega.
          }
          apply H17 in H19.
          repeat rewrite <- nth_eq_nth_S_cons in H19. auto.
      + intros.
        assert (forall k,
                   nth k mds2 E.Normal = nth (length mds1 + k) mds E.Normal).
        {
          intros. rewrite H4. symmetry.
          remember (length mds1 + k) as n.
          replace k with (n - length mds1) by omega.
          eapply app_nth2; omega.
        }
        rewrite (H16 i) in H15.
        rewrite (H16 (i + 1)) in H15.
        rewrite plus_assoc in H15.
        apply Hmds in H15.
        rewrite H9 in H15.
        replace (length mds1 + i + 1) with (length (G1 :: Gs1) + i + 1) in H15.
        rewrite app_comm_cons in H15.
        rewrite app_nth2 in H15.
        replace (length (G1 :: Gs1) + i + 1 - length (G1 :: Gs1))
        with (i + 1) in H15 by omega. auto.
        1-2: omega.
      + rewrite H9 in H0. rewrite H7 in H0.
        rewrite app_comm_cons in H0.
        repeat rewrite app_length in H0. omega.
      + rewrite H11 in H1. rewrite H7 in H1.
        rewrite app_comm_cons in H1.
        repeat rewrite app_length in H1. omega.
      + rewrite H4 in H2. rewrite H7 in H2.
        repeat rewrite app_length in H2. omega.
      + intros.
        rewrite (nth_app_helper_xs mds1 mds2 _ _).
        repeat rewrite (nth_app_helper_xs (G1 :: Gs1) (G2 :: Gs2) _ _).
        repeat rewrite (nth_app_helper_xs (K1 :: Ks1) (K2 :: Ks2) _ _).
        rewrite (nth_app_helper_xs coms1 coms2 _ _).
        rewrite H10. rewrite H12. rewrite H8.
        repeat rewrite <- app_comm_cons. subst.
        assert (length mds1 + i < length (coms1 ++ coms2)).
        {
          rewrite app_length. omega.
        }
        repeat rewrite plus_assoc. now apply H3.
  Qed.
*)
  
  Lemma process_seq_output_wt (pc: policy) (md0: E.mode) (mds: list E.mode)
        (Gs: list E.context) (Ks Ks' Ks'': list (list E.enclave))
        (d: E.loc_mode) (U: set condition) (coms: list E.com) :
    forall comsout Gsout Ksout,
      (forall (i: nat),
          (nth i mds E.Normal <> E.Normal /\
           (nth i mds E.Normal <> nth (i + 1) mds E.Normal \/
            nth i Ks'' [] = []) ->
           E.is_var_low_context (nth (i + 1) Gs E.mt))) ->
      (forall i,
          i < length Ks - 1 ->
          nth (i + 1) Ks [] = union (nth i Ks' []) (nth i Ks'' [])) ->
      (forall i,
          Forall (fun e => ~In e (nth i Ks' [])) (nth i Ks'' [])) ->
      (forall i,
          i < length mds - 1 ->
          nth i mds E.Normal <> E.Normal /\
          nth i mds E.Normal = nth (i + 1) mds E.Normal ->
          nth i Ks'' [] = []) ->
      U = [] \/ md0 <> E.Normal ->
      length Gs = length coms + 1 ->
      length Ks = length coms ->
      length Ks' = length coms ->
      length Ks'' = length coms ->
      length mds = length coms ->
      (forall i,
          i < length coms ->
          E.com_type pc (nth i mds E.Normal) (nth i Gs E.mt)
                     (nth i Ks []) U d (nth i coms E.Cskip)
                     (nth (i + 1) Gs E.mt) (nth i Ks' [])) ->
      process_seq_output coms md0 mds Gs Ks Ks' Ks'' comsout Gsout Ksout ->
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
    - eapply process_seq_output_wt; eauto; rewrite e5 in *; auto;
        simpl in e1; omega.
  Qed.
  
End TransProof.