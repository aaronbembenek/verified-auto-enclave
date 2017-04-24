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
Require Import ImpE.

(*******************************************************************************
*
* SYNTAX
*
*******************************************************************************)

Section Syntax.
  Inductive val2 : Type :=
  | VSingle: val -> val2
  | VPair: val -> val -> val2.
End Syntax.

(*******************************************************************************
*
* SEMANTICS
*
*******************************************************************************)

Section Semantics.
  Definition reg2 : Type := register val2.
  Definition reg_init2 : reg2 := fun x => VSingle (Vnat 0).
  Definition mem2 : Type := memory val2.

  Inductive event2 : Type :=
  | Emp2 : event2
  | Decl2 : exp -> mem2 -> event2
  | Mem2 : mem2 -> event2
  | Out2 : sec_level -> val2 -> event2
  | ANonEnc2 : com -> event2
  | AEnc2 : forall c c' : com, enc_equiv c c' -> event2
  | EPair : event2 -> event2 -> event2.
  Definition trace2 : Type := list event2.

  Definition val_to_val2 (v: val) : val2 := VSingle v.
  Definition mem_to_mem2 (m: mem) : mem2 := fun x => val_to_val2 (m x).
  Inductive merge_reg (r1 r2: reg) : reg2 -> Prop :=
  | rmerge : forall r,
      (forall x, r1 x <> r2 x -> r x = VPair (r1 x) (r2 x))
      -> (forall y, r1 y = r2 y -> r y = val_to_val2 (r1 y))
      -> merge_reg r1 r2 r.
  Inductive merge_mem (m1 m2: mem) : mem2 -> Prop :=
  | mmerge : forall m,
      (forall x, m1 x <> m2 x -> m x = VPair (m1 x) (m2 x))
      -> (forall y, m1 y = m2 y -> m y = val_to_val2 (m1 y))
      -> merge_mem m1 m2 m.
  Definition event_to_event2 (e: event) : event2 :=
    match e with
      | Mem m => Mem2 (mem_to_mem2 m)
      | Decl e m => Decl2 e (mem_to_mem2 m)
      | Out l v => Out2 l (val_to_val2 v)
      | ANonEnc c => ANonEnc2 c
      | AEnc c1 c2 enc_equiv => AEnc2 c1 c2 enc_equiv
      | Emp => Emp2
    end.
  Definition tracepair_len (t: trace * trace) := length (fst t) + length (snd t).
  Function merge_trace (t: trace * trace) {measure tracepair_len t} : trace2 :=
    match fst t, snd t with
    | a1::tl1, a2::tl2 => EPair (event_to_event2 a1)
                                 (event_to_event2 a2) :: (merge_trace (tl1, tl2))
    | a1::tl1, [] => EPair (event_to_event2 a1) Emp2 :: merge_trace (tl1, [])
    | [], a2::tl2 => EPair Emp2 (event_to_event2 a2) :: merge_trace ([], tl2)
    | _, _ => []
    end.
  Proof. all: intros; unfold tracepair_len; rewrite teq, teq0; simpl; omega. Qed.
  
  Function project_value (v: val2) (is_left: bool): val :=
    match v with
    | VPair v1 v2 => if is_left then v1 else v2
    | VSingle v => v
    end.
  Definition project_reg (r: reg2) (is_left : bool): reg :=
    fun x => match r x with
             | VPair v1 v2 => if is_left then v1 else v2
             | VSingle v => v
          end.
  Definition project_mem (m: mem2) (is_left : bool): mem :=
    fun x => match m x with
             | VPair v1 v2 => if is_left then v1 else v2
             | VSingle v => v
          end.
    
  (* XXX show event pairs are never nested *)
  Function event2_to_event (e: event2) (is_left: bool): event :=
     match e with
      | Mem2 m => Mem (project_mem m is_left)
      | Decl2 e m => Decl e (project_mem m is_left)
      | Out2 l v => Out l (project_value v is_left)
      | ANonEnc2 c => ANonEnc c
      | AEnc2 c1 c2 enc_equiv => AEnc c1 c2 enc_equiv
      | EPair e1 e2 => if is_left then event2_to_event e1 is_left
                        else event2_to_event e2 is_left
      | Emp2 => Emp
     end.
  Function project_trace (t: trace2) (is_left : bool) : trace :=
    match t with
    | [] => []
    | hd :: tl => let hd_proj := (event2_to_event hd is_left) in
      match hd_proj with
      | Emp => project_trace tl is_left
      | _ => hd_proj :: project_trace tl is_left
      end
    end.

  Lemma project_trace_app (t1 t2: trace2) (is_left: bool) :
    project_trace t1 is_left ++ project_trace t2 is_left
    = project_trace (t1 ++ t2) is_left.
  Proof.
    induction t1, t2; simpl in *; auto.
    rewrite app_nil_r in *; rewrite (app_nil_r t1) in *; auto.
    destruct (event2_to_event a is_left); rewrite <- IHt1; auto.
  Qed.

  Definition econfig2 : Type := exp * reg2 * mem2.
  Definition ecfg_exp2 (ecfg: econfig2) : exp :=
    match ecfg with (e, _, _) => e end.
  Definition ecfg_reg2 (ecfg: econfig2) : reg2 :=
    match ecfg with (_, r, _) => r end.
  Definition ecfg_mem2 (ecfg: econfig2) : mem2 :=
    match ecfg with (_, _, m) => m end.
  Definition ecfg_update_exp2 (ecfg: econfig2) (e: exp) : econfig2 :=
    match ecfg with (_, r, m) => (e, r, m) end.
  Definition esemantics2 : Type := mode -> loc_mode -> econfig2 -> val2 -> Prop.

   Definition project_ecfg (ecfg : econfig2) (is_left : bool) : econfig :=
    (ecfg_exp2 ecfg, project_reg (ecfg_reg2 ecfg) is_left,
     project_mem (ecfg_mem2 ecfg) is_left).

   Definition contains_nat (v : val2) :=
     (exists n1, v = VSingle (Vnat n1)) \/
     (exists n1 n2, v = VPair (Vnat n1) (Vnat n2)).

   Fixpoint apply_op (op : nat -> nat -> nat) (v1 v2 : val2) :=
     match v1, v2 with
     | VSingle (Vnat n1), VSingle (Vnat n2) => VSingle (Vnat (op n1 n2))
     | VSingle (Vnat n1), VPair (Vnat n2) (Vnat n3) => VPair (Vnat (op n1 n2)) (Vnat (op n1 n3))
     | VPair (Vnat n1) (Vnat n2), VPair (Vnat n3) (Vnat n4) =>
                                  VPair (Vnat (op n1 n3)) (Vnat (op n2 n4))
     | _, _ => v1
     end.

   Lemma apply_op_pair (op : nat -> nat -> nat) (v1 v2: val2) :
       contains_nat v1 /\ contains_nat v2 /\
       (exists v3 v4, apply_op op v1 v2 = VPair v3 v4) <->
       exists v' v'', contains_nat v1 /\ contains_nat v2 /\
                      (v1 = VPair v' v'' \/ v2 = VPair v' v'').
   Proof.
     intros.
     split; intros; destruct_pairs.
     induction v1, v2; unfold apply_op in *; destruct H1; destruct H1.
     destruct v, v0; try discriminate.
     - destruct v, v0; try discriminate.
       destruct v1; try discriminate.
       exists (Vnat n0). exists (Vnat n1).
       split; auto. 
     - destruct v, v0; try discriminate.
       1-4: unfold contains_nat in H; destruct H; destruct H;
         [discriminate | destruct H; inversion H].
       2-5: unfold contains_nat in H; destruct H; destruct H;
         [discriminate | destruct H; inversion H].
       exists (Vnat n). exists (Vnat n0). split; auto.
     - destruct v, v0; try discriminate.
       1-4: unfold contains_nat in H; destruct H; destruct H;
         [discriminate | destruct H; inversion H].
       2-5: unfold contains_nat in H; destruct H; destruct H;
         [discriminate | destruct H; inversion H].
       exists (Vnat n). exists (Vnat n0). split; auto.
     - destruct H. destruct H. destruct H; destruct_pairs.
       split; [ | split]; auto.
       destruct H1.
       -- rewrite H1. destruct v2; destruct v.
          destruct H0; destruct H0; [discriminate | destruct H0; inversion H0].
          2-5: destruct H0; destruct H0; [discriminate | destruct H0; inversion H0].
          unfold apply_op.
          exists x. exists x0. destruct x; auto. destruct x0; auto.
          unfold apply_op.
          destruct x; auto. exists (Vlambda m c). exists x0; auto.
          destruct x0; auto. exists (Vnat n0). exists (Vlambda m c); auto.
          exists (Vnat (op n0 x1)). exists (Vnat (op n1 x2)); auto.
          exists (Vnat n0). exists (Vloc l). auto.
          exists (Vloc l). exists x0. auto.
       -- rewrite H1 in *. destruct v1; destruct v.
          destruct H; destruct H; [discriminate | destruct H; inversion H].
          2-5: destruct H; destruct H; [discriminate | destruct H; inversion H].
          unfold apply_op.
          destruct x. destruct H0; destruct H0; [discriminate | destruct H0; inversion H0].
          destruct x0. destruct H0; destruct H0; [discriminate | destruct H0; inversion H0].
          exists (Vnat (op n n0)). exists (Vnat (op n n1)). auto.
          destruct H0; destruct H0; [discriminate | destruct H0; inversion H0].
          destruct H0; destruct H0; [discriminate | destruct H0; inversion H0].
          unfold apply_op.
          destruct x; auto. exists (Vnat x1). exists (Vnat x2). auto.
          destruct x0; auto. exists (Vnat x1). exists (Vnat x2); auto.
          exists (Vnat (op x1 n0)). exists (Vnat (op x2 n1)); auto.
          1-2: exists (Vnat x1); exists (Vnat x2); auto.
   Qed.
       
   Inductive estep2 : esemantics2 :=
  | Estep2_nat : forall md d ecfg n,
      ecfg_exp2 ecfg = Enat n ->
      estep2 md d ecfg (VSingle (Vnat n))
  | Estep2_loc : forall md d ecfg l,
      ecfg_exp2 ecfg = Eloc l ->
      estep2 md d ecfg (VSingle (Vloc l))
  | Estep2_lambda : forall md d ecfg c,
      ecfg_exp2 ecfg = Elambda md c ->
      estep2 md d ecfg (VSingle (Vlambda md c))
  | Estep2_var : forall md d ecfg x v,
      ecfg_exp2 ecfg = Evar x ->
      ecfg_reg2 ecfg x = v ->
      estep2 md d ecfg v
  | Estep2_binop : forall md d ecfg e1 e2 v1 v2 op,
      ecfg_exp2 ecfg = Ebinop e1 e2 op ->
      estep2 md d (ecfg_update_exp2 ecfg e1) v1 ->
      estep2 md d (ecfg_update_exp2 ecfg e2) v2 ->
      contains_nat v1 /\ contains_nat v2 ->
      estep2 md d ecfg (apply_op op v1 v2)
  | Estep2_deref : forall md d ecfg e r m l v,
      ecfg = (Ederef e, r, m) ->
      estep2 md d (e, r, m) (VSingle (Vloc l)) ->
      m l = v ->
      mode_access_ok md d l ->
      estep2 md d ecfg v.
  
  (* Semantics for commands. *)
  Definition cconfig2 : Type := com * reg2 * mem2.
  Definition cterm2 : Type := reg2 * mem2.
  Definition ccfg_com2 (ccfg: cconfig2) : com :=
    match ccfg with (c, _, _) => c end.
  Definition ccfg_reg2 (ccfg: cconfig2) : reg2 :=
    match ccfg with (_, r, _) => r end.
  Definition ccfg_mem2 (ccfg: cconfig2) : mem2 :=
    match ccfg with (_, _, m) => m end.
  Definition ccfg_update_mem2 (ccfg: cconfig2) (l: location) (v: val2) : mem2 := 
    fun loc => if loc =? l then v
               else (ccfg_mem2 ccfg) loc.
  Definition ccfg_update_reg2 (ccfg: cconfig2) (x: var) (v: val2) : reg2 :=
    fun var => if var =? x then v
               else (ccfg_reg2 ccfg) var.
  Definition ccfg_to_ecfg2 (e: exp) (ccfg : cconfig2) : econfig2 :=
    (e, (ccfg_reg2 ccfg), (ccfg_mem2 ccfg)).
  Definition ccfg_update_com2 (c: com) (ccfg : cconfig2) : cconfig2 :=
    (c, (ccfg_reg2 ccfg), (ccfg_mem2 ccfg)).
  Definition csemantics2 : Type := mode -> loc_mode -> cconfig2 -> cterm2 -> trace2 -> Prop.  

  Definition project_ccfg (ccfg : cconfig2) (is_left : bool) : cconfig :=
    (ccfg_com2 ccfg, project_reg (ccfg_reg2 ccfg) is_left,
     project_mem (ccfg_mem2 ccfg) is_left).

  Inductive cstep2 : csemantics2 := 
  | Cstep2_skip : forall md d ccfg,
      ccfg_com2 ccfg = Cskip ->
      cstep2 md d ccfg (ccfg_reg2 ccfg, ccfg_mem2 ccfg) []
  | Cstep2_assign : forall md d ccfg x e v r',
      ccfg_com2 ccfg = Cassign x e ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) v ->
      r' = ccfg_update_reg2 ccfg x v ->
      cstep2 md d ccfg (r', ccfg_mem2 ccfg) []
  | Cstep2_declassify : forall md d ccfg x e v r',
      ccfg_com2 ccfg = Cdeclassify x e ->
      exp_novars e ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) v ->
      r' = ccfg_update_reg2 ccfg x v ->
      cstep2 md d ccfg (r', ccfg_mem2 ccfg) [Decl2 e (ccfg_mem2 ccfg)]
  | Cstep2_update : forall md d ccfg e1 e2 l v m',
      ccfg_com2 ccfg = Cupdate e1 e2 ->
      estep2 md d (ccfg_to_ecfg2 e1 ccfg) (VSingle (Vloc l)) ->
      estep2 md d (ccfg_to_ecfg2 e2 ccfg) v ->
      m' = ccfg_update_mem2 ccfg l v ->
      cstep2 md d ccfg (ccfg_reg2 ccfg, m') []
  | Cstep2_output : forall md d ccfg e sl v,
      ccfg_com2 ccfg = Coutput e sl ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) v ->
      cstep2 md d ccfg (ccfg_reg2 ccfg, ccfg_mem2 ccfg)
             [Mem2 (ccfg_mem2 ccfg); Out2 sl v]
  | Cstep2_call : forall md d ccfg e c r' m' tr,
      ccfg_com2 ccfg = Ccall e ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (VSingle (Vlambda md c)) ->
      cstep2 md d (ccfg_update_com2 c ccfg) (r', m') tr ->
      cstep2 md d ccfg (r', m') tr
  | Cstep2_call_div : forall md d ccfg e c1 c2 r1 m1 t1 r2 m2 t2 rmerge mmerge,
      ccfg_com2 ccfg = Ccall e ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (VPair (Vlambda md c1) (Vlambda md c2)) ->
      cstep md d (c1, project_reg (ccfg_reg2 ccfg) true,
                  project_mem (ccfg_mem2 ccfg) true)
                  (r1, m1) t1 ->
      cstep md d (c2, project_reg (ccfg_reg2 ccfg) false,
                  project_mem (ccfg_mem2 ccfg) false)                  
            (r2, m2) t2 ->
      merge_reg r1 r2 rmerge ->
      merge_mem m1 m2 mmerge ->
      cstep2 md d ccfg (rmerge, mmerge) (merge_trace (t1, t2))
  | Cstep2_enclave : forall md d ccfg enc c r' m' tr,
    md = Normal ->
    ccfg_com2 ccfg = Cenclave enc c ->
    cstep2 (Encl enc) d (c, ccfg_reg2 ccfg, ccfg_mem2 ccfg) (r', m') tr ->
    cstep2 md d ccfg (r', m') tr
  | Cstep2_seq_nil : forall md d ccfg,
      ccfg_com2 ccfg = Cseq [] ->
      cstep2 md d ccfg (ccfg_reg2 ccfg, ccfg_mem2 ccfg) []
  | Cstep2_seq_hd : forall md d ccfg hd tl r m tr r' m' tr',
      ccfg_com2 ccfg = Cseq (hd::tl) ->
      cstep2 md d (ccfg_update_com2 hd ccfg) (r, m) tr ->
      cstep2 md d (Cseq tl, r, m) (r', m') tr' ->
      cstep2 md d ccfg (r', m') (tr++tr')
  | Cstep2_if : forall md d ccfg e c1 c2 r' m' tr,
      ccfg_com2 ccfg = Cif e c1 c2 ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (VSingle (Vnat 1)) ->
      cstep2 md d (ccfg_update_com2 c1 ccfg) (r', m') tr ->
      cstep2 md d ccfg (r', m') tr
  | Cstep2_else : forall md d ccfg e c1 c2 r' m' tr,
      ccfg_com2 ccfg = Cif e c1 c2 ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (VSingle (Vnat 0)) ->
      cstep2 md d (ccfg_update_com2 c2 ccfg) (r', m') tr ->
      cstep2 md d ccfg (r', m') tr
  | Cstep2_if_div : forall md d ccfg e c1 c2 n1 n2 r1 m1 t1 r2 m2 t2 rmerge mmerge,
      ccfg_com2 ccfg = Cif e c1 c2 ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (VPair (Vnat n1) (Vnat n2)) ->
      n1 < 2 /\ n2 < 2 ->
      let cleft := (match n1 with
                    | 0 => c2
                    | _ => c1 end) in
      cstep md d (cleft, project_reg (ccfg_reg2 ccfg) true,
                  project_mem (ccfg_mem2 ccfg) true)
                  (r1, m1) t1 ->
      let cright := (match n2 with
                     | 0 => c2
                     | _ => c1 end) in
      cstep md d (cright, project_reg (ccfg_reg2 ccfg) false,
                  project_mem (ccfg_mem2 ccfg) false)
                  (r2, m2) t2 ->
      merge_reg r1 r2 rmerge ->
      merge_mem m1 m2 mmerge ->
      cstep2 md d ccfg (rmerge, mmerge) (merge_trace (t1, t2))
  | Cstep2_while_t : forall md d ccfg e c r m tr r' m' tr',
      ccfg_com2 ccfg = Cwhile e c ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (VSingle (Vnat 1)) ->
      cstep2 md d (ccfg_update_com2 c ccfg) (r, m) tr ->
      cstep2 md d (Cwhile e c,r,m) (r', m') tr' ->
      cstep2 md d ccfg (r', m') (tr++tr')
  | Cstep2_while_f : forall md d ccfg e c,
      ccfg_com2 ccfg = Cwhile e c ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (VSingle (Vnat 0)) ->
      cstep2 md d ccfg (ccfg_reg2 ccfg, ccfg_mem2 ccfg) []
  | Cstep2_while_div : forall md d ccfg e c n1 n2 r1 m1 t1 r2 m2 t2 rmerge mmerge,
      ccfg_com2 ccfg = Cwhile e c ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (VPair (Vnat n1) (Vnat n2)) ->
      n1 < 2 /\ n2 < 2 ->
      let cleft := (match n1 with
                    | 0 => Cskip
                    | _ => Cseq [c; Cwhile e c] end) in
      cstep md d (cleft, project_reg (ccfg_reg2 ccfg) true,
                  project_mem (ccfg_mem2 ccfg) true)
                  (r1, m1) t1 ->
      let cright := (match n2 with
                     | 0 => Cskip
                     | _ => Cseq [c; Cwhile e c] end) in
      cstep md d (cright, project_reg (ccfg_reg2 ccfg) false,
                  project_mem (ccfg_mem2 ccfg) false)
                  (r2, m2) t2 ->
      merge_reg r1 r2 rmerge ->
      merge_mem m1 m2 mmerge ->
      cstep2 md d ccfg (rmerge, mmerge) (merge_trace (t1, t2))
  .
  Hint Constructors cstep2.

  Inductive imm_premise : com -> mode -> reg2 -> mem2 -> reg2 -> mem2 -> trace2 ->
                          com -> mode -> reg2 -> mem2 -> reg2 -> mem2 -> trace2 ->
                          loc_mode -> Prop :=
  | IPcall: forall md d e r m r' m' tr c,
      estep2 md d (e, r, m) (VSingle (Vlambda md c)) ->
      cstep2 md d (c, r, m) (r', m') tr ->
      cstep2 md d (Ccall e, r, m) (r', m') tr ->
      imm_premise c md r m r' m' tr
                  (Ccall e) md r m r' m' tr d
  | IPencl: forall d encl c r m r' m' tr,
      cstep2 (Encl encl) d (c, r, m) (r', m') tr ->
      cstep2 Normal d (Cenclave encl c, r, m) (r', m') tr ->
      imm_premise c (Encl encl) r m r' m' tr
                  (Cenclave encl c) Normal r m r' m' tr d
  | IPseq1: forall md d c rest r m r' m' r'' m'' tr tr',
      cstep2 md d (c, r, m) (r', m') tr' ->
      cstep2 md d (Cseq rest, r', m') (r'', m'') tr ->
      cstep2 md d (Cseq (c :: rest), r, m) (r'', m'') (tr' ++ tr) ->
      imm_premise c md r m r' m' tr' 
                  (Cseq (c :: rest)) md r m r'' m'' (tr'++tr) d
  | IPseq2: forall md d c rest r m r' m' r'' m'' tr tr',
      cstep2 md d (c, r, m) (r', m') tr' ->
      cstep2 md d (Cseq rest, r', m') (r'', m'') tr ->
      cstep2 md d (Cseq (c :: rest), r, m) (r'', m'') (tr' ++ tr) ->
      imm_premise (Cseq rest) md r' m' r'' m'' tr
                  (Cseq (c :: rest)) md r m r'' m'' (tr' ++ tr) d
  | IPif: forall md d c1 c2 e r m r' m' tr,
      estep2 md d (e, r, m) (VSingle (Vnat 1)) ->
      cstep2 md d (c1, r, m) (r', m') tr ->
      cstep2 md d (Cif e c1 c2, r, m) (r', m') tr ->
      cstep2 md d (Cif e c1 c2, r, m) (r', m') (tr) ->
      imm_premise c1 md r m r' m' tr
                  (Cif e c1 c2) md r m r' m' tr d
  | IPelse: forall md d c1 c2 e r m r' m' tr,
      estep2 md d (e, r, m) (VSingle (Vnat 0)) ->
      cstep2 md d (c2, r, m) (r', m') tr ->
      cstep2 md d (Cif e c1 c2, r, m) (r', m') tr ->
      imm_premise c2 md r m r' m' tr (Cif e c1 c2) md r m r' m' tr d
  | IPwhilet1: forall md d c e r m r' m' r'' m'' tr tr',
      estep2 md d (e, r, m) (VSingle (Vnat 1)) ->
      cstep2 md d (c, r, m) (r', m') tr' ->
      cstep2 md d (Cwhile e c, r', m') (r'', m'') tr ->
      cstep2 md d (Cwhile e c, r, m) (r'', m'') (tr' ++ tr) ->
      imm_premise c md r m r' m' tr' (Cwhile e c) md r m r'' m'' (tr' ++ tr) d
  | IPwhilet2: forall md d c e r m r' m' r'' m'' tr tr',
      estep2 md d (e, r, m) (VSingle (Vnat 1)) ->
      cstep2 md d (c, r, m) (r', m') tr' ->
      cstep2 md d (Cwhile e c, r', m') (r'', m'') tr ->
      cstep2 md d (Cwhile e c, r, m) (r'', m'') (tr' ++ tr) ->
      imm_premise (Cwhile e c) md r' m' r'' m'' tr
                  (Cwhile e c) md r m r'' m'' (tr' ++ tr) d
  .
  Hint Constructors imm_premise.
End Semantics.
