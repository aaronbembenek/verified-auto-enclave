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
  Inductive kill2 : Type :=
  | KSingle: set enclave -> kill2
  | KPair: set enclave -> set enclave -> kill2.

  Inductive event2 : Type :=
  | Emp2 : event2
  | Decl2 : exp -> mem2 -> event2
  | Mem2 : mem2 -> event2
  | Out2 : sec_level -> val2 -> event2
  | ANonEnc2 : com -> event2
  | AEnc2 : forall c c' : com, enc_equiv c c' -> event2
  | EPair : event2 -> event2 -> event2.
  Definition trace2 : Type := list event2.

  (* Mode is only alive if it is alive in both of the kill sets in a pair *)
  (* XXX: not sure if this definition is right but it seems reasonable *)
  (* Seems right---both sides of kill pair are equal when it's well-typed *)
  Function mode_alive2 (md : mode) (k : kill2) :=
    match md with
    | Normal => True
    | Encl i =>
      match k with
      | KSingle ks => ~set_In i ks
      | KPair ks1 ks2 => mode_alive md ks1 /\ mode_alive md ks2
      end
    end.
  Definition mode_access_ok2 (md : mode) (d : loc_mode) (l : location) (k : kill2) :=
    let lmd := d l in
    match lmd with
    | Normal => True
    | Encl _ => md = lmd /\ mode_alive2 lmd k
    end.
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
  Definition merge_kill (k1 k2: set enclave) := KPair k1 k2.

  Definition add_to_kill2 (e : enclave) (k : kill2) : kill2 :=
    match k with
    | KSingle ks => KSingle (set_add Nat.eq_dec e ks)
    | KPair ks1 ks2 => KPair (set_add Nat.eq_dec e ks1) (set_add Nat.eq_dec e ks2)
    end.
  
  Function project_value (v: val2) (is_left: bool): val :=
    match v with
      (* XXX pretty sure we can't have nested value pairs *)
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
  Function project_kill (k: kill2) (is_left : bool) : set enclave :=
    match k with
    | KPair ks1 ks2 => if is_left then ks1 else ks2
    | KSingle k => k
    end.
  
  Lemma mode_alive_project_alive : forall md k is_left,
      mode_alive2 md k -> mode_alive md (project_kill k is_left).
  Proof.
    intros.
    destruct k; simpl; auto.
    destruct md; simpl; auto; unfold mode_alive2 in H; destruct_conjs.
    destruct is_left; unfold mode_alive in *; auto.
  Qed.

  Lemma mode_access_ok_project_ok : forall md d l k is_left,
      mode_access_ok2 md d l k -> mode_access_ok md d l (project_kill k is_left).
    intros.
    destruct k; simpl; auto.
    assert ((if is_left then s else s0) = project_kill (KPair s s0) is_left) by
        (destruct is_left; auto);
    destruct md; simpl; auto; unfold mode_access_ok2 in H; destruct_conjs;
    remember (d l) as mem_mode; destruct mem_mode; unfold mode_access_ok;
      rewrite <- Heqmem_mode; auto; destruct_conjs; split; auto;
    rewrite H0; apply mode_alive_project_alive; auto.
  Qed.
  
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
  
  Definition econfig2 : Type := exp * reg2 * mem2 * kill2.
  Definition ecfg_exp2 (ecfg: econfig2) : exp :=
    match ecfg with (e, _, _, _) => e end.
  Definition ecfg_reg2 (ecfg: econfig2) : reg2 :=
    match ecfg with (_, r, _, _) => r end.
  Definition ecfg_mem2 (ecfg: econfig2) : mem2 :=
    match ecfg with (_, _, m, _) => m end.
  Definition ecfg_kill2 (ecfg: econfig2) : kill2 :=
    match ecfg with (_, _, _, k) => k end.
  Definition ecfg_update_exp2 (ecfg: econfig2) (e: exp) : econfig2 :=
    match ecfg with (_, r, m, k) => (e, r, m, k) end.
  Definition esemantics2 : Type := mode -> loc_mode -> econfig2 -> val2 -> Prop.

   Definition project_ecfg (ecfg : econfig2) (is_left : bool) : econfig :=
    (ecfg_exp2 ecfg, project_reg (ecfg_reg2 ecfg) is_left,
     project_mem (ecfg_mem2 ecfg) is_left, project_kill (ecfg_kill2 ecfg) is_left).

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
  | Estep2_binop : forall md d ecfg e1 e2 n1 n2 op,
      ecfg_exp2 ecfg = Ebinop e1 e2 op ->
      estep2 md d (ecfg_update_exp2 ecfg e1) (VSingle (Vnat n1)) ->
      estep2 md d (ecfg_update_exp2 ecfg e2) (VSingle (Vnat n2)) ->
      estep2 md d ecfg (VSingle (Vnat (op n1 n2)))
  | Estep2_deref : forall md d ecfg e r m k l v,
      ecfg = (Ederef e, r, m, k) ->
      estep2 md d (e, r, m, k) (VSingle (Vloc l)) ->
      m l = v ->
      mode_access_ok2 md d l k ->
      estep2 md d ecfg v
  | Estep2_isunset : forall md d ecfg cnd v res,
      ecfg_exp2 ecfg = Eisunset cnd ->
      estep2 md d (ecfg_update_exp2 ecfg (Ederef (Eloc (Cnd cnd)))) v ->
      (v = VSingle (Vnat 0) /\ res = VSingle (Vnat 1))
      \/ (v = VSingle (Vnat 1) /\ res = VSingle (Vnat 0)) ->
      estep2 md d ecfg res.

  (* Semantics for commands. *)
  Definition cconfig2 : Type := com * reg2 * mem2 * kill2.
  Definition cterm2 : Type := reg2 * mem2 * kill2.
  Definition ccfg_com2 (ccfg: cconfig2) : com :=
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
  Definition ccfg_to_ecfg2 (e: exp) (ccfg : cconfig2) : econfig2 :=
    (e, (ccfg_reg2 ccfg), (ccfg_mem2 ccfg), (ccfg_kill2 ccfg)).
  Definition ccfg_update_com2 (c: com) (ccfg : cconfig2) : cconfig2 :=
    (c, (ccfg_reg2 ccfg), (ccfg_mem2 ccfg), (ccfg_kill2 ccfg)).
  Definition csemantics2 : Type := mode -> loc_mode -> cconfig2 -> cterm2 -> trace2 -> Prop.  

  Definition project_ccfg (ccfg : cconfig2) (is_left : bool) : cconfig :=
    (ccfg_com2 ccfg, project_reg (ccfg_reg2 ccfg) is_left,
     project_mem (ccfg_mem2 ccfg) is_left, project_kill (ccfg_kill2 ccfg) is_left).

  Inductive cstep2 : csemantics2 := 
  | Cstep2_skip : forall md d ccfg,
      ccfg_com2 ccfg = Cskip ->
      mode_alive2 md (ccfg_kill2 ccfg) ->
      cstep2 md d ccfg (ccfg_reg2 ccfg, ccfg_mem2 ccfg, ccfg_kill2 ccfg) []
  | Cstep2_assign : forall md d ccfg x e v r',
      ccfg_com2 ccfg = Cassign x e ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) v ->
      r' = ccfg_update_reg2 ccfg x v ->
      mode_alive2 md (ccfg_kill2 ccfg) ->
      cstep2 md d ccfg (r', ccfg_mem2 ccfg, ccfg_kill2 ccfg) []
  | Cstep2_declassify : forall md d ccfg x e v r',
      ccfg_com2 ccfg = Cdeclassify x e ->
      exp_novars e ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) v ->
      r' = ccfg_update_reg2 ccfg x v ->
      mode_alive2 md (ccfg_kill2 ccfg) ->
      cstep2 md d ccfg (r', ccfg_mem2 ccfg, ccfg_kill2 ccfg) [Decl2 e (ccfg_mem2 ccfg)]
  | Cstep2_update : forall md d ccfg e1 e2 l v m',
      ccfg_com2 ccfg = Cupdate e1 e2 ->
      estep2 md d (ccfg_to_ecfg2 e1 ccfg) (VSingle (Vloc l)) ->
      estep2 md d (ccfg_to_ecfg2 e2 ccfg) v ->
      mode_alive2 md (ccfg_kill2 ccfg) ->
      mode_access_ok2 md d l (ccfg_kill2 ccfg) ->
      is_Not_cnd l ->
      m' = ccfg_update_mem2 ccfg l v ->
      cstep2 md d ccfg (ccfg_reg2 ccfg, m', ccfg_kill2 ccfg) []
  | Cstep2_output : forall md d ccfg e sl v,
      ccfg_com2 ccfg = Coutput e sl ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) v ->
      sl = L \/ sl = H ->
      mode_alive2 md (ccfg_kill2 ccfg) ->
      cstep2 md d ccfg (ccfg_reg2 ccfg, ccfg_mem2 ccfg, ccfg_kill2 ccfg)
            [Mem2 (ccfg_mem2 ccfg); Out2 sl v]
  | Cstep2_call : forall md d ccfg e c r' m' k' tr,
      ccfg_com2 ccfg = Ccall e ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (VSingle (Vlambda md c)) ->
      cstep2 md d (ccfg_update_com2 c ccfg) (r', m', k') tr ->
      cstep2 md d ccfg (r', m', k') tr
  | Cstep2_call_div : forall md d ccfg e c1 c2 r1 m1 k1 t1 r2 m2 k2 t2 rmerge mmerge,
      ccfg_com2 ccfg = Ccall e ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (VPair (Vlambda md c1) (Vlambda md c2)) ->
      cstep md d (c1, project_reg (ccfg_reg2 ccfg) true,
                  project_mem (ccfg_mem2 ccfg) true,
                  project_kill (ccfg_kill2 ccfg) true)
             (r1, m1, k1) t1 ->
      cstep md d (c2, project_reg (ccfg_reg2 ccfg) false,
                  project_mem (ccfg_mem2 ccfg) false,
                  project_kill (ccfg_kill2 ccfg) false)
            (r2, m2, k2) t2 ->
      merge_reg r1 r2 rmerge ->
      merge_mem m1 m2 mmerge ->
      cstep2 md d ccfg (rmerge, mmerge, merge_kill k1 k2) (merge_trace (t1, t2))
  | Cstep2_cset : forall md d ccfg c m',
      ccfg_com2 ccfg = Cset c ->
      mode_access_ok2 md d (Cnd c) (ccfg_kill2 ccfg) ->
      m' = ccfg_update_mem2 ccfg (Cnd c) (VSingle (Vnat 1)) ->
      mode_alive2 md (ccfg_kill2 ccfg) ->
      cstep2 md d ccfg (ccfg_reg2 ccfg, m', ccfg_kill2 ccfg) [Mem2 m']
  | Cstep2_enclave : forall md d ccfg enc c r' m' k' tr,
    md = Normal ->
    ccfg_com2 ccfg = Cenclave enc c ->
    cstep2 (Encl enc) d (c, ccfg_reg2 ccfg, ccfg_mem2 ccfg, ccfg_kill2 ccfg) (r', m', k') tr ->
    cstep2 md d ccfg (r', m', k') tr
  | Cstep2_seq_nil : forall md d ccfg,
      ccfg_com2 ccfg = Cseq [] ->
      cstep2 md d ccfg (ccfg_reg2 ccfg, ccfg_mem2 ccfg, ccfg_kill2 ccfg) []
  | Cstep2_seq_hd : forall md d ccfg hd tl r m k tr r' m' k' tr',
      ccfg_com2 ccfg = Cseq (hd::tl) ->
      cstep2 md d (ccfg_update_com2 hd ccfg) (r, m, k) tr ->
      cstep2 md d (Cseq tl, r, m, k) (r', m', k') tr' ->
      cstep2 md d ccfg (r', m', k') (tr++tr')
  | Cstep2_if : forall md d ccfg e c1 c2 r' m' k' tr,
      ccfg_com2 ccfg = Cif e c1 c2 ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (VSingle (Vnat 1)) ->
      cstep2 md d (ccfg_update_com2 c1 ccfg) (r', m', k') tr ->
      cstep2 md d ccfg (r', m', k') tr
  | Cstep2_else : forall md d ccfg e c1 c2 r' m' k' tr,
      ccfg_com2 ccfg = Cif e c1 c2 ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (VSingle (Vnat 0)) ->
      cstep2 md d (ccfg_update_com2 c2 ccfg) (r', m', k') tr ->
      cstep2 md d ccfg (r', m', k') tr
  | Cstep2_if_div : forall md d ccfg e c1 c2 n1 n2 r1 m1 k1 t1 r2 m2 k2 t2 rmerge mmerge,
      ccfg_com2 ccfg = Cif e c1 c2 ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (VPair (Vnat n1) (Vnat n2)) ->
      let cleft := (match n1 with
                    | 0 => c2
                    | _ => c1 end) in
      cstep md d (cleft, project_reg (ccfg_reg2 ccfg) true,
                  project_mem (ccfg_mem2 ccfg) true,
                  project_kill (ccfg_kill2 ccfg) true)
             (r1, m1, k1) t1 ->
      let cright := (match n2 with
                     | 0 => c2
                     | _ => c1 end) in
      cstep md d (cright, project_reg (ccfg_reg2 ccfg) false,
                  project_mem (ccfg_mem2 ccfg) false,
                  project_kill (ccfg_kill2 ccfg) false)
            (r2, m2, k2) t2 ->
      merge_reg r1 r2 rmerge ->
      merge_mem m1 m2 mmerge ->
      cstep2 md d ccfg (rmerge, mmerge, merge_kill k1 k2) (merge_trace (t1, t2))
  | Cstep2_while_t : forall md d ccfg e c r m k tr r' m' k' tr',
      ccfg_com2 ccfg = Cwhile e c ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (VSingle (Vnat 1)) ->
      cstep2 md d (ccfg_update_com2 c ccfg) (r, m, k) tr ->
      cstep2 md d (ccfg_update_com2 (Cwhile e c) ccfg) (r', m', k') tr' ->
      cstep2 md d ccfg (r', m', k') (tr++tr')
  | Cstep2_while_f : forall md d ccfg e c,
      ccfg_com2 ccfg = Cwhile e c ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (VSingle (Vnat 0)) ->
      mode_alive2 md (ccfg_kill2 ccfg) ->
      cstep2 md d ccfg (ccfg_reg2 ccfg, ccfg_mem2 ccfg, ccfg_kill2 ccfg) []
  | Cstep2_while_div : forall md d ccfg e c n1 n2 r1 m1 k1 t1 r2 m2 k2 t2 rmerge mmerge,
      ccfg_com2 ccfg = Cwhile e c ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (VPair (Vnat n1) (Vnat n2)) ->
      let cleft := (match n1 with
                    | 0 => Cskip
                    | _ => c end) in
      cstep md d (cleft, project_reg (ccfg_reg2 ccfg) true,
                  project_mem (ccfg_mem2 ccfg) true,
                  project_kill (ccfg_kill2 ccfg) true)
             (r1, m1, k1) t1 ->
      let cright := (match n2 with
                     | 0 => Cskip
                     | _ => c end) in
      cstep md d (cright, project_reg (ccfg_reg2 ccfg) false,
                  project_mem (ccfg_mem2 ccfg) false,
                  project_kill (ccfg_kill2 ccfg) false)
            (r2, m2, k2) t2 ->
      merge_reg r1 r2 rmerge ->
      merge_mem m1 m2 mmerge ->
      cstep2 md d ccfg (rmerge, mmerge, merge_kill k1 k2) (merge_trace (t1, t2))
  | Cstep2_kill : forall md d ccfg enc,
      md = Normal ->
      ccfg_com2 ccfg = Ckill enc ->
      mode_alive2 (Encl enc) (ccfg_kill2 ccfg) ->
      cstep2 md d ccfg (ccfg_reg2 ccfg, ccfg_mem2 ccfg, add_to_kill2 enc (ccfg_kill2 ccfg)) [].
  
  Hint Constructors cstep2.

  Inductive imm_premise : Prop -> Prop -> Prop :=
  | IPcall: forall md d e r m k r' m' k' tr c,
      estep2 md d (e, r, m, k) (VSingle (Vlambda md c)) ->
      cstep2 md d (c, r, m, k) (r', m', k') tr ->
      imm_premise (cstep2 md d (c, r, m, k) (r', m', k') tr)
                  (cstep2 md d (Ccall e, r, m, k) (r', m', k') tr)
  | IPencl: forall d encl c r m k r' m' k' tr,
      cstep2 (Encl encl) d (c, r, m, k) (r', m', k') tr ->
      imm_premise (cstep2 (Encl encl) d (c, r, m, k) (r', m', k') tr)
                  (cstep2 Normal d (Cenclave encl c, r, m, k) (r', m', k') tr)
  | IPseq1: forall md d c rest r m k r' m' k' r'' m'' k'' tr tr',
      cstep2 md d (c, r, m, k) (r', m', k') tr' ->
      cstep2 md d (Cseq rest, r', m', k') (r'', m'', k'') tr ->
      imm_premise (cstep2 md d (c, r, m, k) (r', m', k') tr')
                  (cstep2 md d (Cseq (c :: rest), r, m, k) (r'', m'', k'')
                          (tr' ++ tr))
  | IPseq2: forall md d c rest r m k r' m' k' r'' m'' k'' tr tr',
      cstep2 md d (c, r, m, k) (r', m', k') tr' ->
      cstep2 md d (Cseq rest, r', m', k') (r'', m'', k'') tr ->
      imm_premise (cstep2 md d (Cseq rest, r', m', k') (r'', m'', k'') tr)
                  (cstep2 md d (Cseq (c :: rest), r, m, k) (r'', m'', k'')
                          (tr' ++ tr))
  | IPif: forall md d c1 c2 e r m k r' m' k' tr tr',
      estep2 md d (e, r, m, k) (VSingle (Vnat 1)) ->
      cstep2 md d (c1, r, m, k) (r', m', k') tr' ->
      cstep2 md d (Cif e c1 c2, r, m, k) (r', m', k') tr ->
      imm_premise (cstep2 md d (c1, r, m, k) (r', m', k') tr)
                  (cstep2 md d (Cif e c1 c2, r, m, k) (r', m', k')
                          (tr' ++ tr))
  | IPelse: forall md d c1 c2 e r m k r' m' k' tr tr',
      estep2 md d (e, r, m, k) (VSingle (Vnat 0)) ->
      cstep2 md d (c2, r, m, k) (r', m', k') tr' ->
      cstep2 md d (Cif e c1 c2, r, m, k) (r', m', k') tr ->
      imm_premise (cstep2 md d (c2, r, m, k) (r', m', k') tr)
                  (cstep2 md d (Cif e c1 c2, r, m, k) (r', m', k')
                          (tr' ++ tr))
  | IPwhilet1: forall md d c e r m k r' m' k' r'' m'' k'' tr tr',
      estep2 md d (e, r, m, k) (VSingle (Vnat 1)) ->
      cstep2 md d (c, r, m, k) (r', m', k') tr' ->
      cstep2 md d (Cwhile e c, r', m', k') (r'', m'', k'') tr ->
      imm_premise (cstep2 md d (c, r, m, k) (r'', m'', k'') tr')
                  (cstep2 md d (Cwhile e c, r, m, k) (r'', m'', k'')
                          (tr' ++ tr))
  | IPwhilet2: forall md d c e r m k r' m' k' r'' m'' k'' tr tr',
      estep2 md d (e, r, m, k) (VSingle (Vnat 1)) ->
      cstep2 md d (c, r, m, k) (r', m', k') tr' ->
      cstep2 md d (Cwhile e c, r', m', k') (r'', m'', k'') tr ->
      imm_premise (cstep2 md d (Cwhile e c, r', m', k') (r'', m'', k'') tr)
                  (cstep2 md d (Cwhile e c, r, m, k) (r'', m'', k'')
                          (tr' ++ tr))
  .
  Hint Constructors imm_premise.
End Semantics.
     