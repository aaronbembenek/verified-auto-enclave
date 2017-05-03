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

  Definition not_pair_val (v : val2) : Prop :=
    match v with
    | VPair _ _ => False
    | _ => True
    end.
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
  | Update2 : mem2 -> location -> val2 -> event2
  | Assign2 : reg2 -> var -> val2 -> event2
  | ANonEnc2 : com -> event2
  | AEnc2 : forall c c' : com, enc_equiv c c' -> event2
  | EPair : event2 -> event2 -> event2.
  Definition trace2 : Type := list event2.

  Definition val_to_val2 (v: val) : val2 := VSingle v.
  Definition mem_to_mem2 (m: mem) : mem2 := fun x => val_to_val2 (m x).
  Definition reg_to_reg2 (r: reg) : reg2 := fun x => val_to_val2 (r x).
  Function merge_reg (r1 r2 : reg) : reg2 :=
    fun x =>
      if (val_decidable (r1 x) (r2 x)) then VSingle (r1 x) else VPair (r1 x) (r2 x).
  Function merge_mem (m1 m2 : mem) : mem2 :=
    fun l =>
      if (val_decidable (m1 l) (m2 l)) then VSingle (m1 l) else VPair (m1 l) (m2 l).

  Definition event_to_event2 (e: event) : event2 :=
    match e with
      | Mem m => Mem2 (mem_to_mem2 m)
      | Decl e m => Decl2 e (mem_to_mem2 m)
      | Out l v => Out2 l (val_to_val2 v)
      | Update m l v => Update2 (mem_to_mem2 m) l (val_to_val2 v)
      | Assign r x v => Assign2 (reg_to_reg2 r) x (val_to_val2 v) 
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
      | Update2 m l v => Update (project_mem m is_left) l (project_value v is_left)
      | Assign2 r x v => Assign (project_reg r is_left) x (project_value v is_left)
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
     | VPair (Vnat n2) (Vnat n3), VSingle (Vnat n1) => VPair (Vnat (op n2 n1)) (Vnat (op n3 n1))
     | _, _ => v1
     end.
   
   Definition val2_add (v1 v2 :val2) := apply_op (fun x y => x + y) v1 v2.

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
   | Estep2_add : forall md d ecfg e1 e2 v1 v2,
       ecfg_exp2 ecfg = Eadd e1 e2 ->
       estep2 md d (ecfg_update_exp2 ecfg e1) v1 ->
       estep2 md d (ecfg_update_exp2 ecfg e2) v2 ->
       contains_nat v1 /\ contains_nat v2 ->
       estep2 md d ecfg (val2_add v1 v2)
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
      cstep2 md d ccfg (r', ccfg_mem2 ccfg) [Assign2 (ccfg_reg2 ccfg) x v]
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
      cstep2 md d ccfg (ccfg_reg2 ccfg, m') [Update2 (ccfg_mem2 ccfg) l v]
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
      merge_reg r1 r2 = rmerge ->
      merge_mem m1 m2 = mmerge ->
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
      merge_reg r1 r2 = rmerge ->
      merge_mem m1 m2 = mmerge ->
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
      merge_reg r1 r2 = rmerge ->
      merge_mem m1 m2 = mmerge ->
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

(*******************************************************************************
*
* SECURITY DEFINITIONS
*
*******************************************************************************)

Section Security_Defn.
  Parameter minit2_left : mem.
  Parameter minit2_right : mem.
  Axiom wf_minit2_left : forall d, meminit_wf minit2_left d.
  Axiom wf_minit2_right : forall d, meminit_wf minit2_right d.
  Definition minit2 := merge_mem minit2_left minit2_right.
  
  Definition esc_hatch : Type := exp.
  Definition is_escape_hatch e : Prop := exp_novars e /\ exp_locs_immutable e.

  Definition tobs_sec_level (sl: sec_level) : trace -> trace :=
    filter (fun event => match event with
                         | Out sl' v => sec_level_le_compute sl' sl
                         | AEnc c c' enc_equiv => true
                         | ANonEnc c => true
                         | _ => false                           
                         end).

  Definition corresponds (G: context) : Prop :=
    (forall l p bt rt, g0 l = p -> Loc_Contxt l = Some (Typ bt p, rt))
    /\ (forall x, G x = Some (Typ Tnat (L))).

  Definition mem_sl_ind (sl: sec_level) :=
    forall l : location,
      sec_level_le (g0 l) sl <-> (project_mem minit2 true) l = (project_mem minit2 false) l.

  (* capture the notion that the memory does not change at the locations by saying *)
  (* that any memory---implicitly derived from minit2---has the same value at the *)
  (* locations of e *)
  Definition mem_esc_hatch_ind :=
    forall e, is_escape_hatch e -> (forall (m: mem2) (l: location),
                                       loc_in_exp e l ->
                                       exists v, minit2 l = VSingle v /\ minit2 l = m l).
  
  Definition secure_prog (sl: sec_level) (d: loc_mode) (c: com) (G: context) : Prop :=
    forall m0 mknown r' m' t tobs,
      merge_mem m0 mknown = minit2 ->
      cstep2 Normal d (c, reg_init2, minit2) (r', m') t ->
      tobs = project_trace t true ->
      mem_sl_ind sl ->
      mem_esc_hatch_ind ->
      tobs_sec_level sl tobs = tobs_sec_level sl (project_trace t false).

    Definition cterm2_ok (md: mode) (G: context) (d: loc_mode) (r: reg2) (m: mem2)
      : Prop :=
      (forall x v1 v2 bt p,
          (r x = VPair v1 v2 /\ G x = Some (Typ bt p)) -> protected p /\ md <> Normal) 
      /\ (forall l v1 v2 bt p rt,
          (m l = VPair v1 v2 /\ Loc_Contxt l = Some (Typ bt p, rt))
          -> protected p /\ d l <> Normal)
      /\ mem_sl_ind L
      /\ mem_esc_hatch_ind.

  Definition cconfig2_ok (pc: sec_level) (md: mode) (G: context) (d: loc_mode)
             (c: com) (r: reg2) (m: mem2) (G': context)
    : Prop :=
    com_type pc md G d c G'
    /\ (forall x v1 v2 bt p,
           (r x = VPair v1 v2
            /\ G x = Some (Typ bt p))
           -> protected p /\ md <> Normal)
    /\ (forall l v1 v2 bt p rt,
           ((m l) = VPair v1 v2 /\ Loc_Contxt (l) = Some (Typ bt p, rt))    
           -> protected p /\ d l <> Normal)
    /\ mem_sl_ind L
    /\ mem_esc_hatch_ind.
  
End Security_Defn.

Section Axioms.
   Definition meminit2_wf (m: mem2) d := forall l,
    match m l with
    | VSingle (Vlambda md c) => forall Gm p Gp q rt,
                               Loc_Contxt l = Some (Typ (Tlambda Gm p md Gp) q, rt) ->
                               com_type p md Gm d c Gp
    | VPair (Vlambda md1 c1) (Vlambda md2 c2) =>
      (forall Gm p Gp q rt,
          Loc_Contxt l = Some (Typ (Tlambda Gm p md1 Gp) q, rt) ->
          com_type p md1 Gm d c1 Gp) /\
      (forall Gm p Gp q rt,
          Loc_Contxt l = Some (Typ (Tlambda Gm p md2 Gp) q, rt) ->
          com_type p md2 Gm d c2 Gp)
    | VSingle (Vnat n) => True
    | VPair (Vnat n1) (Vnat n2) => True
    | _ => False
    end.

   Lemma wf_minit2 : forall d: loc_mode, meminit2_wf minit2 d.
   Proof.
     intros.
     unfold minit2.
     unfold meminit2_wf; intros.
     remember (minit2_left l) as vl; remember (minit2_right l) as vr.
     pose (wf_minit2_left d l) as wfl; rewrite <- Heqvl in wfl.
     pose (wf_minit2_right d l) as wfr; rewrite <- Heqvr in wfr.
     unfold merge_mem.
     rewrite <- Heqvl, <- Heqvr.
     destruct (val_decidable vl vr); destruct vl, vr; auto.
     (* XXX the cases left are where you have a pair of lambda and nat...
        need to allow that in the initial memory or require that minit2_left
        and minit2_right have the same type at each location *)
   Admitted.
     
   Axiom Initial_State2: forall d r' m',
       exists c md tr, cstep2 md d (c, reg_init2, minit2) (r', m') tr.

   (* These follow from the axiom above and the assumption made in ImpE *)
   Axiom No_Loc_Mem : forall (m: mem2) l,
       (forall l', m l <> VSingle (Vloc l')) /\
       (forall l' l'', m l <> VPair (Vloc l') (Vloc l'')).
   
   Axiom No_Pair_Loc_Reg : forall (r: reg2) l,
       (forall l' l'', r l <> VPair (Vloc l') (Vloc l'')).
   
   Axiom pair_distinct : forall v v1 v2,
       v = VPair v1 v2 <-> v1 <> v2.
   
   Axiom pair_wf : forall v v1 v2,
       v = VPair v1 v2 <->
       (exists n1 n2, v1 = Vnat n1 /\ v2 = Vnat n2) \/
       (exists md1 md2 c1 c2, v1 = Vlambda md1 c1 /\ v2 = Vlambda md2 c2).
End Axioms.