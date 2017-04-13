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
  Definition ecfg_update_exp2 (ecfg: econfig2) (e: exp) : econfig2 :=
    match ecfg with (_, r, m, k) => (e, r, m, k) end.
  Definition esemantics2 : Type := mode -> loc_mode -> econfig2 -> val2 -> Prop.

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
  | Estep2_plus : forall md d ecfg e1 e2 n1 n2,
      ecfg_exp2 ecfg = Eplus e1 e2 ->
      estep2 md d (ecfg_update_exp2 ecfg e1) (VSingle (Vnat n1)) ->
      estep2 md d (ecfg_update_exp2 ecfg e2) (VSingle (Vnat n2)) ->
      estep2 md d ecfg (VSingle (Vnat (n1 + n2)))
  | Estep2_mult : forall md d ecfg e1 e2 n1 n2,
      ecfg_exp2 ecfg = Emult e1 e2 ->
      estep2 md d (ecfg_update_exp2 ecfg e1) (VSingle (Vnat n1)) ->
      estep2 md d (ecfg_update_exp2 ecfg e2) (VSingle (Vnat n2)) ->
      estep2 md d ecfg (VSingle (Vnat (n1 * n2)))
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
      \/ (v <> VSingle (Vnat 0) /\ res = VSingle (Vnat 0)) ->
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

  Inductive cstep2 : csemantics2 := 
  | Cstep2_skip : forall md d ccfg,
      ccfg_com2 ccfg = Cskip ->
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
  | Cstep2_if : forall md d ccfg e c1 c2 n r' m' k' tr,
      ccfg_com2 ccfg = Cif e c1 c2 ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (VSingle (Vnat n)) ->
      ~(n = 0) ->
      cstep2 md d (ccfg_update_com2 c1 ccfg) (r', m', k') tr ->
      cstep2 md d ccfg (r', m', k') tr
  | Cstep2_else : forall md d ccfg e c1 c2 n r' m' k' tr,
      ccfg_com2 ccfg = Cif e c1 c2 ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (VSingle (Vnat n)) ->
      (n = 0) ->
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
  | Cstep_while_t : forall md d ccfg e c v r m k tr r' m' k' tr',
      ccfg_com2 ccfg = Cwhile e c ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) v ->
      ~(v = (VSingle (Vnat 0))) ->
      cstep2 md d (ccfg_update_com2 c ccfg) (r, m, k) tr ->
      cstep2 md d (ccfg_update_com2 (Cwhile e c) ccfg) (r', m', k') tr' ->
      cstep2 md d ccfg (r', m', k') (tr++tr')
  | Cstep_while_f : forall md d ccfg e c,
      ccfg_com2 ccfg = Cwhile e c ->
      estep2 md d (ccfg_to_ecfg2 e ccfg) (VSingle (Vnat 0)) ->
      mode_alive2 md (ccfg_kill2 ccfg) ->
      cstep2 md d ccfg (ccfg_reg2 ccfg, ccfg_mem2 ccfg, ccfg_kill2 ccfg) [].
  (* XXX add in while-div and call-div *)
  (* XXX: add in set add for pairs
  | Cstep_kill : forall md d ccfg enc,
      md = Normal ->
      ccfg_com2 ccfg = Ckill enc ->
      mode_alive2 (Encl enc) (ccfg_kill2 ccfg) ->
      cstep2 md d ccfg (ccfg_reg2 ccfg, ccfg_mem2 ccfg, set_add Nat.eq_dec enc (ccfg_kill2 ccfg)) []*)
  Hint Constructors cstep2.
End Semantics.

(*******************************************************************************
*
* TYPING
*
*******************************************************************************)

Section Typing.

  (* XXX: I *think* that we probably don't need to redefine all types. 
we can use the same typing rules, but need to add the well-formed configs for 
commands and values (in section Security below). There is some unfortunate business
with kill sets inside functions needing to be kill2... will need to think
about this a bit more *)
  (* FIXME: don't have subsumption rule *)
  Inductive exp_type2 : mode -> context -> loc_mode -> exp -> type -> Prop :=
  | ETnat2 : forall md g d n,
      exp_type2 md g d (Enat n) (Typ Tnat (LevelP L))
  | ETvar2 : forall md g d x t,
      var_context g x = Some t -> exp_type2 md g d (Evar x) t
  | ETcnd2 : forall md g d a md',
      let l := Cnd a in
      d l = md' ->
      exp_type2 md g d (Eloc l) (Typ (Tcond md') (LevelP L))
  | ETloc2 : forall md g d a md' t rt,
      let l := Not_cnd a in
      d l = md' ->
      loc_context g l = Some (t, rt) ->
      exp_type2 md g d (Eloc l) (Typ (Tref t md' rt) (LevelP L))
  | ETderef2 : forall md g d e md' s p rt q,
      exp_type md g d e (Typ (Tref (Typ s p) md' rt) q) ->
      md' = Normal \/ md' = md ->
      exp_type2 md g d (Ederef e) (Typ s (policy_join p q))
  | ETunset2 : forall md g d cnd md',
      md' = d (Cnd cnd) ->
      md' = Normal \/ md' = md ->
      exp_type2 md g d (Eisunset cnd) (Typ Tnat (LevelP L))
  (* kill2 problem here too *)
                (*
  | ETlambda2 : forall md g d c p k u g' k',
      com_type2 p md g k u d c g' k' ->
      exp_type2 md g d (Elambda md c) (Typ (Tlambda g k u p md g' k') (LevelP L)) *)
  | ETplus2 : forall md g d e1 e2 p q,
      exp_type2 md g d e1 (Typ Tnat p) ->
      exp_type2 md g d e2 (Typ Tnat q) ->
      exp_type2 md g d (Eplus e1 e2) (Typ Tnat (policy_join p q))
  | ETmult2 : forall md g d e1 e2 p q,
      exp_type2 md g d e1 (Typ Tnat p) ->
      exp_type2 md g d e2 (Typ Tnat q) ->
      exp_type2 md g d (Emult e1 e2) (Typ Tnat (policy_join p q))

  with com_type2 : sec_policy -> mode -> context -> kill2 ->
                  set condition -> loc_mode -> com ->
                  context -> kill2 -> Prop :=
  | CTskip2 : forall pc md g d k u,
      mode_alive2 md k ->
      com_type2 pc md g k u d Cskip g k
  | CTkillsingle2 : forall i g d k u,
      mode_alive2 (Encl i) (KSingle k) ->
      com_type2 (LevelP L) Normal g (KSingle k) u d (Ckill i) g (KSingle (set_add Nat.eq_dec i k))
  | CTkillpair2 : forall i g d k1 k2 u,
      mode_alive2 (Encl i) (KPair k1 k2) ->
      com_type2 (LevelP L) Normal g (KPair k1 k2) u d (Ckill i) g
                (KPair (set_add Nat.eq_dec i k1) (set_add Nat.eq_dec i k2))
  | CTassign2 : forall pc md g k u d x e s p q vc lc vc',
      exp_type md g d e (Typ s p) ->
      q = policy_join p pc ->
      q <> LevelP T ->
      policy_le q (LevelP L) \/ md <> Normal ->
      mode_alive2 md k ->
      g = Cntxt vc lc ->
      vc' = (fun y => if y =? x then Some (Typ s q) else vc y) ->
      com_type2 pc md g k u d (Cassign x e) (Cntxt vc' lc) k
  | CTdeclassify2 : forall md g k u d x e s p vc lc vc',
      exp_type2 md g d e (Typ s p) ->
      p <> LevelP T ->
      mode_alive2 md k ->
      exp_novars e ->
      all_loc_immutable e g ->
      vc' = (fun y => if y =? x then Some (Typ s (LevelP L)) else vc y) ->
      com_type2 (LevelP L) md g k u d (Cdeclassify x e) (Cntxt vc' lc) k
  | CToutput2 : forall pc md g k u d e l s p,
      exp_type md g d e (Typ s p) ->
      mode_alive2 md k ->
      p <> LevelP T ->
      sec_level_le (sec_level_join (cur p u) (cur pc u)) l ->
      com_type2 pc md g k u d (Coutput e l) g k
  | CTupdate2 : forall pc md g k u d e1 e2 s p md' q p',
      exp_type md g d e1 (Typ (Tref (Typ s p) md' Mut) q) ->
      exp_type md g d e2 (Typ s p') ->
      policy_le (policy_join (policy_join p' q) pc) p ->
      md' = Normal \/ md' = md ->
      mode_alive2 md k ->
      p <> LevelP T ->
      p' <> LevelP T ->
      q <> LevelP T ->
      com_type2 pc md g k u d (Cupdate e1 e2) g k
  | Tset2 : forall md g k u d cnd md',
      md' = d (Cnd cnd) ->
      ~set_In cnd u ->
      md' = Normal \/ md' = md ->
      mode_alive2 md k ->
      com_type2 (LevelP L) md g k u d (Cset cnd) g k
  | Tifunset2 : forall pc md g k u d cnd c1 c2 g' k',
      exp_type md g d (Eisunset cnd) (Typ Tnat (LevelP L)) ->
      com_type2 pc md g k (set_add Nat.eq_dec cnd u) d c1 g' k' ->
      com_type2 pc md g k u d c2 g' k' ->
      com_type2 pc md g k u d (Cif (Eisunset cnd) c1 c2) g' k'
  | Tifelse2 : forall pc md g k u d e c1 c2 pc' p g' k',
      ~(exists cnd, e = Eisunset cnd) ->
      com_type2 pc' md g k u d c1 g' k' ->
      com_type2 pc' md g k u d c2 g' k' ->
      exp_type2 md g d e (Typ Tnat p) ->
      policy_le (policy_join pc p) pc' ->
      policy_le p (LevelP L) \/ md <> Normal ->
      p <> LevelP T ->
      com_type2 pc md g k u d (Cif e c1 c2) g' k'
  | Tenclave2 : forall pc g k u d c i c' g' k',
      c = Cenclave i c' ->
      com_type2 pc (Encl i) g k nil d c' g' k' ->
      is_var_low_context g' ->
      com_type2 pc Normal g k u d c g' k'
  | Twhile2 : forall pc md g k u d c e p pc',
      exp_type2 md g d e (Typ Tnat p) ->
      com_type2 pc' md g k u d c g k ->
      policy_le (policy_join pc p) pc' ->
      policy_le p (LevelP L) \/ md <> Normal ->
      p <> LevelP T ->
      com_type2 pc md g k u d (Cwhile e c) g k
  | Tseq2 : forall pc md g k u d c rest g' k' gn kn,
      com_type2 pc md g k u d c g' k' ->
      com_type2 pc md g' k' u d (Cseq rest) gn kn ->
      com_type2 pc md g k u d (Cseq (c :: rest)) gn kn
  | Tseqnil2 : forall pc md g k u d,
      com_type2 pc md g k u d (Cseq []) g k.
  (* XXX km and kp need to be kill2, not set enclave... *)
                (*
  | Tcall2 : forall pc md G u d e Gm km Gp kp Gout q p,
      exp_type2 md G d e (Typ (Tlambda Gm km u p md Gp kp) q) ->
      policy_le (policy_join pc q) p ->
      q <> LevelP T ->
      u = nil \/ md <> Normal ->
      forall_dom Gm
                 (fun x t => exists t', var_in_dom G x t' /\ type_le t' t)
                 (fun l t rt => exists t',
                      loc_in_dom G l t' rt /\ type_le t' t) ->
      forall_dom Gp
                 (fun x t => exists t', var_in_dom Gout x t' /\ type_le t' t)
                 (fun l t rt => exists t',
                      loc_in_dom Gout l t' rt /\ type_le t' t) ->
      forall_dom G
                 (fun x t =>
                    (forall t', ~var_in_dom Gp x t') ->
                    var_in_dom Gout x t)
                 (fun l t rt =>
                    (forall t' rt', ~loc_in_dom Gp l t' rt') ->
                    loc_in_dom Gout l t rt) ->
      com_type2 pc md G km u d (Ccall e) Gout kp.*)
  
End Typing.


(*******************************************************************************
*
* Security
*
*******************************************************************************)
Section Security.
  Inductive protected : sec_policy -> set condition -> Prop :=
  | level_high: forall S, protected (LevelP H) S
  | level_top: forall S, protected (LevelP T) S
  | erase_high: forall cnd S sl pf,
      protected (ErasureP H cnd sl pf) S
  | erase_low: forall cnd S sl pf,
      set_In cnd S -> protected (ErasureP L cnd sl pf) S.

  Definition val2config_wt (G: context) (S: set condition) (H: set esc_hatch) (m0: mem2)
             (r: reg2) (m: mem2) (K: kill2) : Prop :=
    forall md d,
      (forall x v1 v2 bt p,
          (r x = VPair v1 v2 /\ (var_context G) x = Some (Typ bt p)) -> protected p S) ->
      (forall l v1 v2 bt p rt,
          (m (Not_cnd l) = VPair v1 v2 /\ (loc_context G) (Not_cnd l) = Some (Typ bt p, rt))
          -> protected p S) ->
      (forall e v, set_In e H ->
                 (estep2 md d (e, reg_init2, m0, K) v ->
                  estep2 md d (e, r, m, K) v)) ->
      project_kill K true = project_kill K false ->
      True.

  Definition cconfig2_wt (pc: sec_policy) (md: mode) (G: context) (U: set condition)
             (d: loc_mode) (S: set condition) (H: set esc_hatch) (m0: mem2)
             (ccfg2: cconfig2) (G': context) (K': kill2) : Prop :=
      (forall i, set_In i U -> (ccfg_mem2 ccfg2) (Cnd i) = VSingle (Vnat 0)) ->
      com_type2 pc md G (ccfg_kill2 ccfg2) U d (ccfg_com2 ccfg2) G' K' ->
      (forall x v1 v2 bt p,
          ((ccfg_reg2 ccfg2) x = VPair v1 v2
          /\ (var_context G) x = Some (Typ bt p)) -> protected p S) ->
      (forall l v1 v2 bt p rt,
          ((ccfg_mem2 ccfg2) (Not_cnd l) = VPair v1 v2
          /\ (loc_context G) (Not_cnd l) = Some (Typ bt p, rt)) -> protected p S) ->
      (forall e v, set_In e H ->
                 (estep2 md d  (e, reg_init2, m0, ccfg_kill2 ccfg2) v ->
                  estep2 md d (e, ccfg_reg2 ccfg2, ccfg_mem2 ccfg2, ccfg_kill2 ccfg2) v)) ->
      project_kill (ccfg_kill2 ccfg2) true = project_kill (ccfg_kill2 ccfg2) false ->
      True.
              
(*      
  Definition overlap (tr tobs: trace) :=
  | tobs is entirely contained in tr => tobs
  | tobs is after tr => empty
  | overlap with beginning of tobs => beginning of tobs
                                                    
  Lemma eq_overlap_tobs (m1 m2: mem) (tobs: trace) :
    forall md d c k r' m' k' tr1 tr2,
    cstep md d (c, reg_init, m1, k) (r', m', k') tr1 ->
    cstep md d (c, reg_init, m2, k) (r', m', k') tr2 ->
    tobs_sec_level L (overlap tr1 tobs) = tobs_sec_level L (overlap tr2 tobs).
  *)    
End Security.


(*******************************************************************************
*
* ADEQUACY
*
*******************************************************************************)
Section Adequacy.

  Definition not_pair_val (v : val2) : Prop :=
    match v with
    | VPair _ _ => False
    | _ => True
    end.
  (* XXX This doesn't make sense any more? because vpairs are 
constructed only with vals and not val2s now*)
  (*
  Definition no_nest_val (v : val2) : Prop :=
    match v with
    | VPair v1 v2 => (not_pair_val v1) /\ (not_pair_val v2)
    | _ => True
    end.

  (* XXX same with this? *)
  Definition kill_wf (k : kill2) : Prop :=
    match k with
    | KPair (KSingle _) (KSingle _) => True
    | KSingle _ => True
    | _ => False
    end.


  Definition reg_wf (r : reg2) : Prop :=
    forall x, no_nest_val (r x).

  Definition mem_wf (m : mem2) : Prop :=
    forall x, no_nest_val (m x).
*)
  (* XXX: thought I needed this for exp_output_wf, didn't use it. Might still be useful...? *)
  Lemma estep2_deterministic : forall md d e r m k v1 v2,
    estep2 md d (e, r, m, k) v1 ->
    estep2 md d (e, r, m, k) v2 ->
    v1 = v2.
  Proof.
    intros; revert H0; revert v2.
    induction H; intros; destruct ecfg as [[[e' r'] m'] k']; simpl in *; try rewrite H in H0.
    1-3: inversion H0; subst; try discriminate; simpl in H1; congruence.
    inversion H1; subst; try discriminate; simpl in *; congruence.
    1-2: rewrite H in H2; inversion H2; try discriminate; simpl in *;
      assert (e1 = e0) by congruence; assert (e2 = e3) by congruence;
        subst; apply IHestep2_1 in H4; apply IHestep2_2 in H5;
          assert (n1 = n0) by congruence; assert (n2 = n3) by congruence; now subst.
    - rewrite H in H3; inversion H3; subst; try discriminate; simpl in *.
      assert (e0 = e1) by congruence.
      assert (r0 = r1) by congruence.
      assert (m0 = m1) by congruence.
      assert (k0 = k1) by congruence.
      subst. apply IHestep2 in H5. assert (l = l0) by congruence; now subst.
    -  rewrite H in H2; inversion H2; subst; try discriminate; simpl in *.
       assert (cnd = cnd0) by congruence; subst.
       apply IHestep2 in H4.
       destruct H1; destruct H5; destruct_conjs; subst; auto; congruence.
  Qed.      

  (*
  Lemma impe2_exp_output_wf : forall md d ecfg v,
      estep2 md d ecfg v ->
      mem_wf (ecfg_mem2 ecfg) ->
      reg_wf (ecfg_reg2 ecfg) ->
      no_nest_val v.
  Proof.
    intros.
    induction H; simpl; auto.
    - unfold reg_wf in H1; now rewrite <- H2.
    - rewrite H in H0; unfold mem_wf in H0; simpl in *; now rewrite <- H3.
    - destruct H3; destruct_conjs; subst; now simpl.
  Qed.

  Lemma impe2_output_wf : forall md d ccfg r' m' K' t,
          reg_wf (ccfg_reg2 ccfg) ->
          mem_wf (ccfg_mem2 ccfg) ->
          cstep2 md d ccfg (r', m', K') t ->
          reg_wf r' /\ mem_wf m' /\ kill_wf K'.
  Proof.
  Admitted.
*)
  
  Lemma impe2_sound : forall md d c r m K r' m' K' t,
    cstep2 md d (c, r, m, K) (r', m', K') t ->
    (cstep md d (c, project_reg r true, project_mem m true, project_kill K true)
           (project_reg r' true, project_mem m' true, project_kill K' true)
           (project_trace t true)) /\
    (cstep md d (c, project_reg r false, project_mem m false, project_kill K false)
           (project_reg r' false, project_mem m' true, project_kill K' false)
           (project_trace t false)).
  Proof.
    intros. split.
    remember (c, r, m, K) as ccfg.
    remember (r', m', K') as cterm.
    induction H.
    rewrite Heqccfg in H, Heqcterm; simpl in *; inversion Heqcterm; subst.
    apply Cstep_skip.
    rewrite Heqccfg in H, Heqcterm; simpl in *; inversion Heqcterm; subst.
    apply Cstep_assign.
  Admitted.
  
  
End Adequacy.