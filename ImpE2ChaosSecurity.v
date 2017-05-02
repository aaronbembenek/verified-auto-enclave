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
Require Import ImpE2.
Require Import ImpE2Helpers.
Require Import ImpE2SecurityHelpers.

Parameter Loc_Contxt_Nchaos : location -> option (type * ImpE.ref_type).
Parameter d_nchaos : loc_mode.
Axiom d_nchaos_low : forall l, d_nchaos l = Normal ->
                               exists bt rt, Loc_Contxt_Nchaos l = Some (Typ bt L, rt).

(* All memory locations not in enclave at security level low 
* (attacker can read/write arbitrary memory locations not in enclave) 
* Then we prove that there are no pairs in non-enclave memory locations.
* This means that since an attacker cannot mess w/enclave code,
* any output of the pairs must be well-typed, i.e. at a high level.
*)

Lemma no_pairs_Normal : forall pc md G c r m G',
  cconfig2_ok pc md G d_nchaos c r m G' ->
  (forall x v1 v2, r x = VPair v1 v2 -> md <> Normal) /\
  (forall l v1 v2, m l = VPair v1 v2 -> md <> Normal).
Proof.
Admitted.

