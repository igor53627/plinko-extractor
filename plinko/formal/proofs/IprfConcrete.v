(** IprfConcrete.v - Concrete instantiation of iPRF at domain n = N

    This module instantiates the abstract iPRF at the concrete domain
    size N (2^64) using SwapOrNot as the underlying PRP.

    The abstract iPRF uses parameters:
      - prp_forward : Z -> Z -> Z
      - prp_inverse : Z -> Z -> Z

    When instantiated at n = N, these become:
      - prp_forward N x := forward_spec x
      - prp_inverse N x := inverse_spec x
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Bool.

Require Import Plinko.Specs.CommonTypes.
Require Import Plinko.Specs.BinomialSpec.
Require Import Plinko.Specs.SwapOrNotSpec.
Require Import Plinko.Specs.IprfSpec.
Require Import Plinko.Proofs.SwapOrNotProofs.
Require Import Plinko.Proofs.IprfProofs.
Require Import Plinko.Proofs.PrpBridge.

Import ListNotations.
Open Scope Z_scope.

(** ============================================================================
    Section 1: Concrete iPRF Definitions at n = N
    ============================================================================ *)

Section IprfConcreteN.

Definition iprf_forward_N (x m : Z) : Z := iprf_forward_spec x N m.

Definition iprf_inverse_N (y m : Z) : list Z := iprf_inverse_spec y N m.

(** ============================================================================
    Section 2: Specialized iPRF Properties for n = N
    ============================================================================ *)

Theorem iprf_forward_N_in_range : forall x m,
  0 <= x < N -> 0 < m -> m <= N ->
  0 <= iprf_forward_N x m < m.
Proof.
  intros x m Hx Hm_pos Hm_le_N.
  unfold iprf_forward_N.
  apply iprf_forward_in_range; assumption.
Qed.

Theorem iprf_inverse_N_contains_preimage : forall x m,
  0 <= x < N -> 0 < m -> m <= N ->
  In x (iprf_inverse_N (iprf_forward_N x m) m).
Proof.
  intros x m Hx Hm_pos Hm_le_N.
  unfold iprf_inverse_N, iprf_forward_N.
  apply iprf_inverse_contains_preimage; auto.
Qed.

Theorem iprf_inverse_N_elements_in_domain : forall y m x,
  0 <= y < m -> 0 < m -> m <= N ->
  In x (iprf_inverse_N y m) -> 0 <= x < N.
Proof.
  intros y m x Hy Hm_pos Hm_le_N Hin.
  unfold iprf_inverse_N in Hin.
  apply (iprf_inverse_elements_in_domain y N m x Hy Hm_pos Hm_le_N Hin).
Qed.

Theorem iprf_inverse_N_consistent : forall y m x,
  0 <= y < m -> 0 < m -> m <= N ->
  In x (iprf_inverse_N y m) -> iprf_forward_N x m = y.
Proof.
  intros y m x Hy Hm_pos Hm_le_N Hin.
  unfold iprf_inverse_N, iprf_forward_N in *.
  apply (iprf_inverse_elements_map_to_y y N m x Hy Hm_pos Hm_le_N Hin).
Qed.

Theorem iprf_inverse_N_partitions_domain : forall m x,
  0 < m -> m <= N ->
  0 <= x < N ->
  exists! y, 0 <= y < m /\ In x (iprf_inverse_N y m).
Proof.
  intros m x Hm_pos Hm_le_N Hx.
  unfold iprf_inverse_N.
  apply (iprf_inverse_partitions_domain N m Hm_pos Hm_le_N x Hx).
Qed.

Theorem iprf_inverse_N_disjoint : forall y1 y2 m x,
  0 <= y1 < m -> 0 <= y2 < m -> y1 <> y2 ->
  0 < m -> m <= N ->
  In x (iprf_inverse_N y1 m) -> ~ In x (iprf_inverse_N y2 m).
Proof.
  intros y1 y2 m x Hy1 Hy2 Hneq Hm_pos Hm_le_N Hin1 Hin2.
  unfold iprf_inverse_N in *.
  assert (Hx_range : 0 <= x < N).
  { apply (iprf_inverse_elements_in_domain y1 N m x Hy1 Hm_pos Hm_le_N Hin1). }
  assert (H1 : iprf_forward_spec x N m = y1).
  { apply (iprf_inverse_elements_map_to_y y1 N m x Hy1 Hm_pos Hm_le_N Hin1). }
  assert (H2 : iprf_forward_spec x N m = y2).
  { apply (iprf_inverse_elements_map_to_y y2 N m x Hy2 Hm_pos Hm_le_N Hin2). }
  congruence.
Qed.

(** ============================================================================
    Section 3: Proptest-style Combined Properties for n = N
    ============================================================================ *)

Theorem iprf_N_inverse_preimage_consistent : forall x m,
  0 <= x < N -> 0 < m -> m <= N ->
  let y := iprf_forward_N x m in
  0 <= y < m /\
  In x (iprf_inverse_N y m) /\
  (forall x2, In x2 (iprf_inverse_N y m) ->
    0 <= x2 < N /\ iprf_forward_N x2 m = y).
Proof.
  intros x m Hx Hm_pos Hm_le_N.
  set (y := iprf_forward_N x m).
  split.
  - apply iprf_forward_N_in_range; assumption.
  - split.
    + apply iprf_inverse_N_contains_preimage; assumption.
    + intros x2 Hx2_in.
      assert (Hy_range : 0 <= y < m).
      { apply iprf_forward_N_in_range; assumption. }
      split.
      * apply (iprf_inverse_N_elements_in_domain y m x2 Hy_range Hm_pos Hm_le_N Hx2_in).
      * apply (iprf_inverse_N_consistent y m x2 Hy_range Hm_pos Hm_le_N Hx2_in).
Qed.

End IprfConcreteN.

Close Scope Z_scope.
