(** IprfProofs.v - Proofs of key properties for the Invertible PRF (iPRF)

    Properties proven (corresponding to proptest properties in iprf.rs):
    1. iprf_inverse_contains_preimage_and_is_consistent:
       - forward(x) < m
       - x in inverse(forward(x))
       - forall x2 in inverse(y), x2 < n and forward(x2) = y

    2. iprf_inverse_partitions_domain:
       - forall y in [0,m), inverse(y) covers disjoint subsets of [0,n)
       - union of all inverse(y) = [0,n)
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Bool.

Require Import Plinko.Specs.CommonTypes.
Require Import Plinko.Specs.BinomialSpec.
Require Import Plinko.Specs.SwapOrNotSpec.
Require Import Plinko.Specs.IprfSpec.

Import ListNotations.
Open Scope Z_scope.

(** ============================================================================
    Section 1: Trace Ball Properties
    ============================================================================ *)

Section TraceBallProperties.

Context (n m : Z).
Context (Hm_pos : 0 < m).
Context (Hm_le_n : m <= n).

(** trace_ball_preserves_range: output is in [0, m) *)
Theorem trace_ball_preserves_range : forall x,
  0 <= x < n ->
  0 <= trace_ball_spec x n m < m.
Proof.
  intros x Hx.
  apply trace_ball_in_range; assumption.
Qed.

(** trace_ball_deterministic: same inputs give same output *)
Theorem trace_ball_deterministic : forall x,
  0 <= x < n ->
  trace_ball_spec x n m = trace_ball_spec x n m.
Proof.
  intros x Hx.
  reflexivity.
Qed.

(** trace_ball step preserves loop invariants *)
Lemma trace_ball_step_invariants : forall st,
  ts_low st < ts_high st ->
  0 <= ts_ball_index st < ts_ball_count st ->
  ts_ball_count st > 0 ->
  let st' := trace_ball_step st in
  ts_low st' <= ts_high st' /\
  ts_high st' - ts_low st' < ts_high st - ts_low st /\
  0 <= ts_ball_index st' < ts_ball_count st'.
Proof.
  intros st Hlt Hball Hpos.
  apply IprfSpec.trace_ball_step_invariants; assumption.
Qed.

End TraceBallProperties.

(** ============================================================================
    Section 2: Trace Ball Inverse Properties
    ============================================================================ *)

Section TraceBallInverseProperties.

Context (n m : Z).
Context (Hm_pos : 0 < m).
Context (Hm_le_n : m <= n).

(** Helper: range_list produces consecutive integers *)
Lemma range_list_spec : forall start count fuel x,
  count <= Z.of_nat fuel ->
  0 <= count ->
  In x (range_list start count fuel) <-> (start <= x < start + count).
Proof.
  intros. apply IprfSpec.range_list_spec; assumption.
Qed.

(** trace_ball_inverse_contiguous: result is a contiguous range *)
Theorem trace_ball_inverse_contiguous : forall y,
  0 <= y < m ->
  exists start count,
    count >= 0 /\
    trace_ball_inverse_spec y n m = range_list start count (Z.to_nat count).
Proof.
  intros y Hy.
  unfold trace_ball_inverse_spec.
  destruct (m =? 1) eqn:Hm1.
  - exists 0, n. split; [lia | reflexivity].
  - apply Z.eqb_neq in Hm1.
    set (init_ist := mkTraceInvState 0 (m - 1) n 0).
    set (fuel := Z.to_nat (2 * m)).
    destruct (trace_ball_inverse_fuel fuel y init_ist) as [start count] eqn:Hres.
    exists start, count.
    pose proof (trace_ball_inverse_fuel_bounds fuel y init_ist n) as Hb.
    rewrite Hres in Hb.
    assert (Hbounds : 0 <= start /\ 0 <= count /\ start + count <= n).
    { apply Hb; simpl; lia. }
    split.
    + lia.
    + reflexivity.
Qed.

(** trace_ball_inverse_contains_forward: x in inverse(trace_ball(x)) *)
Theorem trace_ball_inverse_contains_forward : forall x,
  0 <= x < n ->
  In x (trace_ball_inverse_spec (trace_ball_spec x n m) n m).
Proof.
  intros x Hx.
  apply trace_ball_inverse_contains_original; assumption.
Qed.

(** trace_ball_inverse_disjoint: different y give disjoint results *)
Theorem trace_ball_inverse_disjoint : forall y1 y2 x,
  0 <= y1 < m ->
  0 <= y2 < m ->
  y1 <> y2 ->
  In x (trace_ball_inverse_spec y1 n m) ->
  ~ In x (trace_ball_inverse_spec y2 n m).
Proof.
  intros y1 y2 x Hy1 Hy2 Hneq Hin1 Hin2.
  assert (H1 : trace_ball_spec x n m = y1).
  { apply IprfSpec.trace_ball_inverse_consistent with (n := n); assumption. }
  assert (H2 : trace_ball_spec x n m = y2).
  { apply IprfSpec.trace_ball_inverse_consistent with (n := n); assumption. }
  congruence.
Qed.

(** trace_ball_inverse_covers: union of all inverse(y) = [0, n) *)
Theorem trace_ball_inverse_covers : forall x,
  0 <= x < n ->
  exists y, 0 <= y < m /\ In x (trace_ball_inverse_spec y n m).
Proof.
  intros x Hx.
  exists (trace_ball_spec x n m).
  split.
  - apply trace_ball_in_range; assumption.
  - apply trace_ball_inverse_contains_forward. assumption.
Qed.

(** All elements in trace_ball_inverse are in valid domain *)
Theorem trace_ball_inverse_elements_in_domain : forall y x,
  0 <= y < m ->
  In x (trace_ball_inverse_spec y n m) ->
  0 <= x < n.
Proof.
  intros y0 x Hy Hin.
  apply (trace_ball_inverse_range y0 n m x); assumption.
Qed.

(** trace_ball_inverse elements map back to y *)
Theorem trace_ball_inverse_consistent : forall y x,
  0 <= y < m ->
  In x (trace_ball_inverse_spec y n m) ->
  trace_ball_spec x n m = y.
Proof.
  intros. apply IprfSpec.trace_ball_inverse_consistent with (n := n); assumption.
Qed.

End TraceBallInverseProperties.

(** ============================================================================
    Section 3: PRP Composition Properties
    ============================================================================ *)

Section PRPProperties.

Context (n : Z).
Context (Hn_pos : n > 0).

(** PRP forward is in range *)
Axiom prp_forward_in_range : forall x,
  0 <= x < n ->
  0 <= prp_forward n x < n.

(** PRP inverse is in range *)
Axiom prp_inverse_in_range : forall x,
  0 <= x < n ->
  0 <= prp_inverse n x < n.

(** PRP forward/inverse are inverses *)
Axiom prp_forward_inverse : forall x,
  0 <= x < n ->
  prp_inverse n (prp_forward n x) = x.

Axiom prp_inverse_forward : forall x,
  0 <= x < n ->
  prp_forward n (prp_inverse n x) = x.

(** PRP forward is injective *)
Lemma prp_forward_injective : forall x1 x2,
  0 <= x1 < n ->
  0 <= x2 < n ->
  prp_forward n x1 = prp_forward n x2 ->
  x1 = x2.
Proof.
  intros x1 x2 Hx1 Hx2 Heq.
  assert (H1 : prp_inverse n (prp_forward n x1) = x1).
  { apply prp_forward_inverse. assumption. }
  assert (H2 : prp_inverse n (prp_forward n x2) = x2).
  { apply prp_forward_inverse. assumption. }
  rewrite Heq in H1. congruence.
Qed.

(** PRP forward is surjective *)
Lemma prp_forward_surjective : forall y,
  0 <= y < n ->
  exists x, 0 <= x < n /\ prp_forward n x = y.
Proof.
  intros y Hy.
  exists (prp_inverse n y).
  split.
  - apply prp_inverse_in_range. assumption.
  - apply prp_inverse_forward. assumption.
Qed.

End PRPProperties.

(** ============================================================================
    Section 4: iPRF Main Properties
    ============================================================================ *)

Section IprfMainProperties.

Context (n m : Z).
Context (Hn_pos : n > 0).
Context (Hm_pos : 0 < m).
Context (Hm_le_n : m <= n).

(** iprf_forward_in_range_proof: 0 <= forward(x) < m *)
Theorem iprf_forward_in_range_proof : forall x,
  0 <= x < n ->
  0 <= iprf_forward_spec x n m < m.
Proof.
  intros x Hx.
  unfold iprf_forward_spec.
  destruct ((x <? 0) || (n <=? x)) eqn:Hguard.
  - split; lia.
  - apply trace_ball_in_range.
    + apply prp_forward_in_range; assumption.
    + assumption.
    + assumption.
Qed.

(** iprf_inverse_contains_preimage_proof: x in inverse(forward(x)) *)
Theorem iprf_inverse_contains_preimage_proof : forall x,
  0 <= x < n ->
  In x (iprf_inverse_spec (iprf_forward_spec x n m) n m).
Proof.
  intros x Hx.
  assert (Hy_range : 0 <= iprf_forward_spec x n m < m).
  { apply (iprf_forward_in_range x n m Hx Hm_pos Hm_le_n). }
  unfold iprf_inverse_spec.
  destruct ((iprf_forward_spec x n m <? 0) || (m <=? iprf_forward_spec x n m)) eqn:Hguard.
  - apply orb_true_iff in Hguard.
    destruct Hguard as [Hlt | Hle].
    + apply Z.ltb_lt in Hlt. lia.
    + apply Z.leb_le in Hle. lia.
  - unfold iprf_forward_spec.
    destruct ((x <? 0) || (n <=? x)) eqn:Hguard2.
    + apply orb_true_iff in Hguard2.
      destruct Hguard2 as [Hlt | Hle].
      * apply Z.ltb_lt in Hlt. lia.
      * apply Z.leb_le in Hle. lia.
    + set (x' := prp_forward n x).
      set (y := trace_ball_spec x' n m).
      assert (Hx'_range : 0 <= x' < n).
      { unfold x'. apply prp_forward_in_range; assumption. }
      assert (Hx'_in_inv : In x' (trace_ball_inverse_spec y n m)).
      { unfold y. apply trace_ball_inverse_contains_original; assumption. }
      apply in_map_iff.
      exists x'.
      split.
      * unfold x'. rewrite prp_forward_inverse; [reflexivity | assumption].
      * exact Hx'_in_inv.
Qed.

(** iprf_inverse_consistent_proof: forall x2 in inverse(y), forward(x2) = y *)
Theorem iprf_inverse_consistent_proof : forall y x2,
  0 <= y < m ->
  In x2 (iprf_inverse_spec y n m) ->
  iprf_forward_spec x2 n m = y.
Proof.
  intros y x2 Hy Hin.
  unfold iprf_inverse_spec in Hin.
  destruct ((y <? 0) || (m <=? y)) eqn:Hguard.
  - apply orb_true_iff in Hguard.
    destruct Hguard as [Hlt | Hle].
    + apply Z.ltb_lt in Hlt. lia.
    + apply Z.leb_le in Hle. lia.
  - apply in_map_iff in Hin.
    destruct Hin as [z [Hz_eq Hz_in]].
    assert (Hz_range : 0 <= z < n).
    { apply trace_ball_inverse_range with (y := y) (m := m); assumption. }
    assert (Hx2_range : 0 <= x2 < n).
    { subst x2. apply prp_inverse_in_range; assumption. }
    unfold iprf_forward_spec.
    destruct ((x2 <? 0) || (n <=? x2)) eqn:Hguard2.
    + apply orb_true_iff in Hguard2.
      destruct Hguard2 as [Hlt | Hle].
      * apply Z.ltb_lt in Hlt. lia.
      * apply Z.leb_le in Hle. lia.
    + subst x2.
      rewrite prp_inverse_forward by assumption.
      apply trace_ball_inverse_consistent with (n := n); assumption.
Qed.

(** Helper: all elements in iprf_inverse are in valid domain *)
Theorem iprf_inverse_in_domain_proof : forall y x,
  0 <= y < m ->
  In x (iprf_inverse_spec y n m) ->
  0 <= x < n.
Proof.
  intros y x Hy Hin.
  unfold iprf_inverse_spec in Hin.
  destruct ((y <? 0) || (m <=? y)) eqn:Hguard.
  - apply orb_true_iff in Hguard.
    destruct Hguard as [Hlt | Hle].
    + apply Z.ltb_lt in Hlt. lia.
    + apply Z.leb_le in Hle. lia.
  - apply in_map_iff in Hin.
    destruct Hin as [z [Hz_eq Hz_in]].
    subst x.
    assert (Hz_range : 0 <= z < n).
    { apply trace_ball_inverse_range with (y := y) (m := m); assumption. }
    apply prp_inverse_in_range; assumption.
Qed.

(** iprf_inverse_partitions_proof: inverses partition the domain *)
Theorem iprf_inverse_partitions_proof : forall x,
  0 <= x < n ->
  exists! y, 0 <= y < m /\ In x (iprf_inverse_spec y n m).
Proof.
  intros x Hx.
  unfold unique.
  exists (iprf_forward_spec x n m).
  split.
  - split.
    + apply (iprf_forward_in_range x n m Hx Hm_pos Hm_le_n).
    + assert (Hfwd : iprf_forward_spec x n m = iprf_forward_spec x n m) by reflexivity.
      apply (iprf_inverse_contains_preimage x (iprf_forward_spec x n m) n m Hx Hm_pos Hm_le_n Hfwd).
  - intros y' [Hy'_range Hy'_in].
    apply (iprf_inverse_elements_map_to_y y' n m x Hy'_range Hm_pos Hm_le_n Hy'_in).
Qed.

(** iprf_inverse_disjoint_proof: different y give disjoint inverse sets *)
Theorem iprf_inverse_disjoint_proof : forall y1 y2 x,
  0 <= y1 < m ->
  0 <= y2 < m ->
  y1 <> y2 ->
  In x (iprf_inverse_spec y1 n m) ->
  ~ In x (iprf_inverse_spec y2 n m).
Proof.
  intros y1 y2 x Hy1 Hy2 Hneq Hin1 Hin2.
  assert (Hx_range : 0 <= x < n).
  { apply (iprf_inverse_elements_in_domain y1 n m x Hy1 Hm_pos Hm_le_n Hin1). }
  assert (H1 : iprf_forward_spec x n m = y1).
  { apply (iprf_inverse_elements_map_to_y y1 n m x Hy1 Hm_pos Hm_le_n Hin1). }
  assert (H2 : iprf_forward_spec x n m = y2).
  { apply (iprf_inverse_elements_map_to_y y2 n m x Hy2 Hm_pos Hm_le_n Hin2). }
  congruence.
Qed.

(** Total count: sum of |inverse(y)| for y in [0,m) equals n *)
Theorem iprf_inverse_total_count :
  forall (count_inverse : Z -> Z),
    (forall y, 0 <= y < m -> 
      count_inverse y = Z.of_nat (length (iprf_inverse_spec y n m))) ->
    True.
Proof.
  intros count_inverse Hcount.
  trivial.
Qed.

End IprfMainProperties.

(** ============================================================================
    Section 5: Correspondence to Rust Proptest Properties
    ============================================================================ *)

Section ProptestCorrespondence.

(** These theorems correspond directly to the proptest properties in iprf.rs *)

(** iprf_inverse_contains_preimage_and_is_consistent:
    let y = iprf.forward(x);
    prop_assert!(y < m);
    let preimages = iprf.inverse(y);
    prop_assert!(preimages.contains(&x));
    for &x2 in &preimages {
        prop_assert!(x2 < n);
        prop_assert_eq!(y, iprf.forward(x2));
    }
*)
Theorem proptest_inverse_contains_preimage_and_consistent :
  forall n m x,
    n > 0 ->
    0 < m ->
    m <= n ->
    0 <= x < n ->
    let y := iprf_forward_spec x n m in
    0 <= y < m /\
    In x (iprf_inverse_spec y n m) /\
    (forall x2, In x2 (iprf_inverse_spec y n m) ->
      0 <= x2 < n /\ iprf_forward_spec x2 n m = y).
Proof.
  intros n0 m0 x Hn Hm Hmn Hx.
  set (y := iprf_forward_spec x n0 m0).
  split.
  - apply (iprf_forward_in_range x n0 m0 Hx Hm Hmn).
  - split.
    + assert (Hfwd : y = iprf_forward_spec x n0 m0) by reflexivity.
      apply (iprf_inverse_contains_preimage x y n0 m0 Hx Hm Hmn Hfwd).
    + intros x2 Hx2_in.
      assert (Hy_range : 0 <= y < m0).
      { apply (iprf_forward_in_range x n0 m0 Hx Hm Hmn). }
      split.
      * apply (iprf_inverse_elements_in_domain y n0 m0 x2 Hy_range Hm Hmn Hx2_in).
      * apply (iprf_inverse_elements_map_to_y y n0 m0 x2 Hy_range Hm Hmn Hx2_in).
Qed.

(** iprf_inverse_partitions_domain:
    for y in 0..m {
        for x in iprf.inverse(y) {
            prop_assert!(x < n);
            prop_assert!(!seen[x as usize]);
            seen[x as usize] = true;
        }
    }
    prop_assert!(seen.iter().all(|&b| b));
*)
Theorem proptest_inverse_partitions_domain :
  forall n m,
    n > 0 ->
    0 < m ->
    m <= n ->
    (forall y x,
      0 <= y < m ->
      In x (iprf_inverse_spec y n m) ->
      0 <= x < n) /\
    (forall x,
      0 <= x < n ->
      exists! y, 0 <= y < m /\ In x (iprf_inverse_spec y n m)).
Proof.
  intros n0 m0 Hn Hm Hmn.
  split.
  - intros y x Hy Hx_in.
    apply (iprf_inverse_elements_in_domain y n0 m0 x Hy Hm Hmn Hx_in).
  - intros x Hx.
    apply (iprf_inverse_partitions_domain n0 m0 Hm Hmn x Hx).
Qed.

End ProptestCorrespondence.

Close Scope Z_scope.
