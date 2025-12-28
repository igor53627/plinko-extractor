(** * BinomialSpec: Specification of binomial_sample function *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import Plinko.Specs.CommonTypes.

Open Scope Z_scope.

(** Specification of binomial_sample matching the Rust implementation:
    binomial_sample(count, num, denom, prf_output) =
      (count * num + (prf_output mod (denom + 1))) / denom
*)
Definition binomial_sample_spec (count num denom prf_output : Z) : Z :=
  if Z.eqb denom 0 then
    0
  else if Z.eqb count 0 then
    0
  else
    (count * num + (prf_output mod (denom + 1))) / denom.

(** Zero denominator returns 0 *)
Lemma binomial_sample_zero_denom :
  forall count num prf_output,
    binomial_sample_spec count num 0 prf_output = 0.
Proof.
  intros. unfold binomial_sample_spec. reflexivity.
Qed.

(** Result is bounded: 0 <= result <= count when count > 0, num < denom, and denom > 0.
    
    The key insight is:
    - numerator = count * num + r where 0 <= r <= denom
    - result = numerator / denom
    - When count > 0 and num < denom: we have slack to absorb the r term
    
    Note: The PMNS use case has ball_count >= 1 when there are balls, and left_bins < total_bins.
    The count = 0 case is handled separately by binomial_sample_range_zero. *)
Lemma binomial_sample_range :
  forall count num denom prf_output,
    0 < count ->
    0 <= num ->
    num < denom ->
    0 < denom ->
    0 <= binomial_sample_spec count num denom prf_output <= count.
Proof.
  intros count num denom prf_output Hcount_pos Hnum Hnum_lt Hdenom.
  unfold binomial_sample_spec.
  assert (Hdenom_neq: Z.eqb denom 0 = false) by (apply Z.eqb_neq; lia).
  assert (Hcount_neq: Z.eqb count 0 = false) by (apply Z.eqb_neq; lia).
  rewrite Hdenom_neq, Hcount_neq.
  set (r := prf_output mod (denom + 1)).
  assert (Hr_bounds: 0 <= r < denom + 1).
  { subst r. apply Z.mod_pos_bound. lia. }
  split.
  - apply Z.div_pos; lia.
  - assert (Hstep1 : count * num <= count * (denom - 1)).
    { assert (num <= denom - 1) by lia. 
      apply Z.mul_le_mono_nonneg_l; lia. }
    assert (Hstep2 : count * num + r <= count * (denom - 1) + denom) by lia.
    assert (Hstep3 : count * (denom - 1) + denom < denom * (count + 1)).
    { ring_simplify. lia. }
    assert (Hstep4 : count * num + r < denom * (count + 1)) by lia.
    assert (Hlt : (count * num + r) / denom < count + 1).
    { apply Z.div_lt_upper_bound; assumption. }
    lia.
Qed.

(** For count = 0, the result is exactly 0 (degenerate binomial with no trials). *)
Lemma binomial_sample_range_zero :
  forall num denom prf_output,
    0 <= num ->
    num < denom ->
    0 < denom ->
    0 <= binomial_sample_spec 0 num denom prf_output <= 0.
Proof.
  intros num denom prf_output Hnum Hnum_lt Hdenom.
  unfold binomial_sample_spec.
  assert (Hdenom_neq: Z.eqb denom 0 = false) by (apply Z.eqb_neq; lia).
  rewrite Hdenom_neq. simpl.
  lia.
Qed.

(** Combined range lemma covering both count = 0 and count > 0 *)
Lemma binomial_sample_range_full :
  forall count num denom prf_output,
    0 <= count ->
    0 <= num ->
    num < denom ->
    0 < denom ->
    0 <= binomial_sample_spec count num denom prf_output <= count.
Proof.
  intros count num denom prf_output Hcount Hnum Hnum_lt Hdenom.
  destruct (Z.eq_dec count 0) as [Hcount_zero | Hcount_pos].
  - subst count. apply binomial_sample_range_zero; assumption.
  - apply binomial_sample_range; lia.
Qed.

(** Monotonicity: larger count gives larger or equal result *)
Lemma binomial_sample_monotone_count :
  forall count1 count2 num denom prf_output,
    0 <= count1 ->
    count1 <= count2 ->
    0 <= num ->
    0 < denom ->
    binomial_sample_spec count1 num denom prf_output <=
    binomial_sample_spec count2 num denom prf_output.
Proof.
  intros count1 count2 num denom prf_output Hcount1 Hle Hnum Hdenom.
  unfold binomial_sample_spec.
  assert (Hdenom_neq: Z.eqb denom 0 = false) by (apply Z.eqb_neq; lia).
  rewrite Hdenom_neq.
  destruct (Z.eq_dec count1 0) as [Hc1_zero | Hc1_pos].
  - subst count1. simpl.
    destruct (Z.eq_dec count2 0) as [Hc2_zero | Hc2_pos].
    + subst count2. simpl. lia.
    + assert (Hc2_neq : Z.eqb count2 0 = false) by (apply Z.eqb_neq; lia).
      rewrite Hc2_neq.
      apply Z.div_pos; try lia.
      apply Z.add_nonneg_nonneg.
      * apply Z.mul_nonneg_nonneg; lia.
      * apply Z.mod_pos_bound. lia.
  - assert (Hc2_pos : 0 < count2) by lia.
    assert (Hc1_neq : Z.eqb count1 0 = false) by lia.
    assert (Hc2_neq : Z.eqb count2 0 = false) by lia.
    rewrite Hc1_neq, Hc2_neq.
    apply Z.div_le_mono.
    + lia.
    + assert (count1 * num <= count2 * num) by nia. lia.
Qed.

(** Predicate form for use in other specifications *)
Definition binomial_sample_valid (count num denom prf_output result : Z) : Prop :=
  result = binomial_sample_spec count num denom prf_output.

Close Scope Z_scope.
