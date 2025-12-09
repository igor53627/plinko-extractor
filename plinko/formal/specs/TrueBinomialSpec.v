(** * TrueBinomialSpec: Specification of true derandomized binomial sampler
    
    This module specifies the inverse-CDF binomial sampler that produces
    a proper Binomial(n, p) distribution when prf_output is uniform.
    
    Key properties:
    1. When prf_output is uniform over [0, 2^64), output is Binomial(count, num/denom)
    2. Deterministic: same inputs always produce same output
    3. Range: output is always in [0, count]
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.
From Stdlib Require Import Reals.
From Stdlib Require Import Lia.
Require Import Plinko.Specs.CommonTypes.

Open Scope Z_scope.

(** ** Binomial PMF using rationals for exact arithmetic *)

(** Binomial coefficient C(n, k) *)
Fixpoint binomial_coeff (n k : nat) : Z :=
  match k with
  | O => 1
  | S k' =>
      match n with
      | O => 0
      | S n' => binomial_coeff n' k' + binomial_coeff n' k
      end
  end.

(** Binomial PMF: P(X = k) = C(n,k) * p^k * (1-p)^(n-k)
    Represented as a rational for exact computation.
    p = num/denom *)
Definition binom_pmf_Q (n k : nat) (num denom : Z) : Q :=
  let coeff := binomial_coeff n k in
  let p_num := Z.pow num (Z.of_nat k) in
  let q_num := Z.pow (denom - num) (Z.of_nat (n - k)) in
  let total_denom := Z.pow denom (Z.of_nat n) in
  Qmake (coeff * p_num * q_num) (Z.to_pos total_denom).

(** Binomial CDF: P(X <= k) = sum_{j=0}^{k} P(X = j) *)
Fixpoint binom_cdf_Q (n : nat) (num denom : Z) (k : nat) : Q :=
  match k with
  | O => binom_pmf_Q n 0 num denom
  | S k' => Qplus (binom_cdf_Q n num denom k') (binom_pmf_Q n (S k') num denom)
  end.

(** ** Mapping u64 to uniform [0,1) *)

(** Convert prf_output to a rational in (0, 1) *)
Definition u64_to_Q (prf_output : Z) : Q :=
  Qmake (prf_output * 2 + 1) (2^65).

(** ** Inverse CDF specification *)

(** The ideal binomial quantile function:
    Given u in [0,1), return the smallest k such that CDF(k) >= u *)
Fixpoint binom_quantile_aux (n : nat) (num denom : Z) (u : Q) (k : nat) : nat :=
  match n with
  | O => O
  | S n' =>
      if Qle_bool u (binom_cdf_Q (S n') num denom k) then k
      else
        match k with
        | O => binom_quantile_aux n num denom u 1
        | S k' => 
            if Nat.leb k n then binom_quantile_aux n num denom u (S k)
            else n
        end
  end.

Definition binom_quantile (n : nat) (num denom : Z) (u : Q) : nat :=
  binom_quantile_aux n num denom u 0.

(** ** Main specification: true binomial sampler *)

(** The true binomial sampler using inverse-CDF transform *)
Definition true_binomial_sample_spec (count num denom prf_output : Z) : Z :=
  if Z.eqb denom 0 then 0
  else if Z.eqb count 0 then 0
  else if Z.eqb num 0 then 0
  else if Z.leb denom num then count
  else
    let u := u64_to_Q prf_output in
    Z.of_nat (binom_quantile (Z.to_nat count) num denom u).

(** ** Key Properties *)

(** Edge case: denom = 0 returns 0 *)
Lemma true_binomial_zero_denom :
  forall count num prf_output,
    true_binomial_sample_spec count num 0 prf_output = 0.
Proof.
  intros. unfold true_binomial_sample_spec. reflexivity.
Qed.

(** Edge case: count = 0 returns 0 *)
Lemma true_binomial_zero_count :
  forall num denom prf_output,
    true_binomial_sample_spec 0 num denom prf_output = 0.
Proof.
  intros. unfold true_binomial_sample_spec.
  destruct (Z.eqb denom 0); reflexivity.
Qed.

(** Edge case: num = 0 returns 0 (all trials fail) *)
Lemma true_binomial_zero_num :
  forall count denom prf_output,
    0 < denom ->
    true_binomial_sample_spec count 0 denom prf_output = 0.
Proof.
  intros count denom prf_output Hdenom.
  unfold true_binomial_sample_spec.
  assert (Z.eqb denom 0 = false) by (apply Z.eqb_neq; lia).
  rewrite H.
  destruct (Z.eqb count 0); reflexivity.
Qed.

(** Edge case: num >= denom returns count (all trials succeed) *)
Lemma true_binomial_full_prob :
  forall count num denom prf_output,
    0 < denom ->
    0 < count ->
    denom <= num ->
    true_binomial_sample_spec count num denom prf_output = count.
Proof.
  intros count num denom prf_output Hdenom Hcount Hle.
  unfold true_binomial_sample_spec.
  assert (Z.eqb denom 0 = false) by (apply Z.eqb_neq; lia).
  assert (Z.eqb count 0 = false) by (apply Z.eqb_neq; lia).
  assert (Z.eqb num 0 = false) by (apply Z.eqb_neq; lia).
  assert (Z.leb denom num = true) by (apply Z.leb_le; lia).
  rewrite H, H0, H1, H2. reflexivity.
Qed.

(** Range property: result is always in [0, count] *)
Lemma true_binomial_range :
  forall count num denom prf_output,
    0 <= count ->
    0 <= num ->
    0 < denom ->
    0 <= true_binomial_sample_spec count num denom prf_output <= count.
Proof.
  intros count num denom prf_output Hcount Hnum Hdenom.
  unfold true_binomial_sample_spec.
  assert (Hdenom_neq: Z.eqb denom 0 = false) by (apply Z.eqb_neq; lia).
  rewrite Hdenom_neq.
  destruct (Z.eqb count 0) eqn:Hcount_eq.
  - apply Z.eqb_eq in Hcount_eq. subst. lia.
  - destruct (Z.eqb num 0) eqn:Hnum_eq.
    + lia.
    + destruct (Z.leb denom num) eqn:Hle.
      * lia.
      * split.
        -- apply Zle_0_nat.
        -- (* The quantile is always <= n by construction *)
           (* This would require proving properties of binom_quantile *)
           admit.
Admitted.

(** Determinism: same inputs always produce same output *)
Lemma true_binomial_deterministic :
  forall count num denom prf_output,
    true_binomial_sample_spec count num denom prf_output =
    true_binomial_sample_spec count num denom prf_output.
Proof.
  reflexivity.
Qed.

(** ** Distribution Property (main theorem)
    
    When prf_output is uniformly distributed over [0, 2^64),
    the output of true_binomial_sample_spec is distributed as Binomial(count, num/denom).
    
    This is stated informally here; a full probabilistic proof would require
    a probability monad or measure theory formalization.
*)

(** The CDF is non-decreasing *)
Lemma binom_cdf_monotone :
  forall n num denom k1 k2,
    0 <= num < denom ->
    0 < denom ->
    (k1 <= k2)%nat ->
    Qle (binom_cdf_Q n num denom k1) (binom_cdf_Q n num denom k2).
Proof.
  (* CDF is a sum of non-negative terms, so adding more terms only increases it *)
  admit.
Admitted.

(** The CDF reaches 1 at k = n *)
Lemma binom_cdf_complete :
  forall n num denom,
    0 <= num < denom ->
    0 < denom ->
    Qeq (binom_cdf_Q n num denom n) 1.
Proof.
  (* Sum of all PMF values equals 1 *)
  admit.
Admitted.

Close Scope Z_scope.
