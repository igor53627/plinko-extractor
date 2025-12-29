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
From Stdlib Require Import Setoid.
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

(** Binomial coefficient is always non-negative *)
Lemma binomial_coeff_nonneg : forall n k, (0 <= binomial_coeff n k)%Z.
Proof.
  induction n as [|n' IHn]; intros k.
  - destruct k; simpl; lia.
  - destruct k as [|k']; simpl.
    + lia.
    + pose proof (IHn k') as H1. pose proof (IHn (S k')) as H2. lia.
Qed.

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

(** The binomial quantile function using explicit fuel for termination.
    Given u in [0,1), return the smallest k such that CDF(k) >= u.
    
    Uses fuel parameter (bounded by n+1) to ensure structural recursion. *)
Fixpoint binom_quantile_aux (n : nat) (num denom : Z) (u : Q) (fuel k : nat) : nat :=
  match fuel with
  | O => k
  | S fuel' =>
      if Qle_bool u (binom_cdf_Q n num denom k) then k
      else if Nat.leb k n then
             binom_quantile_aux n num denom u fuel' (S k)
           else
             n
  end.

Definition binom_quantile (n : nat) (num denom : Z) (u : Q) : nat :=
  binom_quantile_aux n num denom u (S n) 0.

(** Quantile is bounded: result <= k + fuel *)
Lemma binom_quantile_aux_bound :
  forall n num denom u fuel k,
    (binom_quantile_aux n num denom u fuel k <= k + fuel)%nat.
Proof.
  induction fuel as [|fuel' IH]; intros k; simpl.
  - rewrite Nat.add_0_r. apply Nat.le_refl.
  - destruct (Qle_bool u (binom_cdf_Q n num denom k)).
    + apply Nat.le_trans with k.
      * apply Nat.le_refl.
      * apply Nat.le_add_r.
    + destruct (Nat.leb k n) eqn:Hleb.
      * specialize (IH (S k)).
        eapply Nat.le_trans; [exact IH|].
        rewrite <- Nat.add_succ_comm. apply Nat.le_refl.
      * apply Nat.leb_nle in Hleb.
        apply Nat.nle_gt in Hleb.
        apply Nat.le_trans with k.
        -- apply Nat.lt_le_incl. exact Hleb.
        -- apply Nat.le_add_r.
Qed.

(** Helper: Qle_bool reflects Qle *)
Lemma Qle_bool_iff : forall x y, Qle_bool x y = true <-> Qle x y.
Proof.
  intros x y.
  split.
  - intro H. apply Qle_bool_imp_le. exact H.
  - intro H. unfold Qle_bool, Qle in *.
    apply Z.leb_le. exact H.
Qed.

Lemma Qle_bool_false_iff : forall x y, Qle_bool x y = false <-> ~ Qle x y.
Proof.
  intros x y.
  destruct (Qle_bool x y) eqn:Hb.
  - split; intro H; [discriminate | apply Qle_bool_iff in Hb; contradiction].
  - split; intro; [|reflexivity].
    intro Hle. apply Qle_bool_iff in Hle. rewrite Hle in Hb. discriminate.
Qed.

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

(** ** PMF Non-negativity *)

(** Z.pow is non-negative for non-negative base *)
Lemma Zpow_nonneg_of_nat :
  forall a (m : nat),
    0 <= a ->
    0 <= Z.pow a (Z.of_nat m).
Proof.
  intros a m Ha.
  apply Z.pow_nonneg. exact Ha.
Qed.

(** PMF terms are non-negative *)
Lemma binom_pmf_Q_nonneg :
  forall n k num denom,
    0 <= num < denom ->
    0 < denom ->
    Qle 0 (binom_pmf_Q n k num denom).
Proof.
  intros n k num denom [Hnum_le Hnum_lt] Hdenom.
  unfold binom_pmf_Q.
  set (coeff := binomial_coeff n k).
  set (p_num := Z.pow num (Z.of_nat k)).
  set (q_num := Z.pow (denom - num) (Z.of_nat (n - k))).
  set (total_denom := Z.pow denom (Z.of_nat n)).
  assert (Hcoeff: 0 <= coeff) by (subst coeff; apply binomial_coeff_nonneg).
  assert (Hp: 0 <= p_num) by (subst p_num; apply Zpow_nonneg_of_nat; lia).
  assert (Hq: 0 <= q_num) by (subst q_num; apply Zpow_nonneg_of_nat; lia).
  assert (Htd: 0 < total_denom) by (subst total_denom; apply Z.pow_pos_nonneg; lia).
  unfold Qle. simpl.
  assert (0 <= coeff * p_num * q_num).
  { apply Z.mul_nonneg_nonneg; [apply Z.mul_nonneg_nonneg|]; assumption. }
  lia.
Qed.

(** ** CDF Properties *)

(** CDF step: adding a PMF term increases CDF *)
Lemma binom_cdf_step_monotone :
  forall n num denom k,
    0 <= num < denom ->
    0 < denom ->
    Qle (binom_cdf_Q n num denom k)
        (binom_cdf_Q n num denom (S k)).
Proof.
  intros n num denom k Hrange Hdenom.
  simpl.
  rewrite <- Qplus_0_r at 1.
  apply Qplus_le_compat.
  - apply Qle_refl.
  - apply binom_pmf_Q_nonneg; assumption.
Qed.

(** The CDF is non-decreasing *)
Lemma binom_cdf_monotone :
  forall n num denom k1 k2,
    0 <= num < denom ->
    0 < denom ->
    (k1 <= k2)%nat ->
    Qle (binom_cdf_Q n num denom k1) (binom_cdf_Q n num denom k2).
Proof.
  intros n num denom k1 k2 Hrange Hdenom Hle.
  induction k2 as [|k2 IH].
  - inversion Hle. apply Qle_refl.
  - destruct (Nat.eq_dec k1 (S k2)) as [Heq | Hneq].
    + subst. apply Qle_refl.
    + assert (Hlt : (k1 <= k2)%nat) by lia.
      specialize (IH Hlt).
      eapply Qle_trans; [exact IH|].
      apply binom_cdf_step_monotone; assumption.
Qed.

(** ** Binomial Theorem (integer version) *)

(** Sum from 0 to n *)
Fixpoint Zsum_0_n (f : nat -> Z) (n : nat) : Z :=
  match n with
  | O => f O
  | S n' => Zsum_0_n f n' + f (S n')
  end.

(** Binomial theorem over Z: (a + b)^n = sum_{k=0}^n C(n,k) * a^k * b^{n-k}
    
    This is a standard combinatorial identity. The proof requires:
    - Pascal's identity: C(n+1, k) = C(n, k-1) + C(n, k)
    - Algebraic manipulation of power sums
    - Reindexing of summations
    
    We admit this theorem as it is well-established mathematically.
    A full Coq proof would require ~100 lines of careful algebraic reasoning. *)
(** Binomial theorem: (a + b)^n = sum_{k=0}^n C(n,k) * a^k * b^{n-k}
    This is a standard combinatorial identity. The full Coq proof requires
    ~100 lines of careful algebraic reasoning with Pascal's identity,
    power sum manipulation, and sum reindexing.
    We axiomatize it as it is mathematically well-established. *)
Axiom binomial_theorem_Z :
  forall n a b,
    Z.pow (a + b) (Z.of_nat n) =
    Zsum_0_n
      (fun k =>
         binomial_coeff n k
           * Z.pow a (Z.of_nat k)
           * Z.pow b (Z.of_nat (n - k)))
      n.

(** Helper: PMF numerator *)
Definition binom_pmf_num (n k : nat) (num denom : Z) : Z :=
  binomial_coeff n k * Z.pow num (Z.of_nat k) * Z.pow (denom - num) (Z.of_nat (n - k)).

(** Helper: CDF numerator sum *)
Fixpoint binom_cdf_num (n : nat) (num denom : Z) (k : nat) : Z :=
  match k with
  | O => binom_pmf_num n 0 num denom
  | S k' => binom_cdf_num n num denom k' + binom_pmf_num n (S k') num denom
  end.

(** CDF numerator equals Zsum *)
Lemma binom_cdf_num_eq_Zsum :
  forall n num denom k,
    binom_cdf_num n num denom k = Zsum_0_n (fun j => binom_pmf_num n j num denom) k.
Proof.
  induction k as [|k' IH]; intros.
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** Zsum with binom_pmf_num equals Zsum with expanded form *)
Lemma Zsum_binom_pmf_num_eq :
  forall n num denom m,
    Zsum_0_n (fun j => binom_pmf_num n j num denom) m =
    Zsum_0_n (fun k => binomial_coeff n k * Z.pow num (Z.of_nat k) * Z.pow (denom - num) (Z.of_nat (n - k))) m.
Proof.
  induction m as [|m' IH]; intros.
  - simpl. unfold binom_pmf_num. simpl. ring.
  - simpl. rewrite IH. unfold binom_pmf_num. reflexivity.
Qed.

(** PMF as Qmake with common denominator *)
Lemma binom_pmf_Q_eq :
  forall n k num denom,
    0 < denom ->
    binom_pmf_Q n k num denom = Qmake (binom_pmf_num n k num denom) (Z.to_pos (Z.pow denom (Z.of_nat n))).
Proof.
  intros. unfold binom_pmf_Q, binom_pmf_num. reflexivity.
Qed.

(** Helper: Qplus of Qmakes with same denom *)
Lemma Qplus_same_denom :
  forall a b d,
    Qeq (Qplus (Qmake a d) (Qmake b d)) (Qmake (a + b) d).
Proof.
  intros a b d.
  unfold Qeq, Qplus. simpl.
  rewrite Pos2Z.inj_mul.
  ring.
Qed.

(** CDF equals Qmake of numerator sum over common denominator *)
Lemma binom_cdf_Q_eq :
  forall n num denom k,
    0 < denom ->
    Qeq (binom_cdf_Q n num denom k)
        (Qmake (binom_cdf_num n num denom k) (Z.to_pos (Z.pow denom (Z.of_nat n)))).
Proof.
  induction k as [|k' IH]; intros Hdenom.
  - simpl. rewrite binom_pmf_Q_eq by assumption. apply Qeq_refl.
  - simpl.
    assert (Hpow_pos : 0 < Z.pow denom (Z.of_nat n)).
    { apply Z.pow_pos_nonneg; lia. }
    specialize (IH Hdenom).
    rewrite binom_pmf_Q_eq by assumption.
    set (d := Z.to_pos (Z.pow denom (Z.of_nat n))).
    eapply Qeq_trans.
    + apply Qplus_comp; [apply IH | apply Qeq_refl].
    + apply Qplus_same_denom.
Qed.

(** Helper: relate binom_cdf_Q sum to Zsum_0_n *)
Lemma binom_cdf_as_Zsum :
  forall n num denom,
    0 < denom ->
    let total_denom := Z.pow denom (Z.of_nat n) in
    Qeq (binom_cdf_Q n num denom n)
        (Qmake (Zsum_0_n
                  (fun k => binomial_coeff n k
                            * Z.pow num (Z.of_nat k)
                            * Z.pow (denom - num) (Z.of_nat (n - k)))
                  n)
               (Z.to_pos total_denom)).
Proof.
  intros n num denom Hdenom total_denom.
  eapply Qeq_trans.
  - apply binom_cdf_Q_eq. exact Hdenom.
  - unfold Qeq. simpl.
    rewrite binom_cdf_num_eq_Zsum.
    assert (Hpow_pos : 0 < Z.pow denom (Z.of_nat n)).
    { apply Z.pow_pos_nonneg; lia. }
    rewrite !Z2Pos.id by lia.
    rewrite Zsum_binom_pmf_num_eq.
    reflexivity.
Qed.

(** The CDF reaches 1 at k = n *)
Lemma binom_cdf_complete :
  forall n num denom,
    0 <= num < denom ->
    0 < denom ->
    Qeq (binom_cdf_Q n num denom n) 1.
Proof.
  intros n num denom [Hnum_lo Hnum_hi] Hdenom.
  assert (Hsum: Zsum_0_n
                  (fun k => binomial_coeff n k
                            * Z.pow num (Z.of_nat k)
                            * Z.pow (denom - num) (Z.of_nat (n - k)))
                  n
                = Z.pow denom (Z.of_nat n)).
  { rewrite <- binomial_theorem_Z.
    f_equal. lia.
  }
  eapply Qeq_trans.
  - apply binom_cdf_as_Zsum. exact Hdenom.
  - rewrite Hsum.
    unfold Qeq. simpl.
    assert (Hpow_pos: 0 < Z.pow denom (Z.of_nat n)).
    { apply Z.pow_pos_nonneg; lia. }
    rewrite Z2Pos.id by lia.
    ring.
Qed.

(** Auxiliary lemma: quantile search never exceeds n when u <= 1 and CDF(n) = 1 *)
Lemma binom_quantile_aux_le_n :
  forall n num denom u fuel k,
    0 < denom ->
    0 <= num < denom ->
    Qle u 1 ->
    (k <= n)%nat ->
    (binom_quantile_aux n num denom u fuel k <= n)%nat.
Proof.
  intros n num denom u fuel.
  induction fuel as [|fuel' IH]; intros k Hdenom Hrange Hu_le1 Hk_le_n; simpl.
  - lia.
  - destruct (Qle_bool u (binom_cdf_Q n num denom k)) eqn:Hu_le_cdf_k.
    + lia.
    + destruct (Nat.leb k n) eqn:Hk_le_n_bool.
      * apply Nat.leb_le in Hk_le_n_bool.
        assert (Hk_cases : (k < n \/ k = n)%nat) by lia.
        destruct Hk_cases as [Hk_lt_n | Hk_eq_n].
        -- apply IH; try lia; assumption.
        -- subst k.
           assert (Hcdf1 : Qeq (binom_cdf_Q n num denom n) 1).
           { apply binom_cdf_complete; assumption. }
           assert (Hu_le_cdf_n : Qle u (binom_cdf_Q n num denom n)).
           { rewrite Hcdf1. exact Hu_le1. }
           apply Qle_bool_false_iff in Hu_le_cdf_k.
           contradiction.
      * lia.
Qed.

(** Quantile is bounded by n for valid parameters and u <= 1 *)
Lemma binom_quantile_le_n :
  forall n num denom u,
    0 < denom ->
    0 <= num < denom ->
    Qle u 1 ->
    (binom_quantile n num denom u <= n)%nat.
Proof.
  intros n num denom u Hdenom Hrange Hu_le1.
  unfold binom_quantile.
  apply (binom_quantile_aux_le_n n num denom u (S n) 0); try assumption; lia.
Qed.

(** u64_to_Q is in (0, 1) for valid prf_output *)
Lemma u64_to_Q_le_1 :
  forall prf_output,
    0 <= prf_output < Z.pow 2 64 ->
    Qle (u64_to_Q prf_output) 1.
Proof.
  intros prf_output [Hlo Hhi].
  unfold u64_to_Q, Qle. simpl.
  assert (prf_output * 2 + 1 <= 2^65 - 1) by lia.
  lia.
Qed.

(** Range property: result is always in [0, count] *)
Lemma true_binomial_range :
  forall count num denom prf_output,
    0 <= count ->
    0 <= num < denom ->
    0 < denom ->
    0 <= prf_output < Z.pow 2 64 ->
    0 <= true_binomial_sample_spec count num denom prf_output <= count.
Proof.
  intros count num denom prf_output Hcount [Hnum_lo Hnum_hi] Hdenom Hprf.
  unfold true_binomial_sample_spec.
  assert (Hdenom_neq: Z.eqb denom 0 = false) by (apply Z.eqb_neq; lia).
  rewrite Hdenom_neq.
  destruct (Z.eqb count 0) eqn:Hcount_eq.
  - apply Z.eqb_eq in Hcount_eq. subst. lia.
  - destruct (Z.eqb num 0) eqn:Hnum_eq.
    + lia.
    + destruct (Z.leb denom num) eqn:Hle.
      * apply Z.leb_le in Hle. lia.
      * apply Z.leb_nle in Hle.
        split.
        -- apply Nat2Z.is_nonneg.
        -- assert (Hrange : 0 <= num < denom) by lia.
           assert (Hu_le1 : Qle (u64_to_Q prf_output) 1) by (apply u64_to_Q_le_1; assumption).
           pose proof (binom_quantile_le_n (Z.to_nat count) num denom (u64_to_Q prf_output) Hdenom Hrange Hu_le1) as Hqle.
           apply Nat2Z.inj_le in Hqle.
           rewrite Z2Nat.id in Hqle by lia.
           exact Hqle.
Qed.

Close Scope Z_scope.
