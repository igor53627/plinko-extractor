(** SwapOrNotProofs.v - Proofs of key properties for the Swap-or-Not PRP

    Properties proven (corresponding to proptest/kani properties in iprf.rs):
    1. round_involutive: applying round twice returns to original
    2. forward_inverse_id: inverse(forward(x)) = x
    3. inverse_forward_id: forward(inverse(x)) = x
    4. forward_is_bijection: forward is a bijection on [0, N)
    5. forward_in_range: 0 <= x < N -> 0 <= forward(x) < N
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.

Require Import Plinko.Specs.CommonTypes.
Require Import Plinko.Specs.SwapOrNotSpec.

Open Scope Z_scope.

(** ============================================================================
    Section 1: Partner is an Involution
    ============================================================================ *)

Lemma mod_in_range : forall x m,
  m > 0 -> 0 <= x mod m < m.
Proof.
  intros x m Hm.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma mod_small : forall x m,
  m > 0 -> 0 <= x < m -> x mod m = x.
Proof.
  intros x m Hm Hx.
  apply Z.mod_small. lia.
Qed.

Theorem partner_in_range_full : forall k_i x,
  0 <= x < N -> 0 <= partner k_i x < N.
Proof.
  intros k_i x Hx.
  unfold partner.
  apply mod_in_range.
  exact N_pos.
Qed.

(** Partner is an involution: partner(partner(x)) = x
    
    Proof sketch:
    - partner(k, x) = (k + N - x mod N) mod N
    - Since 0 <= x < N, x mod N = x
    - So partner(k, x) = (k + N - x) mod N
    - Let p = partner(k, x). Then p is in [0, N).
    - partner(k, p) = (k + N - p) mod N
    - Substitute p: = (k + N - (k + N - x) mod N) mod N
    - This simplifies to x.
*)
Theorem partner_involutive_full : forall k_i x,
  0 <= x < N -> 0 <= k_i < N ->
  partner k_i (partner k_i x) = x.
Proof.
  intros k_i x Hx Hk.
  unfold partner.
  assert (HN : N > 0) by exact N_pos.
  assert (Hx_mod : x mod N = x).
  { apply Z.mod_small. lia. }
  rewrite Hx_mod.
  set (p := (k_i + N - x) mod N).
  assert (Hp_range : 0 <= p < N).
  { unfold p. apply Z.mod_pos_bound. lia. }
  assert (Hp_mod : p mod N = p).
  { apply Z.mod_small. lia. }
  rewrite Hp_mod.
  unfold p.
  assert (Hsum_lower : 0 < k_i + N - x) by lia.
  assert (Hsum_upper : k_i + N - x < 2 * N) by lia.
  destruct (Z_lt_dec (k_i + N - x) N) as [Hlt | Hge].
  - assert (Hmod_small : (k_i + N - x) mod N = k_i + N - x).
    { apply Z.mod_small. lia. }
    rewrite Hmod_small.
    assert (Hresult : (k_i + N - (k_i + N - x)) mod N = x).
    { replace (k_i + N - (k_i + N - x)) with x by ring.
      apply Z.mod_small. lia. }
    exact Hresult.
  - assert (Hge' : k_i + N - x >= N) by lia.
    assert (Hmod_sub : (k_i + N - x) mod N = k_i + N - x - N).
    { symmetry. apply Zmod_unique with 1.
      - lia.
      - ring. }
    rewrite Hmod_sub.
    assert (Hresult : (k_i + N - (k_i + N - x - N)) mod N = x).
    { replace (k_i + N - (k_i + N - x - N)) with (x + 1 * N) by ring.
      rewrite Z.mod_add by lia.
      apply Z.mod_small. lia. }
    exact Hresult.
Qed.

(** ============================================================================
    Section 2: Canonical Symmetry
    ============================================================================ *)

Theorem canonical_symmetric : forall k_i x,
  0 <= x < N -> 0 <= k_i < N ->
  canonical x (partner k_i x) = canonical (partner k_i x) x.
Proof.
  intros k_i x Hx Hk.
  unfold canonical.
  lia.
Qed.

Lemma canonical_partner_eq : forall k_i x,
  0 <= x < N -> 0 <= k_i < N ->
  canonical x (partner k_i x) = 
  canonical (partner k_i x) (partner k_i (partner k_i x)).
Proof.
  intros k_i x Hx Hk.
  rewrite partner_involutive_full by assumption.
  apply canonical_symmetric; assumption.
Qed.

(** ============================================================================
    Section 3: Round is an Involution
    ============================================================================ *)

(** Each round is an involution: round(round(x)) = x
    
    Key insight: Both x and partner(x) see the same canonical = max(x, partner(x)),
    so they make the same swap decision. If we swap x->partner, applying round again
    swaps partner->x since partner(partner(x)) = x.
*)
Theorem round_involutive_full : forall r x,
  0 <= x < N ->
  round_spec r (round_spec r x) = x.
Proof.
  intros r x Hx.
  unfold round_spec.
  set (k_i := round_key r).
  assert (Hk : 0 <= k_i < N) by apply round_key_in_range.
  set (p := partner k_i x).
  set (c := canonical x p).
  assert (Hp_range : 0 <= p < N).
  { unfold p. apply partner_in_range_full. assumption. }
  assert (Hp_inv : partner k_i p = x).
  { unfold p. apply partner_involutive_full; assumption. }
  assert (Hc_eq : canonical p (partner k_i p) = c).
  { unfold c. rewrite Hp_inv. unfold canonical. lia. }
  destruct (round_bit r c) eqn:Hbit.
  - rewrite Hc_eq. rewrite Hbit. rewrite Hp_inv. reflexivity.
  - fold p. fold c. rewrite Hbit. reflexivity.
Qed.

(** ============================================================================
    Section 4: Round Preserves Range
    ============================================================================ *)

Theorem round_in_range : forall r x,
  0 <= x < N ->
  0 <= round_spec r x < N.
Proof.
  intros r x Hx.
  unfold round_spec.
  set (k_i := round_key r).
  set (p := partner k_i x).
  set (c := canonical x p).
  destruct (round_bit r c).
  - apply partner_in_range_full. assumption.
  - assumption.
Qed.

(** ============================================================================
    Section 5: Forward/Inverse Round Composition Lemmas
    ============================================================================ *)

Lemma forward_rounds_in_range : forall n x,
  0 <= x < N ->
  0 <= forward_rounds n x < N.
Proof.
  intros n x Hx.
  induction n as [|n' IH].
  - simpl. assumption.
  - simpl. apply round_in_range. apply IH.
Qed.

Lemma inverse_rounds_in_range : forall n x,
  0 <= x < N ->
  0 <= inverse_rounds n x < N.
Proof.
  intros n.
  induction n as [|n' IH]; intros x Hx.
  - simpl. assumption.
  - simpl. apply IH. apply round_in_range. assumption.
Qed.

(** ============================================================================
    Section 6: Forward is in Range
    ============================================================================ *)

Theorem forward_in_range_full : forall x,
  0 <= x < N ->
  0 <= forward_spec x < N.
Proof.
  intros x Hx.
  unfold forward_spec.
  apply forward_rounds_in_range. assumption.
Qed.

Theorem inverse_in_range_full : forall x,
  0 <= x < N ->
  0 <= inverse_spec x < N.
Proof.
  intros x Hx.
  unfold inverse_spec.
  apply inverse_rounds_in_range. assumption.
Qed.

(** ============================================================================
    Section 7: Forward/Inverse Identity (Main Theorems)
    ============================================================================ *)

(** Key lemma: inverse then forward returns to original.
    
    Proof by induction on n:
    - Base: forward_rounds 0 (inverse_rounds 0 x) = x (trivial)
    - Step: forward_rounds (S n) (inverse_rounds (S n) x)
          = forward_rounds (S n) (inverse_rounds n (round_spec n x))
          = round_spec n (forward_rounds n (inverse_rounds n (round_spec n x)))
          By IH on (round_spec n x): = round_spec n (round_spec n x)
          By round_involutive: = x
*)
Lemma inverse_forward_rounds : forall n x,
  0 <= x < N ->
  forward_rounds n (inverse_rounds n x) = x.
Proof.
  intros n.
  induction n as [|n' IH]; intros x Hx.
  - simpl. reflexivity.
  - simpl.
    assert (Hrnd_range : 0 <= round_spec n' x < N).
    { apply round_in_range. assumption. }
    rewrite IH by assumption.
    apply round_involutive_full. assumption.
Qed.

(** Key lemma: forward then inverse returns to original.
    
    Proof by induction on n:
    - Base: inverse_rounds 0 (forward_rounds 0 x) = x (trivial)  
    - Step: inverse_rounds (S n) (forward_rounds (S n) x)
          = inverse_rounds (S n) (round_spec n (forward_rounds n x))
          = inverse_rounds n (round_spec n (round_spec n (forward_rounds n x)))
          By round_involutive: = inverse_rounds n (forward_rounds n x)
          By IH: = x
*)
Lemma forward_inverse_rounds : forall n x,
  0 <= x < N ->
  inverse_rounds n (forward_rounds n x) = x.
Proof.
  intros n.
  induction n as [|n' IH]; intros x Hx.
  - simpl. reflexivity.
  - simpl.
    assert (Hfwd_range : 0 <= forward_rounds n' x < N).
    { apply forward_rounds_in_range. assumption. }
    rewrite round_involutive_full by assumption.
    apply IH. assumption.
Qed.

Theorem forward_inverse_id_full : forall x,
  0 <= x < N ->
  inverse_spec (forward_spec x) = x.
Proof.
  intros x Hx.
  unfold forward_spec, inverse_spec.
  apply forward_inverse_rounds. assumption.
Qed.

Theorem inverse_forward_id_full : forall x,
  0 <= x < N ->
  forward_spec (inverse_spec x) = x.
Proof.
  intros x Hx.
  unfold forward_spec, inverse_spec.
  apply inverse_forward_rounds. assumption.
Qed.

(** ============================================================================
    Section 8: Forward is a Bijection
    ============================================================================ *)

Theorem forward_injective : forall x1 x2,
  0 <= x1 < N -> 0 <= x2 < N ->
  forward_spec x1 = forward_spec x2 ->
  x1 = x2.
Proof.
  intros x1 x2 Hx1 Hx2 Heq.
  assert (H1 : inverse_spec (forward_spec x1) = x1).
  { apply forward_inverse_id_full. assumption. }
  assert (H2 : inverse_spec (forward_spec x2) = x2).
  { apply forward_inverse_id_full. assumption. }
  rewrite Heq in H1.
  congruence.
Qed.

Theorem forward_surjective : forall y,
  0 <= y < N ->
  exists x, 0 <= x < N /\ forward_spec x = y.
Proof.
  intros y Hy.
  exists (inverse_spec y).
  split.
  - apply inverse_in_range_full. assumption.
  - apply inverse_forward_id_full. assumption.
Qed.

Theorem forward_is_bijection :
  (forall x1 x2, 0 <= x1 < N -> 0 <= x2 < N ->
    forward_spec x1 = forward_spec x2 -> x1 = x2) /\
  (forall y, 0 <= y < N -> 
    exists x, 0 <= x < N /\ forward_spec x = y).
Proof.
  split.
  - exact forward_injective.
  - exact forward_surjective.
Qed.
