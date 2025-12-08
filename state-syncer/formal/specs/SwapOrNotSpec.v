(** SwapOrNotSpec.v - Formal specification of SwapOrNot PRP
    
    Based on Morris-Rogaway 2013: "How to Encipher Messages on a Small Domain"
    Reference: state-syncer/src/iprf.rs
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.

Require Import Plinko.Specs.CommonTypes.

Open Scope Z_scope.

(** Domain size: 2^64 for u64 compatibility with Rust implementation *)

Definition N : Z := Z.pow 2 64.

Lemma N_pos : N > 0.
Proof.
  unfold N. vm_compute. reflexivity.
Qed.

Parameter num_rounds : nat.

Parameter round_key : nat -> Z.

Parameter round_bit : nat -> Z -> bool.

(** Partner function: K_i - X mod N *)
Definition partner (k_i x : Z) : Z :=
  (k_i + N - (x mod N)) mod N.

(** Canonical representative: max(X, X') *)
Definition canonical (x x' : Z) : Z :=
  Z.max x x'.

(** Single round of swap-or-not *)
Definition round_spec (r : nat) (x : Z) : Z :=
  let k_i := round_key r in
  let x' := partner k_i x in
  let c := canonical x x' in
  if round_bit r c then x' else x.

(** Forward permutation: apply rounds 0..num_rounds-1 *)
Fixpoint forward_rounds (n : nat) (x : Z) : Z :=
  match n with
  | O => x
  | S n' => round_spec n' (forward_rounds n' x)
  end.

Definition forward_spec (x : Z) : Z :=
  forward_rounds num_rounds x.

(** Inverse permutation: apply rounds num_rounds-1..0 *)
Fixpoint inverse_rounds (n : nat) (x : Z) : Z :=
  match n with
  | O => x
  | S n' => inverse_rounds n' (round_spec n' x)
  end.

Definition inverse_spec (x : Z) : Z :=
  inverse_rounds num_rounds x.

(** Key lemmas *)

Lemma partner_in_range : forall k_i x,
  0 <= x < N -> 0 <= partner k_i x < N.
Proof.
  intros k_i x Hx.
  unfold partner.
  apply Z.mod_pos_bound.
  pose proof N_pos. lia.
Qed.

Lemma partner_involutive : forall k_i x,
  0 <= x < N -> partner k_i (partner k_i x) = x.
Proof.
  intros k_i x Hx.
  unfold partner.
  assert (HN : N > 0) by (pose proof N_pos; lia).
  assert (Hx_mod : x mod N = x) by (apply Z.mod_small; lia).
  rewrite Hx_mod.
  rewrite Z.mod_mod by lia.
  rewrite Zminus_mod_idemp_r.
  replace (k_i + N - (k_i + N - x)) with x by ring.
  apply Z.mod_small. lia.
Qed.

Lemma canonical_comm : forall x y,
  canonical x y = canonical y x.
Proof.
  intros x y. unfold canonical. lia.
Qed.

Axiom round_key_in_range : forall r, 0 <= round_key r < N.

Lemma round_in_range : forall r x,
  0 <= x < N -> 0 <= round_spec r x < N.
Proof.
  intros r x Hx.
  unfold round_spec.
  destruct (round_bit r (canonical x (partner (round_key r) x))).
  - apply partner_in_range. assumption.
  - assumption.
Qed.

Lemma round_involutive : forall r x,
  0 <= x < N -> round_spec r (round_spec r x) = x.
Proof.
  intros r x Hx.
  unfold round_spec.
  set (k_i := round_key r).
  set (p := partner k_i x).
  set (c := canonical x p).
  assert (Hp_range : 0 <= p < N) by (unfold p; apply partner_in_range; assumption).
  assert (Hp_inv : partner k_i p = x) by (unfold p; apply partner_involutive; assumption).
  assert (Hc_eq : canonical p (partner k_i p) = c).
  { unfold c. rewrite Hp_inv. unfold canonical. lia. }
  destruct (round_bit r c) eqn:Hbit.
  - rewrite Hc_eq. rewrite Hbit. rewrite Hp_inv. reflexivity.
  - fold p. fold c. rewrite Hbit. reflexivity.
Qed.

Lemma forward_rounds_in_range : forall n x,
  0 <= x < N -> 0 <= forward_rounds n x < N.
Proof.
  intros n x Hx.
  induction n as [|n' IH].
  - simpl. assumption.
  - simpl. apply round_in_range. apply IH.
Qed.

Lemma inverse_rounds_in_range : forall n x,
  0 <= x < N -> 0 <= inverse_rounds n x < N.
Proof.
  intros n.
  induction n as [|n' IH]; intros x Hx.
  - simpl. assumption.
  - simpl. apply IH. apply round_in_range. assumption.
Qed.

Lemma forward_inverse_rounds : forall n x,
  0 <= x < N -> inverse_rounds n (forward_rounds n x) = x.
Proof.
  intros n.
  induction n as [|n' IH]; intros x Hx.
  - simpl. reflexivity.
  - simpl.
    assert (Hfwd_range : 0 <= forward_rounds n' x < N).
    { apply forward_rounds_in_range. assumption. }
    rewrite round_involutive by assumption.
    apply IH. assumption.
Qed.

Lemma inverse_forward_rounds : forall n x,
  0 <= x < N -> forward_rounds n (inverse_rounds n x) = x.
Proof.
  intros n.
  induction n as [|n' IH]; intros x Hx.
  - simpl. reflexivity.
  - simpl.
    assert (Hrnd_range : 0 <= round_spec n' x < N).
    { apply round_in_range. assumption. }
    rewrite IH by assumption.
    apply round_involutive. assumption.
Qed.

Lemma forward_inverse_id : forall x,
  0 <= x < N -> inverse_spec (forward_spec x) = x.
Proof.
  intros x Hx.
  unfold forward_spec, inverse_spec.
  apply forward_inverse_rounds. assumption.
Qed.

Lemma inverse_forward_id : forall x,
  0 <= x < N -> forward_spec (inverse_spec x) = x.
Proof.
  intros x Hx.
  unfold forward_spec, inverse_spec.
  apply inverse_forward_rounds. assumption.
Qed.

Lemma forward_in_range : forall x,
  0 <= x < N -> 0 <= forward_spec x < N.
Proof.
  intros x Hx.
  unfold forward_spec.
  apply forward_rounds_in_range. assumption.
Qed.

Lemma inverse_in_range : forall x,
  0 <= x < N -> 0 <= inverse_spec x < N.
Proof.
  intros x Hx.
  unfold inverse_spec.
  apply inverse_rounds_in_range. assumption.
Qed.
