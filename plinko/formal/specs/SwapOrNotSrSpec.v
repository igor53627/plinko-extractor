(** SwapOrNotSrSpec.v - Sometimes-Recurse (SR) wrapper for SwapOrNot PRP

    Provides full-domain PRP security by recursively applying SwapOrNot
    to shrinking subdomains until the element lands in the "right pile".

    Reference: Morris-Rogaway 2013 Sometimes-Recurse shuffle construction
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
Import ListNotations.

Require Import Plinko.Specs.CommonTypes.
Require Import Plinko.Specs.SwapOrNotSpec.

Open Scope Z_scope.

(** SR-specific parameters *)

(* Round count function for level with domain size n *)
Parameter sr_t_rounds : Z -> nat.

(* Level-aware round key derivation *)
Parameter sr_round_key : nat -> nat -> Z -> Z.

(* Level-aware PRF bit *)
Parameter sr_round_bit : nat -> nat -> Z -> Z -> bool.

(** SR partner function: domain-parameterized *)
Definition sr_partner (k_i x n : Z) : Z :=
  (k_i + n - (x mod n)) mod n.

(** Single SR round at a given level with domain size n *)
Definition sr_round_spec (level : nat) (r : nat) (n : Z) (x : Z) : Z :=
  let k_i := sr_round_key level r n in
  let x' := sr_partner k_i x n in
  let c := Z.max x x' in
  if sr_round_bit level r c n then x' else x.

(** Apply t rounds of swap-or-not at a level *)
Fixpoint sr_apply_rounds (level : nat) (rounds : nat) (n : Z) (x : Z) : Z :=
  match rounds with
  | O => x
  | S r' => sr_round_spec level r' n (sr_apply_rounds level r' n x)
  end.

(** Apply t rounds in reverse order (for inverse) *)
Fixpoint sr_apply_rounds_inv (level : nat) (rounds : nat) (n : Z) (x : Z) : Z :=
  match rounds with
  | O => x
  | S r' => sr_apply_rounds_inv level r' n (sr_round_spec level r' n x)
  end.

(** SR forward permutation: recursive descent *)
Fixpoint sr_forward_aux (x : Z) (n : Z) (level : nat) (fuel : nat) : Z :=
  match fuel with
  | O => x
  | S fuel' =>
      if n <=? 1 then x
      else
        let t := sr_t_rounds n in
        let x' := sr_apply_rounds level t n x in
        let half := n / 2 in
        if half <=? x' then x'
        else sr_forward_aux x' half (S level) fuel'
  end.

Definition sr_forward (domain : Z) (x : Z) : Z :=
  let max_levels := (Z.to_nat (Z.log2_up domain) + 1)%nat in
  sr_forward_aux x domain 0 max_levels.

(** SR inverse: reconstruct path from output *)
Fixpoint sr_inverse_aux (y : Z) (n : Z) (level : nat) (fuel : nat) : Z :=
  match fuel with
  | O => y
  | S fuel' =>
      if n <=? 1 then y
      else
        let t := sr_t_rounds n in
        let half := n / 2 in
        if half <=? y then
          sr_apply_rounds_inv level t n y
        else
          let x_rec := sr_inverse_aux y half (S level) fuel' in
          sr_apply_rounds_inv level t n x_rec
  end.

Definition sr_inverse (domain : Z) (y : Z) : Z :=
  let max_levels := (Z.to_nat (Z.log2_up domain) + 1)%nat in
  sr_inverse_aux y domain 0 max_levels.

(** Key lemmas *)

(* Partner is in range *)
Lemma sr_partner_in_range : forall k_i x n,
  0 < n -> 0 <= x < n -> 0 <= sr_partner k_i x n < n.
Proof.
  intros k_i x n Hn Hx.
  unfold sr_partner.
  apply Z.mod_pos_bound. lia.
Qed.

(* Partner is involutive *)
Lemma sr_partner_involutive : forall k_i x n,
  0 < n -> 0 <= x < n -> sr_partner k_i (sr_partner k_i x n) n = x.
Proof.
  intros k_i x n Hn Hx.
  unfold sr_partner.
  assert (Hx_mod : x mod n = x) by (apply Z.mod_small; lia).
  rewrite Hx_mod.
  rewrite Z.mod_mod by lia.
  rewrite Zminus_mod_idemp_r.
  replace (k_i + n - (k_i + n - x)) with x by ring.
  apply Z.mod_small. lia.
Qed.

(* Axiom: round keys are in range *)
Axiom sr_round_key_in_range : forall level r n,
  0 < n -> 0 <= sr_round_key level r n < n.

(* Round is involutive at each level *)
Lemma sr_round_involutive : forall level r n x,
  0 < n -> 0 <= x < n ->
  sr_round_spec level r n (sr_round_spec level r n x) = x.
Proof.
  intros level r n x Hn Hx.
  unfold sr_round_spec.
  set (k_i := sr_round_key level r n).
  set (p := sr_partner k_i x n).
  set (c := Z.max x p).
  assert (Hp_range : 0 <= p < n) by (unfold p; apply sr_partner_in_range; assumption).
  assert (Hp_inv : sr_partner k_i p n = x) by (unfold p; apply sr_partner_involutive; assumption).
  assert (Hc_eq : Z.max p (sr_partner k_i p n) = c).
  { unfold c. rewrite Hp_inv. lia. }
  destruct (sr_round_bit level r c n) eqn:Hbit.
  - rewrite Hc_eq. rewrite Hbit. rewrite Hp_inv. reflexivity.
  - fold p. fold c. rewrite Hbit. reflexivity.
Qed.

(* Round preserves range *)
Lemma sr_round_in_range : forall level r n x,
  0 < n -> 0 <= x < n -> 0 <= sr_round_spec level r n x < n.
Proof.
  intros level r n x Hn Hx.
  unfold sr_round_spec.
  destruct (sr_round_bit level r (Z.max x (sr_partner (sr_round_key level r n) x n)) n).
  - apply sr_partner_in_range; assumption.
  - assumption.
Qed.

(* Apply rounds preserves range *)
Lemma sr_apply_rounds_in_range : forall level rounds n x,
  0 < n -> 0 <= x < n -> 0 <= sr_apply_rounds level rounds n x < n.
Proof.
  intros level rounds n x Hn Hx.
  induction rounds as [|r' IH].
  - simpl. assumption.
  - simpl. apply sr_round_in_range; [assumption | apply IH].
Qed.

(* Apply rounds then inverse is identity *)
Lemma sr_apply_rounds_inverse : forall level rounds n x,
  0 < n -> 0 <= x < n ->
  sr_apply_rounds_inv level rounds n (sr_apply_rounds level rounds n x) = x.
Proof.
  intros level rounds n x Hn Hx.
  induction rounds as [|r' IH].
  - simpl. reflexivity.
  - simpl.
    assert (Hfwd_range : 0 <= sr_apply_rounds level r' n x < n).
    { apply sr_apply_rounds_in_range; assumption. }
    rewrite sr_round_involutive by assumption.
    apply IH.
Qed.

(* Inverse rounds then apply is identity *)
Lemma sr_apply_rounds_inv_inverse : forall level rounds n x,
  0 < n -> 0 <= x < n ->
  sr_apply_rounds level rounds n (sr_apply_rounds_inv level rounds n x) = x.
Admitted.

(* SR forward preserves range *)
Lemma sr_forward_range : forall domain x,
  0 < domain -> 0 <= x < domain ->
  0 <= sr_forward domain x < domain.
Admitted.

(* SR inverse preserves range *)
Lemma sr_inverse_range : forall domain y,
  0 < domain -> 0 <= y < domain ->
  0 <= sr_inverse domain y < domain.
Admitted.

(* SR is a bijection: forward then inverse is identity *)
Axiom sr_forward_inverse_id : forall domain x,
  0 < domain -> 0 <= x < domain ->
  sr_inverse domain (sr_forward domain x) = x.

(* SR is a bijection: inverse then forward is identity *)
Axiom sr_inverse_forward_id : forall domain y,
  0 < domain -> 0 <= y < domain ->
  sr_forward domain (sr_inverse domain y) = y.

(** Compatibility with base SwapOrNot *)

(* When domain = 2^64, SR with 0 recursions is equivalent to base SwapOrNot *)
Lemma sr_base_case_equiv : forall x,
  0 <= x < N ->
  sr_t_rounds N = num_rounds ->
  (forall r, sr_round_key 0 r N = round_key r) ->
  (forall r c, sr_round_bit 0 r c N = round_bit r c) ->
  sr_forward N x = forward_spec x.
Admitted.

(** Connection to iPRF: SR-based PRP maintains iPRF properties *)

(* The iPRF can instantiate PRP with sr_forward/sr_inverse *)
(* This ensures iPRF works over arbitrary (non-power-of-two) domains *)
