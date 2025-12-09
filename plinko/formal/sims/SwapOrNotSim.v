(** SwapOrNotSim.v - Simulation relations for SwapOrNot PRP

    Connects the Rust SwapOrNot implementation (plinko/src/iprf.rs)
    to the Rocq specification (specs/SwapOrNotSpec.v).
    
    Reference: Morris-Rogaway 2013 "How to Encipher Messages on a Small Domain"
    
    CRYPTO TRUST BASE:
    This module axiomatizes AES-128 operations. The two key axioms are:
    - [round_key_refinement]: Rust AES-based key derivation = abstract round_key
    - [prf_bit_refinement]: Rust AES-based PRF bit = abstract round_bit
    
    These axioms form our root assumptions about the crypto layer. All PRP
    properties (bijection, inversion, etc.) are proved in SwapOrNotProofs.v
    using only abstract round_key/round_bit, NOT AES internals.
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.

Require Import Plinko.Specs.CommonTypes.
Require Import Plinko.Specs.SwapOrNotSpec.
Require Import Plinko.Sims.SimTypes.

Import ListNotations.
Open Scope Z_scope.

(** ============================================================================
    Section 1: Rust SwapOrNot Struct State Representation
    ============================================================================ *)

(** SwapOrNotState is imported from SimTypes.v:
    Record SwapOrNotState := mkSwapOrNotState {
      son_domain : Z;
      son_num_rounds : nat;
      son_key : list Z;  (* 16 bytes of AES-128 key *)
    }.
*)

(** State refinement: Rust state refines spec parameters.
    Uses swapornot_state_valid from SimTypes.v as the canonical validity predicate,
    plus constraints binding to spec parameters N and num_rounds. *)
Definition refines_swap_or_not_state (rust_state : SwapOrNotState) : Prop :=
  swapornot_state_valid rust_state /\
  son_domain rust_state = N /\
  son_num_rounds rust_state = num_rounds.

(** ============================================================================
    Section 2: Crypto Primitive Axioms (AES-128)
    ============================================================================ *)

(** We axiomatize the crypto primitives since we cannot verify AES correctness
    within Rocq. These axioms capture the functional behavior. *)

(** AES-128 block encryption: 16-byte key x 16-byte block -> 16-byte output *)
Axiom aes128_encrypt : list Z -> list Z -> list Z.

(** AES produces 16-byte output from 16-byte input *)
Axiom aes128_encrypt_length : forall key block,
  length key = 16%nat ->
  length block = 16%nat ->
  length (aes128_encrypt key block) = 16%nat.

(** AES output bytes are in range [0, 256) *)
Axiom aes128_encrypt_bytes_valid : forall key block,
  length key = 16%nat ->
  length block = 16%nat ->
  Forall (fun b => 0 <= b < 256) (aes128_encrypt key block).

(** ============================================================================
    Section 3: Round Key Derivation Refinement
    ============================================================================ *)

(** Build 16-byte input block for round key derivation:
    bytes 0-7: round (big-endian u64)
    bytes 8-15: domain (big-endian u64) *)
Definition build_round_key_input (round : nat) (domain : Z) : list Z :=
  let r_bytes := [
    Z.shiftr (Z.of_nat round) 56 mod 256;
    Z.shiftr (Z.of_nat round) 48 mod 256;
    Z.shiftr (Z.of_nat round) 40 mod 256;
    Z.shiftr (Z.of_nat round) 32 mod 256;
    Z.shiftr (Z.of_nat round) 24 mod 256;
    Z.shiftr (Z.of_nat round) 16 mod 256;
    Z.shiftr (Z.of_nat round) 8 mod 256;
    Z.of_nat round mod 256
  ] in
  let d_bytes := [
    Z.shiftr domain 56 mod 256;
    Z.shiftr domain 48 mod 256;
    Z.shiftr domain 40 mod 256;
    Z.shiftr domain 32 mod 256;
    Z.shiftr domain 24 mod 256;
    Z.shiftr domain 16 mod 256;
    Z.shiftr domain 8 mod 256;
    domain mod 256
  ] in
  r_bytes ++ d_bytes.

(** Extract u64 from first 8 bytes (big-endian) *)
Definition bytes_to_u64 (bs : list Z) : Z :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: _ =>
      Z.shiftl b0 56 + Z.shiftl b1 48 + Z.shiftl b2 40 + Z.shiftl b3 32 +
      Z.shiftl b4 24 + Z.shiftl b5 16 + Z.shiftl b6 8 + b7
  | _ => 0
  end.

(** Rust derive_round_key function specification *)
Definition rust_derive_round_key (s : SwapOrNotState) (round : nat) : Z :=
  let input := build_round_key_input round (son_domain s) in
  let output := aes128_encrypt (son_key s) input in
  (bytes_to_u64 output) mod (son_domain s).

(** Round key is in domain range *)
Lemma rust_derive_round_key_in_range : forall s r,
  swapornot_state_valid s ->
  0 <= rust_derive_round_key s r < son_domain s.
Proof.
  intros s r [Hdom_pos [Hrounds [Hkey_len Hkey_valid]]].
  unfold rust_derive_round_key.
  apply Z.mod_pos_bound. lia.
Qed.

(** Axiom: Rust derive_round_key refines spec round_key
    
    This axiom links the AES-based key derivation to the abstract spec.
    It states that for a valid state, the Rust implementation produces
    the same round keys as the spec (modeled as a parameter). *)
Axiom round_key_refinement : forall s r,
  refines_swap_or_not_state s ->
  rust_derive_round_key s r = round_key r.

(** ============================================================================
    Section 4: PRF Bit Computation Refinement
    ============================================================================ *)

(** Build 16-byte input block for PRF bit:
    bytes 0-7: (round | 0x8000000000000000) (big-endian u64)
    bytes 8-15: canonical (big-endian u64) *)
Definition build_prf_bit_input (round : nat) (canonical : Z) : list Z :=
  let r_with_flag := Z.lor (Z.of_nat round) (Z.shiftl 1 63) in
  let r_bytes := [
    Z.shiftr r_with_flag 56 mod 256;
    Z.shiftr r_with_flag 48 mod 256;
    Z.shiftr r_with_flag 40 mod 256;
    Z.shiftr r_with_flag 32 mod 256;
    Z.shiftr r_with_flag 24 mod 256;
    Z.shiftr r_with_flag 16 mod 256;
    Z.shiftr r_with_flag 8 mod 256;
    r_with_flag mod 256
  ] in
  let c_bytes := [
    Z.shiftr canonical 56 mod 256;
    Z.shiftr canonical 48 mod 256;
    Z.shiftr canonical 40 mod 256;
    Z.shiftr canonical 32 mod 256;
    Z.shiftr canonical 24 mod 256;
    Z.shiftr canonical 16 mod 256;
    Z.shiftr canonical 8 mod 256;
    canonical mod 256
  ] in
  r_bytes ++ c_bytes.

(** Extract LSB from first output byte *)
Definition extract_lsb (bs : list Z) : bool :=
  match bs with
  | b0 :: _ => Z.odd b0
  | _ => false
  end.

(** Rust prf_bit function specification *)
Definition rust_prf_bit (s : SwapOrNotState) (round : nat) (canonical : Z) : bool :=
  let input := build_prf_bit_input round canonical in
  let output := aes128_encrypt (son_key s) input in
  extract_lsb output.

(** Axiom: Rust prf_bit refines spec round_bit
    
    This axiom links the AES-based PRF bit to the abstract spec. *)
Axiom prf_bit_refinement : forall s r c,
  refines_swap_or_not_state s ->
  0 <= c < N ->
  rust_prf_bit s r c = round_bit r c.

(** ============================================================================
    Section 5: Single Round Operation Refinement
    ============================================================================ *)

(** Rust partner computation (matches SwapOrNotSpec.partner) *)
Definition rust_partner (domain k_i x : Z) : Z :=
  (k_i + domain - (x mod domain)) mod domain.

(** Partner computation is equivalent to spec *)
Lemma rust_partner_equiv : forall s k_i x,
  swapornot_state_valid s ->
  son_domain s = N ->
  rust_partner (son_domain s) k_i x = partner k_i x.
Proof.
  intros s k_i x Hvalid Hdomain.
  unfold rust_partner, partner.
  rewrite Hdomain. reflexivity.
Qed.

(** Rust canonical computation (matches SwapOrNotSpec.canonical) *)
Definition rust_canonical (x x' : Z) : Z := Z.max x x'.

(** Rust single round specification *)
Definition rust_round (s : SwapOrNotState) (r : nat) (x : Z) : Z :=
  let k_i := rust_derive_round_key s r in
  let x' := rust_partner (son_domain s) k_i x in
  let c := rust_canonical x x' in
  if rust_prf_bit s r c then x' else x.

(** Single round refinement theorem *)
Theorem rust_round_refines_spec : forall s r x,
  refines_swap_or_not_state s ->
  0 <= x < N ->
  rust_round s r x = round_spec r x.
Proof.
  intros s r x Hrefines Hx.
  destruct Hrefines as [Hvalid [Hdomain Hnrounds]].
  unfold rust_round, round_spec.
  rewrite round_key_refinement by (split; [assumption | split; assumption]).
  rewrite Hdomain.
  unfold rust_partner, partner.
  unfold rust_canonical, canonical.
  set (p := (round_key r + N - x mod N) mod N).
  assert (Hp_range : 0 <= p < N).
  { unfold p. apply Z.mod_pos_bound. pose proof N_pos. lia. }
  assert (Hmax_range : 0 <= Z.max x p < N).
  { lia. }
  rewrite prf_bit_refinement.
  - reflexivity.
  - split; [assumption | split; assumption].
  - exact Hmax_range.
Qed.

(** ============================================================================
    Section 6: Forward Permutation Refinement
    ============================================================================ *)

(** Rust forward permutation: apply rounds 0..num_rounds-1 *)
Fixpoint rust_forward_rounds (s : SwapOrNotState) (n : nat) (x : Z) : Z :=
  match n with
  | O => x
  | S n' => rust_round s n' (rust_forward_rounds s n' x)
  end.

Definition rust_forward (s : SwapOrNotState) (x : Z) : Z :=
  rust_forward_rounds s (son_num_rounds s) x.

(** Forward rounds refinement *)
Lemma rust_forward_rounds_refines : forall s n x,
  refines_swap_or_not_state s ->
  0 <= x < N ->
  rust_forward_rounds s n x = forward_rounds n x.
Proof.
  intros s n.
  induction n as [|n' IH]; intros x Hrefines Hx.
  - simpl. reflexivity.
  - simpl.
    rewrite IH by assumption.
    apply rust_round_refines_spec; try assumption.
    apply forward_rounds_in_range. assumption.
Qed.

(** Main forward simulation theorem *)
Theorem rust_forward_refines_spec : forall s x,
  refines_swap_or_not_state s ->
  0 <= x < N ->
  rust_forward s x = forward_spec x.
Proof.
  intros s x Hrefines Hx.
  unfold rust_forward, forward_spec.
  destruct Hrefines as [Hvalid [Hdomain Hnrounds]].
  rewrite Hnrounds.
  apply rust_forward_rounds_refines.
  - split; [assumption | split; assumption].
  - assumption.
Qed.

(** ============================================================================
    Section 7: Inverse Permutation Refinement
    ============================================================================ *)

(** Rust inverse permutation: apply rounds num_rounds-1..0 *)
Fixpoint rust_inverse_rounds (s : SwapOrNotState) (n : nat) (x : Z) : Z :=
  match n with
  | O => x
  | S n' => rust_inverse_rounds s n' (rust_round s n' x)
  end.

Definition rust_inverse (s : SwapOrNotState) (x : Z) : Z :=
  rust_inverse_rounds s (son_num_rounds s) x.

(** Inverse rounds refinement *)
Lemma rust_inverse_rounds_refines : forall s n x,
  refines_swap_or_not_state s ->
  0 <= x < N ->
  rust_inverse_rounds s n x = inverse_rounds n x.
Proof.
  intros s n.
  induction n as [|n' IH]; intros x Hrefines Hx.
  - simpl. reflexivity.
  - simpl.
    rewrite rust_round_refines_spec by assumption.
    apply IH; try assumption.
    apply round_in_range. assumption.
Qed.

(** Main inverse simulation theorem *)
Theorem rust_inverse_refines_spec : forall s x,
  refines_swap_or_not_state s ->
  0 <= x < N ->
  rust_inverse s x = inverse_spec x.
Proof.
  intros s x Hrefines Hx.
  unfold rust_inverse, inverse_spec.
  destruct Hrefines as [Hvalid [Hdomain Hnrounds]].
  rewrite Hnrounds.
  apply rust_inverse_rounds_refines.
  - split; [assumption | split; assumption].
  - assumption.
Qed.

(** ============================================================================
    Section 8: Lifted Properties (From Spec to Rust Implementation)
    ============================================================================ *)

(** These theorems lift the verified properties from SwapOrNotProofs.v
    to the Rust implementation via the simulation relation. *)

(** Rust forward preserves range *)
Theorem rust_forward_in_range : forall s x,
  refines_swap_or_not_state s ->
  0 <= x < N ->
  0 <= rust_forward s x < N.
Proof.
  intros s x Hrefines Hx.
  rewrite rust_forward_refines_spec by assumption.
  apply forward_in_range. assumption.
Qed.

(** Rust inverse preserves range *)
Theorem rust_inverse_in_range : forall s x,
  refines_swap_or_not_state s ->
  0 <= x < N ->
  0 <= rust_inverse s x < N.
Proof.
  intros s x Hrefines Hx.
  rewrite rust_inverse_refines_spec by assumption.
  apply inverse_in_range. assumption.
Qed.

(** Rust forward/inverse identity *)
Theorem rust_forward_inverse_id : forall s x,
  refines_swap_or_not_state s ->
  0 <= x < N ->
  rust_inverse s (rust_forward s x) = x.
Proof.
  intros s x Hrefines Hx.
  rewrite rust_forward_refines_spec by assumption.
  rewrite rust_inverse_refines_spec.
  - apply forward_inverse_id. assumption.
  - assumption.
  - apply forward_in_range. assumption.
Qed.

(** Rust inverse/forward identity *)
Theorem rust_inverse_forward_id : forall s x,
  refines_swap_or_not_state s ->
  0 <= x < N ->
  rust_forward s (rust_inverse s x) = x.
Proof.
  intros s x Hrefines Hx.
  rewrite rust_inverse_refines_spec by assumption.
  rewrite rust_forward_refines_spec.
  - apply inverse_forward_id. assumption.
  - assumption.
  - apply inverse_in_range. assumption.
Qed.

(** Rust forward is injective *)
Theorem rust_forward_injective : forall s x1 x2,
  refines_swap_or_not_state s ->
  0 <= x1 < N -> 0 <= x2 < N ->
  rust_forward s x1 = rust_forward s x2 ->
  x1 = x2.
Proof.
  intros s x1 x2 Hrefines Hx1 Hx2 Heq.
  rewrite rust_forward_refines_spec in Heq by assumption.
  rewrite rust_forward_refines_spec in Heq by assumption.
  assert (H1 : inverse_spec (forward_spec x1) = x1).
  { apply forward_inverse_id. assumption. }
  assert (H2 : inverse_spec (forward_spec x2) = x2).
  { apply forward_inverse_id. assumption. }
  rewrite Heq in H1. congruence.
Qed.

(** Rust forward is surjective *)
Theorem rust_forward_surjective : forall s y,
  refines_swap_or_not_state s ->
  0 <= y < N ->
  exists x, 0 <= x < N /\ rust_forward s x = y.
Proof.
  intros s y Hrefines Hy.
  exists (rust_inverse s y).
  split.
  - apply rust_inverse_in_range; assumption.
  - apply rust_inverse_forward_id; assumption.
Qed.

(** Rust forward is a bijection *)
Theorem rust_forward_is_bijection : forall s,
  refines_swap_or_not_state s ->
  (forall x1 x2, 0 <= x1 < N -> 0 <= x2 < N ->
    rust_forward s x1 = rust_forward s x2 -> x1 = x2) /\
  (forall y, 0 <= y < N -> 
    exists x, 0 <= x < N /\ rust_forward s x = y).
Proof.
  intros s Hrefines.
  split.
  - intros x1 x2 Hx1 Hx2. apply rust_forward_injective; assumption.
  - intros y Hy. apply rust_forward_surjective; assumption.
Qed.
