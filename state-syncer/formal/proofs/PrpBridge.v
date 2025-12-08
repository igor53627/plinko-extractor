(** PrpBridge.v - Bridge from abstract PRP axioms to concrete SwapOrNot

    This module bridges the abstract PRP interface used in IprfProofs.v
    to the concrete SwapOrNot implementation proven in SwapOrNotProofs.v.

    The iPRF module (IprfSpec.v/IprfProofs.v) uses abstract PRP parameters:
      - prp_forward : Z -> Z -> Z
      - prp_inverse : Z -> Z -> Z

    These are instantiated with SwapOrNot when the domain size n = N.

    The 4 abstract PRP axioms from IprfProofs.v:
      1. prp_forward_in_range : 0 <= x < n -> 0 <= prp_forward n x < n
      2. prp_inverse_in_range : 0 <= x < n -> 0 <= prp_inverse n x < n
      3. prp_forward_inverse  : 0 <= x < n -> prp_inverse n (prp_forward n x) = x
      4. prp_inverse_forward  : 0 <= x < n -> prp_forward n (prp_inverse n x) = x

    These are discharged by the corresponding theorems from SwapOrNotProofs.v:
      1. forward_in_range_full  : 0 <= x < N -> 0 <= forward_spec x < N
      2. inverse_in_range_full  : 0 <= x < N -> 0 <= inverse_spec x < N
      3. forward_inverse_id_full: 0 <= x < N -> inverse_spec (forward_spec x) = x
      4. inverse_forward_id_full: 0 <= x < N -> forward_spec (inverse_spec x) = x
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.

Require Import Plinko.Specs.SwapOrNotSpec.
Require Import Plinko.Proofs.SwapOrNotProofs.

Open Scope Z_scope.

(** ============================================================================
    Section 1: Concrete PRP Instantiation
    ============================================================================ *)

(** When the iPRF uses domain size n = N (the SwapOrNot domain size),
    the abstract PRP is instantiated as follows:

      prp_forward N x := forward_spec x
      prp_inverse N x := inverse_spec x

    This section defines the concrete instantiation and proves it
    satisfies the abstract PRP interface.
*)

Section ConcretePRP.

(** Concrete PRP forward: when n = N, use SwapOrNot forward_spec *)
Definition concrete_prp_forward (n x : Z) : Z :=
  if Z.eqb n N then forward_spec x else x.

(** Concrete PRP inverse: when n = N, use SwapOrNot inverse_spec *)
Definition concrete_prp_inverse (n x : Z) : Z :=
  if Z.eqb n N then inverse_spec x else x.

(** ============================================================================
    Section 2: Bridging Theorems
    ============================================================================ *)

(** These theorems show that the concrete instantiation satisfies
    the abstract PRP properties when operating on domain N. *)

(** Bridge theorem 1: forward maps [0,N) to [0,N) *)
Theorem concrete_prp_forward_in_range : forall x,
  0 <= x < N ->
  0 <= concrete_prp_forward N x < N.
Proof.
  intros x Hx.
  unfold concrete_prp_forward.
  assert (Heq : (N =? N)%Z = true) by (apply Z.eqb_eq; reflexivity).
  rewrite Heq.
  apply forward_in_range_full.
  exact Hx.
Qed.

(** Bridge theorem 2: inverse maps [0,N) to [0,N) *)
Theorem concrete_prp_inverse_in_range : forall x,
  0 <= x < N ->
  0 <= concrete_prp_inverse N x < N.
Proof.
  intros x Hx.
  unfold concrete_prp_inverse.
  assert (Heq : (N =? N)%Z = true) by (apply Z.eqb_eq; reflexivity).
  rewrite Heq.
  apply inverse_in_range_full.
  exact Hx.
Qed.

(** Bridge theorem 3: inverse(forward(x)) = x *)
Theorem concrete_prp_forward_inverse : forall x,
  0 <= x < N ->
  concrete_prp_inverse N (concrete_prp_forward N x) = x.
Proof.
  intros x Hx.
  unfold concrete_prp_forward, concrete_prp_inverse.
  assert (Heq : (N =? N)%Z = true) by (apply Z.eqb_eq; reflexivity).
  rewrite Heq.
  apply forward_inverse_id_full.
  exact Hx.
Qed.

(** Bridge theorem 4: forward(inverse(x)) = x *)
Theorem concrete_prp_inverse_forward : forall x,
  0 <= x < N ->
  concrete_prp_forward N (concrete_prp_inverse N x) = x.
Proof.
  intros x Hx.
  unfold concrete_prp_forward, concrete_prp_inverse.
  assert (Heq : (N =? N)%Z = true) by (apply Z.eqb_eq; reflexivity).
  rewrite Heq.
  apply inverse_forward_id_full.
  exact Hx.
Qed.

End ConcretePRP.

(** ============================================================================
    Section 3: Direct Bridging for Fixed Domain N
    ============================================================================ *)

(** When the iPRF is instantiated with domain size = N (the SwapOrNot
    domain), we can directly use forward_spec and inverse_spec.
    These theorems provide the bridge without the conditional wrapper. *)

Section DirectBridge.

(** Direct bridge 1: forward_spec maps [0,N) to [0,N) *)
Theorem prp_forward_in_range_N : forall x,
  0 <= x < N ->
  0 <= forward_spec x < N.
Proof.
  exact forward_in_range_full.
Qed.

(** Direct bridge 2: inverse_spec maps [0,N) to [0,N) *)
Theorem prp_inverse_in_range_N : forall x,
  0 <= x < N ->
  0 <= inverse_spec x < N.
Proof.
  exact inverse_in_range_full.
Qed.

(** Direct bridge 3: inverse_spec(forward_spec(x)) = x *)
Theorem prp_forward_inverse_N : forall x,
  0 <= x < N ->
  inverse_spec (forward_spec x) = x.
Proof.
  exact forward_inverse_id_full.
Qed.

(** Direct bridge 4: forward_spec(inverse_spec(x)) = x *)
Theorem prp_inverse_forward_N : forall x,
  0 <= x < N ->
  forward_spec (inverse_spec x) = x.
Proof.
  exact inverse_forward_id_full.
Qed.

(** Bijection properties follow from the forward/inverse identities *)
Theorem prp_forward_bijection_N :
  (forall x1 x2, 0 <= x1 < N -> 0 <= x2 < N ->
    forward_spec x1 = forward_spec x2 -> x1 = x2) /\
  (forall y, 0 <= y < N ->
    exists x, 0 <= x < N /\ forward_spec x = y).
Proof.
  exact forward_is_bijection.
Qed.

End DirectBridge.

Close Scope Z_scope.
