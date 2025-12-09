(** CommonTypes.v - Common types and helpers for Plinko formal verification *)

From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

(** Type definitions *)

Definition Word := Z.

Definition Key128 := list Z.

(** Domain and range constraints *)

Definition valid_domain (n : Z) : Prop := n > 0.

Definition valid_range (m n : Z) : Prop := 1 <= m /\ m <= n.

(** Power of two predicates *)

Fixpoint is_power_of_two_nat (n : nat) : bool :=
  match n with
  | O => false
  | S O => true
  | S (S n' as m) => Nat.even m && is_power_of_two_nat n'
  end.

Definition is_power_of_two (n : Z) : Prop :=
  n > 0 /\ exists k : nat, n = Z.pow 2 (Z.of_nat k).

Lemma is_power_of_two_pos : forall n, is_power_of_two n -> n > 0.
Proof.
  intros n [Hpos _]. exact Hpos.
Qed.

(** Ceiling division *)

Definition ceil_div (a b : Z) : Z := (a + b - 1) / b.

(** Round up to multiple *)

Definition round_up_multiple (x m : Z) : Z := ((x + m - 1) / m) * m.

(** Finite domain type wrapper *)

Definition FinDomain (N : Z) := { x : Z | 0 <= x < N }.
