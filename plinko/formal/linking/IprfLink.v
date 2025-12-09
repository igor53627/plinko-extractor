(** * IprfLink.v - Links rocq-of-rust translated Iprf to simulation layer
    
    This module provides the refinement bridge between:
    - Translated Rust code (src/iprf.v) from rocq-of-rust
    - Simulation specifications (sims/IprfSim.v)
    
    The linking approach:
    1. Define placeholder parameters for Rust functions (until RocqOfRust compiled)
    2. State refinement axioms connecting Rust to spec
    3. Derive properties from refinement + spec lemmas
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.

Require Import Plinko.Specs.IprfSpec.
Require Import Plinko.Sims.SimTypes.
Require Import Plinko.Sims.IprfSim.

(* Note: Full linking requires RocqOfRust library *)
(* When available, uncomment:
   Require Import src.iprf.
*)

Import ListNotations.
Open Scope Z_scope.

(** ============================================================================
    Placeholder Parameters for Rust Functions
    ============================================================================ *)

(** These parameters represent the translated Rust functions.
    When rocq-of-rust translation is compiled, replace with actual imports. *)

(** Refinement: Rust SwapOrNot::forward refines forward_spec *)
(* When rocq-of-rust library is available, this becomes:
   
   Definition rust_swap_or_not_forward_refines :
     forall st x,
       swapornot_state_valid st ->
       0 <= x < son_domain st ->
       iprf.SwapOrNot.forward st x = forward_spec x.
*)

(** Placeholder until RocqOfRust library is compiled *)
Parameter rust_swap_or_not_forward : SwapOrNotState -> Z -> Z.
Parameter rust_swap_or_not_inverse : SwapOrNotState -> Z -> Z.
Parameter rust_iprf_forward : IprfState -> Z -> Z.
Parameter rust_iprf_inverse : IprfState -> Z -> list Z.

(** ============================================================================
    Refinement Axioms
    ============================================================================ *)

(** These axioms state that the Rust implementations refine the specifications.
    They become theorems when rocq-of-rust translation is proven correct. *)

Section RefinementAxioms.

(** *** SwapOrNot Refinement *)

(** Rust SwapOrNot::forward refines prp_forward *)
Axiom rust_swap_or_not_forward_refines : forall st x,
  swapornot_state_valid st ->
  0 <= x < son_domain st ->
  rust_swap_or_not_forward st x = prp_forward (son_domain st) x.

(** Rust SwapOrNot::inverse refines prp_inverse *)
Axiom rust_swap_or_not_inverse_refines : forall st y,
  swapornot_state_valid st ->
  0 <= y < son_domain st ->
  rust_swap_or_not_inverse st y = prp_inverse (son_domain st) y.

(** *** Iprf Refinement *)

(** Rust Iprf::forward refines iprf_forward_spec *)
Axiom rust_iprf_forward_refines : forall st x,
  iprf_state_valid st ->
  0 <= x < iprf_domain st ->
  rust_iprf_forward st x = iprf_forward_spec x (iprf_domain st) (iprf_range st).

(** Rust Iprf::inverse refines iprf_inverse_spec *)
Axiom rust_iprf_inverse_refines : forall st y,
  iprf_state_valid st ->
  0 <= y < iprf_range st ->
  rust_iprf_inverse st y = iprf_inverse_spec y (iprf_domain st) (iprf_range st).

End RefinementAxioms.

(** ============================================================================
    Derived Properties from Refinement
    ============================================================================ *)

(** These theorems show that Rust implementations inherit spec properties
    via the refinement axioms. *)

Section DerivedProperties.

(** *** SwapOrNot Derived Properties *)

(** Rust SwapOrNot::forward output is in range *)
Theorem rust_swap_or_not_forward_in_range : forall st x,
  swapornot_state_valid st ->
  0 <= x < son_domain st ->
  0 <= rust_swap_or_not_forward st x < son_domain st.
Proof.
  intros st x Hvalid Hx.
  rewrite rust_swap_or_not_forward_refines; try assumption.
  apply prp_forward_in_range; assumption.
Qed.

(** Rust SwapOrNot::inverse output is in range *)
Theorem rust_swap_or_not_inverse_in_range : forall st y,
  swapornot_state_valid st ->
  0 <= y < son_domain st ->
  0 <= rust_swap_or_not_inverse st y < son_domain st.
Proof.
  intros st y Hvalid Hy.
  rewrite rust_swap_or_not_inverse_refines; try assumption.
  apply prp_inverse_in_range; assumption.
Qed.

(** Rust SwapOrNot roundtrip: inverse(forward(x)) = x *)
Theorem rust_swap_or_not_roundtrip : forall st x,
  swapornot_state_valid st ->
  0 <= x < son_domain st ->
  rust_swap_or_not_inverse st (rust_swap_or_not_forward st x) = x.
Proof.
  intros st x Hvalid Hx.
  rewrite rust_swap_or_not_forward_refines; try assumption.
  assert (Hfwd_range : 0 <= prp_forward (son_domain st) x < son_domain st).
  { apply prp_forward_in_range; assumption. }
  rewrite rust_swap_or_not_inverse_refines; try assumption.
  apply prp_forward_inverse; assumption.
Qed.

(** *** Iprf Derived Properties *)

(** Rust Iprf::forward output is in range *)
Theorem rust_iprf_forward_in_range : forall st x,
  iprf_state_valid st ->
  0 <= x < iprf_domain st ->
  0 <= rust_iprf_forward st x < iprf_range st.
Proof.
  intros st x Hvalid Hx.
  rewrite rust_iprf_forward_refines; try assumption.
  apply iprf_forward_in_range.
  - exact Hx.
  - destruct Hvalid as [? [? [? ?]]]; lia.
  - destruct Hvalid as [? [? [? ?]]]; lia.
Qed.

(** Rust Iprf::inverse elements are in domain *)
Theorem rust_iprf_inverse_in_domain : forall st y x,
  iprf_state_valid st ->
  0 <= y < iprf_range st ->
  In x (rust_iprf_inverse st y) ->
  0 <= x < iprf_domain st.
Proof.
  intros st y x Hvalid Hy Hin.
  rewrite rust_iprf_inverse_refines in Hin; try assumption.
  apply iprf_inverse_elements_in_domain with (y := y) (m := iprf_range st).
  - exact Hy.
  - destruct Hvalid as [? [? [? ?]]]; lia.
  - destruct Hvalid as [? [? [? ?]]]; lia.
  - exact Hin.
Qed.

(** Rust Iprf::inverse contains preimage *)
Theorem rust_iprf_inverse_contains_preimage : forall st x,
  iprf_state_valid st ->
  0 <= x < iprf_domain st ->
  In x (rust_iprf_inverse st (rust_iprf_forward st x)).
Proof.
  intros st x Hvalid Hx.
  rewrite rust_iprf_forward_refines; try assumption.
  assert (Hfwd_range : 0 <= iprf_forward_spec x (iprf_domain st) (iprf_range st) < iprf_range st).
  { apply iprf_forward_in_range.
    - exact Hx.
    - destruct Hvalid as [? [? [? ?]]]; lia.
    - destruct Hvalid as [? [? [? ?]]]; lia. }
  rewrite rust_iprf_inverse_refines; try assumption.
  apply iprf_inverse_contains_preimage.
  - exact Hx.
  - destruct Hvalid as [? [? [? ?]]]; lia.
  - destruct Hvalid as [? [? [? ?]]]; lia.
  - reflexivity.
Qed.

(** Rust Iprf::inverse elements map back to y *)
Theorem rust_iprf_inverse_consistent : forall st y x,
  iprf_state_valid st ->
  0 <= y < iprf_range st ->
  In x (rust_iprf_inverse st y) ->
  rust_iprf_forward st x = y.
Proof.
  intros st y x Hvalid Hy Hin.
  rewrite rust_iprf_inverse_refines in Hin; try assumption.
  assert (Hx_range : 0 <= x < iprf_domain st).
  { apply iprf_inverse_elements_in_domain with (y := y) (m := iprf_range st).
    - exact Hy.
    - destruct Hvalid as [? [? [? ?]]]; lia.
    - destruct Hvalid as [? [? [? ?]]]; lia.
    - exact Hin. }
  rewrite rust_iprf_forward_refines; try assumption.
  apply iprf_inverse_elements_map_to_y with (y := y).
  - exact Hy.
  - destruct Hvalid as [? [? [? ?]]]; lia.
  - destruct Hvalid as [? [? [? ?]]]; lia.
  - exact Hin.
Qed.

(** Rust Iprf inverses partition the domain *)
Theorem rust_iprf_partition : forall st,
  iprf_state_valid st ->
  forall x, 0 <= x < iprf_domain st ->
    exists! y, 0 <= y < iprf_range st /\ In x (rust_iprf_inverse st y).
Proof.
  intros st Hvalid x Hx.
  set (y := rust_iprf_forward st x).
  exists y.
  split.
  - split.
    + apply rust_iprf_forward_in_range; assumption.
    + apply rust_iprf_inverse_contains_preimage; assumption.
  - intros y' [Hy'_range Hy'_in].
    assert (Hfwd : rust_iprf_forward st x = y').
    { apply rust_iprf_inverse_consistent with (y := y'); assumption. }
    unfold y. exact Hfwd.
Qed.

End DerivedProperties.

(** ============================================================================
    State Construction Helpers
    ============================================================================ *)

Section StateConstruction.

(** Build a valid SwapOrNotState from parameters *)
Definition make_swapornot_state (domain : Z) (num_rounds : nat) (key : list Z) : SwapOrNotState :=
  mkSwapOrNotState domain num_rounds key.

(** Build a valid IprfState from parameters *)
Definition make_iprf_state (n m : Z) (depth : nat) : IprfState :=
  mkIprfState n m depth.

(** Validity check for SwapOrNotState construction *)
Lemma make_swapornot_valid : forall domain num_rounds key,
  domain > 0 ->
  (num_rounds >= 6)%nat ->
  length key = 16%nat ->
  Forall (fun b => 0 <= b < 256) key ->
  swapornot_state_valid (make_swapornot_state domain num_rounds key).
Proof.
  intros domain num_rounds key Hdom Hrounds Hlen Hkey.
  unfold swapornot_state_valid, make_swapornot_state. simpl.
  repeat split; assumption.
Qed.

(** Validity check for IprfState construction *)
Lemma make_iprf_valid : forall n m depth,
  n > 0 ->
  m > 0 ->
  m <= n ->
  (Z.of_nat depth >= Z.log2_up m) ->
  iprf_state_valid (make_iprf_state n m depth).
Proof.
  intros n m depth Hn Hm Hmn Hdepth.
  unfold iprf_state_valid, make_iprf_state. simpl.
  repeat split; assumption.
Qed.

End StateConstruction.

Close Scope Z_scope.

(* 
   LINKING LAYER SUMMARY
   
   This module provides:

   1. Placeholder parameters for Rust functions
      Replace with actual imports when rocq-of-rust is compiled
    
   2. Refinement axioms connecting Rust to spec
    
   3. Derived theorems proven from refinement + spec
    
   4. State construction helpers for testing
    
   AXIOM STATUS:
   4 refinement axioms to become theorems when RocqOfRust available
   All derived properties are proven from axioms + spec lemmas
*)
