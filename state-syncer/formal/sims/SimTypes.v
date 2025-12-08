(** SimTypes.v - Simulation relation infrastructure for Plinko verification *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.

(** Simulation relations connect:
    - Rocq specs (pure functional, in specs/)
    - Translated Rust (from rocq-of-rust, in src/)
    
    The approach:
    1. Define refinement relations between spec types and Rust types
    2. Prove that Rust functions refine spec functions
    3. Lift spec properties to Rust implementations
*)

(** Basic refinement: Rust u64 refines Z when in range *)
Definition refines_u64 (rust_val : Z) (spec_val : Z) : Prop :=
  rust_val = spec_val /\ (0 <= spec_val < 2^64)%Z.

(** List refinement *)
Definition refines_list {A B : Type} (R : A -> B -> Prop) 
  (rust_list : list A) (spec_list : list B) : Prop :=
  length rust_list = length spec_list /\
  forall i : nat, (i < length rust_list)%nat ->
    exists a b, nth_error rust_list i = Some a /\
                nth_error spec_list i = Some b /\
                R a b.

(** TODO: Add refinement relations for:
    - SwapOrNot state
    - Iprf state  
    - Database parameters
*)

(** Placeholder for simulation proofs *)
Section SimulationProofs.

(** When translated code is available, prove:
    - swap_or_not_forward refines forward_spec
    - iprf_forward refines iprf_forward_spec
    - derive_plinko_params refines derive_plinko_params_spec
*)

End SimulationProofs.
