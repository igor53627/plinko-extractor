(** * Type Links for Plinko
    
    This module defines Link instances connecting:
    - Simulation types (Z-based integers) in specs/
    - Translated Rust types from rocq-of-rust
    
    The linking approach follows rocq-of-rust conventions:
    - Link typeclass provides Φ (Rust type) and φ (encoding function)
    - OfTy.t witnesses Rocq type ↔ Rust type correspondence
*)

Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulations.M.

Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Import ListNotations.

Require Import Plinko.Specs.CommonTypes.

Open Scope Z_scope.

(** ** Byte linking (u8) *)

Module ByteLink.
  Definition Rust_ty : Ty.t := Ty.path "u8".
  
  Global Instance IsLink : Link Z := {
    Φ := Rust_ty;
    φ b := Value.Integer IntegerKind.U8 b;
  }.
  
  Definition of_ty : OfTy.t Rust_ty.
  Proof. eapply OfTy.Make with (A := Z); reflexivity. Defined.
End ByteLink.

(** ** Word linking (u64) *)

Module WordLink.
  Definition Rust_ty : Ty.t := Ty.path "u64".
  
  Global Instance IsLink : Link Z := {
    Φ := Rust_ty;
    φ w := Value.Integer IntegerKind.U64 w;
  }.
  
  Definition of_ty : OfTy.t Rust_ty.
  Proof. eapply OfTy.Make with (A := Z); reflexivity. Defined.
End WordLink.

(** ** Usize linking *)

Module UsizeLink.
  Definition Rust_ty : Ty.t := Ty.path "usize".
  
  Global Instance IsLink : Link nat := {
    Φ := Rust_ty;
    φ n := Value.Integer IntegerKind.Usize (Z.of_nat n);
  }.
  
  Definition of_ty : OfTy.t Rust_ty.
  Proof. eapply OfTy.Make with (A := nat); reflexivity. Defined.
End UsizeLink.

(** ** Key128 linking ([u8; 16]) *)

Module Key128Link.
  Definition Rust_ty : Ty.t := 
    Ty.apply (Ty.path "array") [Value.Integer IntegerKind.Usize 16] [Ty.path "u8"].
  
  Fixpoint bytes_to_array (bs : list Z) : list Value.t :=
    match bs with
    | [] => []
    | b :: rest => Value.Integer IntegerKind.U8 b :: bytes_to_array rest
    end.
  
  Global Instance IsLink : Link Key128 := {
    Φ := Rust_ty;
    φ k := Value.Array (bytes_to_array k);
  }.
  
  Definition of_ty : OfTy.t Rust_ty.
  Proof. eapply OfTy.Make with (A := Key128); reflexivity. Defined.
End Key128Link.

(** ** SwapOrNot params linking *)

Module SwapOrNotParamsLink.
  (** Rust struct: SwapOrNot { cipher: Aes128, domain: u64, num_rounds: usize } *)
  Definition Rust_ty : Ty.t := Ty.path "plinko::iprf::SwapOrNot".
  
  (** We link to a pair (domain, num_rounds) for specification purposes *)
  Record SwapOrNotParams := mkSwapOrNotParams {
    son_domain : Z;
    son_num_rounds : nat;
  }.
  
  Global Instance IsLink : Link SwapOrNotParams := {
    Φ := Rust_ty;
    φ p := Value.StructRecord "plinko::iprf::SwapOrNot" [] []
             [("domain", Value.Integer IntegerKind.U64 (son_domain p));
              ("num_rounds", Value.Integer IntegerKind.Usize (Z.of_nat (son_num_rounds p)))];
  }.
End SwapOrNotParamsLink.

(** ** Iprf params linking *)

Module IprfParamsLink.
  (** Rust struct: Iprf { key, cipher, prp, domain, range, _tree_depth } *)
  Definition Rust_ty : Ty.t := Ty.path "plinko::iprf::Iprf".
  
  (** We link to (n, m) domain/range pair for specification *)
  Record IprfParams := mkIprfParams {
    iprf_n : Z;  (** domain *)
    iprf_m : Z;  (** range *)
  }.
  
  Global Instance IsLink : Link IprfParams := {
    Φ := Rust_ty;
    φ p := Value.StructRecord "plinko::iprf::Iprf" [] []
             [("domain", Value.Integer IntegerKind.U64 (iprf_n p));
              ("range", Value.Integer IntegerKind.U64 (iprf_m p))];
  }.
End IprfParamsLink.

(** ** Database params linking *)

Module DbParamsLink.
  (** Result type of derive_plinko_params: (chunk_size, set_size) *)
  Definition Rust_ty : Ty.t := 
    Ty.tuple [Ty.path "u64"; Ty.path "u64"].
  
  Global Instance IsLink : Link (Z * Z) := {
    Φ := Rust_ty;
    φ p := Value.Tuple [Value.Integer IntegerKind.U64 (fst p);
                        Value.Integer IntegerKind.U64 (snd p)];
  }.
  
  Definition of_ty : OfTy.t Rust_ty.
  Proof. eapply OfTy.Make with (A := Z * Z); reflexivity. Defined.
End DbParamsLink.

(** ** Option linking *)

Module OptionLink.
  Definition Rust_ty (A_ty : Ty.t) : Ty.t := 
    Ty.apply (Ty.path "core::option::Option") [] [A_ty].
  
  Global Instance IsLink (A : Set) `{Link A} : Link (option A) := {
    Φ := OptionLink.Rust_ty (Φ A);
    φ opt := match opt with
             | None => Value.StructTuple "core::option::Option::None" [] [Φ A] []
             | Some v => Value.StructTuple "core::option::Option::Some" [] [Φ A] [φ v]
             end;
  }.
End OptionLink.

(** ** Vec/list linking *)

Module ListLink.
  Definition Rust_ty (A_ty : Ty.t) : Ty.t := 
    Ty.apply (Ty.path "alloc::vec::Vec") [] [A_ty].
  
  Fixpoint list_to_values {A : Set} `{Link A} (l : list A) : list Value.t :=
    match l with
    | [] => []
    | x :: rest => φ x :: list_to_values rest
    end.
  
  Global Instance IsLink (A : Set) `{Link A} : Link (list A) := {
    Φ := ListLink.Rust_ty (Φ A);
    φ l := Value.StructTuple "alloc::vec::Vec" [] [Φ A] [Value.Array (list_to_values l)];
  }.
End ListLink.

(** ** Link hints for proof automation *)

#[export] Hint Resolve ByteLink.of_ty : of_ty.
#[export] Hint Resolve WordLink.of_ty : of_ty.
#[export] Hint Resolve UsizeLink.of_ty : of_ty.
#[export] Hint Resolve Key128Link.of_ty : of_ty.
#[export] Hint Resolve DbParamsLink.of_ty : of_ty.
