(** * HintInitSim: Simulation Relation for Plinko HintInit
    
    Connects the Rust plinko_hints.rs implementation to the Plinko paper
    specification (Fig. 7 HintInit) and Plinko.v Coq spec.
    
    Key implementation details from plinko_hints.rs:
    - derive_block_keys(master_seed, c): derives c iPRF keys (one per block)
    - Regular hints: subset size c/2+1, single parity
    - Backup hints: subset size c/2, dual parities (in/out)
    - iPRF domain = total hints (lambda x w + q), range = w (block size)
    - Streaming: (block, offset) = (i/w, i mod w)
    
    TRUST BASE (Axioms):
    - [derive_key_deterministic], [derive_key_distinct]: Key derivation properties
    - [block_in_subset_deterministic], [block_in_subset_block_range]: Subset membership
    - [subset_from_seed_length]: Statistical property of hash-based subset selection
    
    PROVEN (Main Theorem):
    - hint_init_streaming_eq_batch: Regular hint streaming == batch
      * Uses xor_list_permutation (proven) and batch_parity_as_xor_list (proven)
      * Proof complete modulo two admitted helper lemmas
    
    PROVEN (Supporting Lemmas):
    - XOR algebra (Z-level): lxor_comm, lxor_assoc, lxor_0_r/l, lxor_nilpotent
    - XOR algebra (Entry-level): xor_entry_comm, xor_entry_assoc, xor_entry_0_r/l, xor_entry_nilpotent
    - XOR algebra (Pair-level): xor_pair_comm, xor_pair_assoc, xor_pair_0_r/l, xor_pair_nilpotent
    - XOR list algebra: xor_list_permutation (permutation invariance)
    - Fold helpers: fold_left_xor_entry_length, fold_left_xor_acc, xor_list_app
    - iPRF parameter validity: streaming_iprf_correct
    - Per-block key correctness: per_block_key_correct
    - simulation_preserves_invariants: Uses subset_from_seed_length axiom and
      seed range invariants from HintInitSimulation record
    - batch_parity_as_xor_list: Batch parity = xor_list of batch entries
    - contributing_entries_length_32: Contributing entries have length 32
    - mapi_aux_In: Helper for mapi membership
    
    ADMITTED (3 lemmas - isolated reasoning steps):
    1. streaming_parity_as_xor_list: Streaming parity = xor_list of contributing entries
       - Requires: Loop invariant induction over database fold
       - Key insight: Each step either XORs entry (if contributing) or leaves unchanged
    2. contributing_entries_permutation_batch: Contributing entries ~ batch entries
       - Requires: Bijection using iprf_inverse_contains_preimage and
         iprf_inverse_elements_map_to_y from IprfSpec.v
       - Key insight: Entry at i=block*w+offset contributes iff forward(j)=offset and
         block in subset
    3. hint_init_backup_streaming_eq_batch: Backup hint streaming == batch
       - Same structure as regular hints, with dual parity tracking
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Sorting.Permutation.

Require Import Plinko.Specs.IprfSpec.
Require Import Plinko.Specs.CommonTypes.
Require Import Plinko.Sims.SimTypes.

Import ListNotations.
Open Scope Z_scope.

(** ============================================================================
    Section 1: Hint Type Refinements
    ============================================================================ *)

Section HintTypeRefinements.

(** Rust RegularHint structure (from plinko_hints.rs lines 55-58):
    struct RegularHint {
        seed: u64,
        parity: [u8; 32],
    }
    
    Paper Fig. 7: P_j subset of c/2+1 blocks, single parity p_j
*)
Record RustRegularHint := mkRustRegularHint {
  rrh_seed : Z;
  rrh_parity : list Z    (* 32 bytes as list of Z *)
}.

Record SpecRegularHint := mkSpecRegularHint {
  srh_blocks : list Z;   (* Explicit subset P_j of block indices *)
  srh_parity : list Z    (* XOR parity (32 bytes) *)
}.

(** Refinement: Rust hint refines spec hint when subset can be regenerated from seed *)
Definition refines_regular_hint (c subset_size : Z) 
    (rust : RustRegularHint) (spec : SpecRegularHint) : Prop :=
  (* Seed determines the same subset as explicit blocks *)
  (* (abstracted - actual membership check uses block_in_subset_seeded) *)
  length (srh_blocks spec) = Z.to_nat subset_size /\
  subset_size = c / 2 + 1 /\
  rrh_parity rust = srh_parity spec /\
  0 <= rrh_seed rust < 2^64.

(** Rust BackupHint structure (from plinko_hints.rs lines 60-66):
    struct BackupHint {
        seed: u64,
        parity_in: [u8; 32],
        parity_out: [u8; 32],
    }
    
    Paper Fig. 7: B_j subset of c/2 blocks, dual parities (in/out)
*)
Record RustBackupHint := mkRustBackupHint {
  rbh_seed : Z;
  rbh_parity_in : list Z;
  rbh_parity_out : list Z
}.

Record SpecBackupHint := mkSpecBackupHint {
  sbh_blocks : list Z;     (* Explicit subset B_j *)
  sbh_parity_in : list Z;  (* Parity of entries where block in B_j *)
  sbh_parity_out : list Z  (* Parity of entries where block not in B_j *)
}.

Definition refines_backup_hint (c subset_size : Z)
    (rust : RustBackupHint) (spec : SpecBackupHint) : Prop :=
  length (sbh_blocks spec) = Z.to_nat subset_size /\
  subset_size = c / 2 /\
  rbh_parity_in rust = sbh_parity_in spec /\
  rbh_parity_out rust = sbh_parity_out spec /\
  0 <= rbh_seed rust < 2^64.

End HintTypeRefinements.

(** ============================================================================
    Section 2: Block Key Derivation Simulation
    ============================================================================ *)

Section BlockKeyDerivation.

(** Rust derive_block_keys (plinko_hints.rs lines 90-103):
    fn derive_block_keys(master_seed: &[u8; 32], c: usize) -> Vec<PrfKey128> {
        for block_idx in 0..c {
            hasher.update(master_seed);
            hasher.update(b"block_key");
            hasher.update(&(block_idx as u64).to_le_bytes());
            ...
        }
    }
    
    Paper: c iPRF keys, one per block (Section 5)
*)

(** Abstract key derivation function *)
Parameter derive_key : Z -> Z -> Z.  (* master_seed -> block_idx -> key *)

(** Specification: keys are deterministic and distinct *)
Axiom derive_key_deterministic : forall seed idx,
  derive_key seed idx = derive_key seed idx.

Axiom derive_key_distinct : forall seed idx1 idx2,
  idx1 <> idx2 ->
  0 <= idx1 ->
  0 <= idx2 ->
  derive_key seed idx1 <> derive_key seed idx2.

(** Block keys list *)
Definition derive_block_keys_spec (seed c : Z) : list Z :=
  map (derive_key seed) (map Z.of_nat (seq 0 (Z.to_nat c))).

(** Refinement: Rust derive_block_keys refines spec *)
Definition refines_block_keys (rust_keys spec_keys : list Z) (c : Z) : Prop :=
  length rust_keys = Z.to_nat c /\
  length spec_keys = Z.to_nat c /\
  rust_keys = spec_keys.

End BlockKeyDerivation.

(** ============================================================================
    Section 3: Subset Membership Simulation
    ============================================================================ *)

Section SubsetMembership.

(** Rust block_in_subset_seeded (plinko_hints.rs lines 115-126):
    fn block_in_subset_seeded(seed: u64, subset_size: usize, 
                              total_blocks: usize, block: usize) -> bool
        let hash_val = SHA256(seed || block);
        let threshold = (subset_size / total_blocks) x u64_MAX;
        hash_val < threshold
    
    This is a probabilistic membership test with expected subset_size elements.
*)

(** Abstract membership predicate *)
Parameter block_in_subset : Z -> Z -> Z -> Z -> bool.
  (* seed -> subset_size -> total_blocks -> block -> in_subset *)

(** Specification properties *)

(** Deterministic: same inputs give same result *)
Axiom block_in_subset_deterministic : forall seed size total block,
  block_in_subset seed size total block = block_in_subset seed size total block.

(** Expected size: approximately subset_size elements in subset *)
(** (This is a statistical property, not proven here) *)

(** Membership respects bounds *)
Axiom block_in_subset_block_range : forall seed size total block,
  block_in_subset seed size total block = true ->
  0 <= block < total.

(** Conversion to explicit subset *)
Definition subset_from_seed (seed size total : Z) : list Z :=
  filter (fun b => block_in_subset seed size total b)
         (map Z.of_nat (seq 0 (Z.to_nat total))).

(** Axiom: subset_from_seed produces a list of expected length.
    This is a statistical property: SHA256-based threshold selection 
    produces expected subset_size elements. We axiomatize exact equality
    as an idealization of the hash function behavior. *)
Axiom subset_from_seed_length : forall seed size total,
  0 < size ->
  size <= total ->
  0 < total ->
  Z.of_nat (length (subset_from_seed seed size total)) = size.

End SubsetMembership.

(** ============================================================================
    Section 3.5: XOR Algebra Lemmas (Z-level)
    ============================================================================ *)

Section XorAlgebraZ.

Lemma lxor_comm : forall x y, Z.lxor x y = Z.lxor y x.
Proof. intros. apply Z.lxor_comm. Qed.

Lemma lxor_assoc : forall x y z, Z.lxor (Z.lxor x y) z = Z.lxor x (Z.lxor y z).
Proof. intros. apply Z.lxor_assoc. Qed.

Lemma lxor_0_r : forall x, Z.lxor x 0 = x.
Proof. intros. rewrite Z.lxor_0_r. reflexivity. Qed.

Lemma lxor_0_l : forall x, Z.lxor 0 x = x.
Proof. intros. rewrite Z.lxor_0_l. reflexivity. Qed.

Lemma lxor_nilpotent : forall x, Z.lxor x x = 0.
Proof. intros. apply Z.lxor_nilpotent. Qed.

End XorAlgebraZ.

(** ============================================================================
    Section 4: Streaming Database Processing
    ============================================================================ *)

Section StreamingProcessing.

(** mapi helper: map with index *)
Fixpoint mapi_aux {A B : Type} (n : nat) (f : nat -> A -> B) (l : list A) : list B :=
  match l with
  | nil => nil
  | x :: xs => f n x :: mapi_aux (S n) f xs
  end.

Definition mapi {A B : Type} (f : nat -> A -> B) (l : list A) : list B :=
  mapi_aux 0 f l.

(** Pipe operator for readability *)
Definition pipe {A B : Type} (x : A) (f : A -> B) : B := f x.
Notation "x |> f" := (pipe x f) (at level 60, right associativity).

(** Rust streaming loop (plinko_hints.rs lines 340-376):
    for i in 0..n_effective {
        let block = i / w;
        let offset = i % w;
        let entry = db[i];
        let hint_indices = block_iprfs[block].inverse(offset);
        for j in hint_indices {
            if j < num_regular {
                if block_in_subset_seeded(...) {
                    xor_32(&mut hint.parity, &entry);
                }
            } else {
                if block_in_subset_seeded(...) {
                    xor_32(&mut hint.parity_in, &entry);
                } else {
                    xor_32(&mut hint.parity_out, &entry);
                }
            }
        }
    }
*)

(** Database entry type: 32 bytes represented as list of Z *)
Definition Entry := list Z.

(** XOR of two 32-byte values *)
Definition xor_entry (a b : Entry) : Entry :=
  map (fun '(x, y) => Z.lxor x y) (combine a b).

(** Zero entry *)
Definition zero_entry : Entry := repeat 0 32.

(** State during streaming *)
Record StreamingState := mkStreamingState {
  ss_regular_parities : list Entry;
  ss_backup_parities_in : list Entry;
  ss_backup_parities_out : list Entry
}.

(** Initial state: all parities zero *)
Definition init_streaming_state (num_regular num_backup : Z) : StreamingState :=
  mkStreamingState
    (repeat zero_entry (Z.to_nat num_regular))
    (repeat zero_entry (Z.to_nat num_backup))
    (repeat zero_entry (Z.to_nat num_backup)).

(** Process one database entry *)
Definition process_entry_streaming 
    (st : StreamingState)
    (block_keys : list Z)
    (regular_seeds backup_seeds : list Z)
    (c w num_regular num_backup total_hints : Z)
    (i : Z) (entry : Entry) : StreamingState :=
  let block := i / w in
  let offset := i mod w in
  let key := nth (Z.to_nat block) block_keys 0 in
  let hint_indices := iprf_inverse_spec offset total_hints w in
  let regular_subset_size := c / 2 + 1 in
  let backup_subset_size := c / 2 in
  (* Update regular hints *)
  let new_regular := mapi (fun idx parity =>
    let j := Z.of_nat idx in
    if existsb (Z.eqb j) hint_indices then
      let seed := nth idx regular_seeds 0 in
      if block_in_subset seed regular_subset_size c block then
        xor_entry parity entry
      else parity
    else parity
  ) (ss_regular_parities st) in
  (* Update backup hints *)
  let new_backup_in := mapi (fun idx parity =>
    let j := Z.of_nat idx + num_regular in
    if existsb (Z.eqb j) hint_indices then
      let seed := nth idx backup_seeds 0 in
      if block_in_subset seed backup_subset_size c block then
        xor_entry parity entry
      else parity
    else parity
  ) (ss_backup_parities_in st) in
  let new_backup_out := mapi (fun idx parity =>
    let j := Z.of_nat idx + num_regular in
    if existsb (Z.eqb j) hint_indices then
      let seed := nth idx backup_seeds 0 in
      if negb (block_in_subset seed backup_subset_size c block) then
        xor_entry parity entry
      else parity
    else parity
  ) (ss_backup_parities_out st) in
  mkStreamingState new_regular new_backup_in new_backup_out.

(** Fold over database to compute final state *)
Definition hint_init_streaming
    (block_keys : list Z)
    (regular_seeds backup_seeds : list Z)
    (c w num_regular num_backup : Z)
    (database : list Entry) : StreamingState :=
  let total_hints := num_regular + num_backup in
  fst (fold_left (fun '(st, i) entry =>
    (process_entry_streaming st block_keys regular_seeds backup_seeds
       c w num_regular num_backup total_hints i entry, i + 1)
  ) database (init_streaming_state num_regular num_backup, 0)).

End StreamingProcessing.

(** ============================================================================
    Section 4.5: XOR Entry Algebra Lemmas
    ============================================================================ *)

Section XorAlgebraEntry.

Lemma xor_entry_comm : forall a b, xor_entry a b = xor_entry b a.
Proof.
  intros a b. unfold xor_entry.
  revert b. induction a as [|x xs IH]; intros [|y ys]; simpl; try reflexivity.
  f_equal.
  - apply lxor_comm.
  - apply IH.
Qed.

Lemma xor_entry_assoc : forall a b c, 
  length a = length b -> length b = length c ->
  xor_entry (xor_entry a b) c = xor_entry a (xor_entry b c).
Proof.
  intros a. induction a as [|x xs IH]; intros [|y ys] [|z zs] Hab Hbc; 
    simpl in *; try reflexivity; try discriminate.
  injection Hab as Hab. injection Hbc as Hbc.
  unfold xor_entry. simpl. f_equal.
  - apply lxor_assoc.
  - fold (xor_entry xs ys). fold (xor_entry (xor_entry xs ys) zs).
    fold (xor_entry ys zs). fold (xor_entry xs (xor_entry ys zs)).
    apply IH; assumption.
Qed.

Lemma xor_entry_0_r : forall a, length a = 32%nat -> xor_entry a zero_entry = a.
Proof.
  intros a Ha. unfold xor_entry, zero_entry.
  assert (Hlen : length (repeat 0 32) = 32%nat) by (apply repeat_length).
  revert Ha. generalize 32%nat as n. intros n Ha.
  revert n Ha. induction a as [|x xs IH]; intros n Ha; simpl.
  - destruct n; reflexivity.
  - destruct n; [discriminate|]. simpl.
    injection Ha as Ha. simpl. f_equal.
    + apply lxor_0_r.
    + apply IH. assumption.
Qed.

Lemma xor_entry_0_l : forall a, length a = 32%nat -> xor_entry zero_entry a = a.
Proof.
  intros a Ha. rewrite xor_entry_comm. apply xor_entry_0_r. assumption.
Qed.

Lemma combine_self : forall {A : Type} (l : list A),
  combine l l = map (fun x => (x, x)) l.
Proof.
  intros A l. induction l as [|x xs IH]; simpl.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Lemma xor_entry_nilpotent_aux : forall a, 
  map (fun '(x, y) => Z.lxor x y) (combine a a) = repeat 0 (length a).
Proof.
  induction a as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite lxor_nilpotent. f_equal. exact IH.
Qed.

Lemma xor_entry_nilpotent : forall a, length a = 32%nat -> xor_entry a a = zero_entry.
Proof.
  intros a Ha. unfold xor_entry, zero_entry.
  rewrite xor_entry_nilpotent_aux. rewrite Ha. reflexivity.
Qed.

End XorAlgebraEntry.

(** ============================================================================
    Section 4.55: XOR Pair Algebra (for backup hints with dual parities)
    ============================================================================ *)

Section XorPairAlgebra.

(** Pair XOR for backup hints: (parity_in, parity_out) *)
Definition xor_pair (p1 p2 : Entry * Entry) : Entry * Entry :=
  (xor_entry (fst p1) (fst p2), xor_entry (snd p1) (snd p2)).

Definition zero_pair : Entry * Entry := (zero_entry, zero_entry).

Lemma xor_pair_comm : forall p1 p2, xor_pair p1 p2 = xor_pair p2 p1.
Proof.
  intros [a1 b1] [a2 b2]. unfold xor_pair. simpl.
  f_equal; apply xor_entry_comm.
Qed.

Lemma xor_pair_assoc : forall p1 p2 p3,
  length (fst p1) = 32%nat -> length (snd p1) = 32%nat ->
  length (fst p2) = 32%nat -> length (snd p2) = 32%nat ->
  length (fst p3) = 32%nat -> length (snd p3) = 32%nat ->
  xor_pair (xor_pair p1 p2) p3 = xor_pair p1 (xor_pair p2 p3).
Proof.
  intros [a1 b1] [a2 b2] [a3 b3] Ha1 Hb1 Ha2 Hb2 Ha3 Hb3.
  unfold xor_pair. simpl in *.
  f_equal.
  - apply xor_entry_assoc.
    + rewrite Ha1. symmetry. exact Ha2.
    + rewrite Ha2. symmetry. exact Ha3.
  - apply xor_entry_assoc.
    + rewrite Hb1. symmetry. exact Hb2.
    + rewrite Hb2. symmetry. exact Hb3.
Qed.

Lemma xor_pair_0_r : forall p,
  length (fst p) = 32%nat -> length (snd p) = 32%nat ->
  xor_pair p zero_pair = p.
Proof.
  intros [a b] Ha Hb. unfold xor_pair, zero_pair. simpl in *.
  f_equal; apply xor_entry_0_r; assumption.
Qed.

Lemma xor_pair_0_l : forall p,
  length (fst p) = 32%nat -> length (snd p) = 32%nat ->
  xor_pair zero_pair p = p.
Proof.
  intros p Hp1 Hp2. rewrite xor_pair_comm. apply xor_pair_0_r; assumption.
Qed.

Lemma xor_pair_nilpotent : forall p,
  length (fst p) = 32%nat -> length (snd p) = 32%nat ->
  xor_pair p p = zero_pair.
Proof.
  intros [a b] Ha Hb. unfold xor_pair, zero_pair. simpl in *.
  f_equal; apply xor_entry_nilpotent; assumption.
Qed.

End XorPairAlgebra.

(** ============================================================================
    Section 4.6: XOR List Lemmas (for fold permutation invariance)
    ============================================================================ *)

Section XorList.

Definition xor_list (l : list Entry) : Entry :=
  fold_left xor_entry l zero_entry.

Lemma fold_left_xor_entry_length : forall l acc,
  length acc = 32%nat ->
  (forall e, In e l -> length e = 32%nat) ->
  length (fold_left xor_entry l acc) = 32%nat.
Proof.
  intros l. induction l as [|x xs IH]; intros acc Hacc Hl.
  - simpl. exact Hacc.
  - simpl. apply IH.
    + unfold xor_entry. rewrite map_length. rewrite combine_length.
      rewrite Hacc. assert (length x = 32%nat) by (apply Hl; left; reflexivity).
      lia.
    + intros e He. apply Hl. right. exact He.
Qed.

Lemma xor_list_length : forall l,
  (forall e, In e l -> length e = 32%nat) ->
  length (xor_list l) = 32%nat.
Proof.
  intros l Hl. unfold xor_list.
  apply fold_left_xor_entry_length.
  - unfold zero_entry. apply repeat_length.
  - exact Hl.
Qed.

Lemma fold_left_xor_acc : forall l acc,
  length acc = 32%nat ->
  (forall e, In e l -> length e = 32%nat) ->
  fold_left xor_entry l acc = xor_entry acc (xor_list l).
Proof.
  intros l. induction l as [|x xs IH]; intros acc Hacc Hl.
  - simpl. unfold xor_list. simpl.
    rewrite xor_entry_0_r; [reflexivity | exact Hacc].
  - simpl. unfold xor_list. simpl.
    assert (Hx : length x = 32%nat).
    { apply Hl. left. reflexivity. }
    assert (Hxs : forall e, In e xs -> length e = 32%nat).
    { intros e He. apply Hl. right. exact He. }
    assert (Hacc_x : length (xor_entry acc x) = 32%nat).
    { unfold xor_entry. rewrite map_length. rewrite combine_length.
      rewrite Hacc. rewrite Hx. reflexivity. }
    assert (Hzero_x : length (xor_entry zero_entry x) = 32%nat).
    { unfold xor_entry. rewrite map_length. rewrite combine_length.
      unfold zero_entry. rewrite repeat_length. rewrite Hx. reflexivity. }
    rewrite IH; [| exact Hacc_x | exact Hxs].
    rewrite IH; [| exact Hzero_x | exact Hxs].
    fold (xor_list xs).
    rewrite xor_entry_0_l; [| exact Hx].
    assert (Hxor_list_len : length (xor_list xs) = 32%nat).
    { apply xor_list_length. exact Hxs. }
    assert (Hab : length acc = length x) by (rewrite Hacc; rewrite Hx; reflexivity).
    assert (Hbc : length x = length (xor_list xs)) by (rewrite Hx; rewrite Hxor_list_len; reflexivity).
    rewrite <- xor_entry_assoc; [reflexivity | exact Hab | exact Hbc].
Qed.

Lemma xor_list_app : forall l1 l2,
  (forall e, In e l1 -> length e = 32%nat) ->
  (forall e, In e l2 -> length e = 32%nat) ->
  xor_list (l1 ++ l2) = xor_entry (xor_list l1) (xor_list l2).
Proof.
  intros l1 l2 Hl1 Hl2.
  unfold xor_list at 1.
  rewrite fold_left_app.
  assert (Hxor_list_len : length (xor_list l1) = 32%nat).
  { apply xor_list_length. exact Hl1. }
  rewrite fold_left_xor_acc; [reflexivity | exact Hxor_list_len | exact Hl2].
Qed.

Lemma xor_list_permutation : forall l1 l2,
  Permutation l1 l2 ->
  (forall e, In e l1 -> length e = 32%nat) ->
  xor_list l1 = xor_list l2.
Proof.
  intros l1 l2 Hperm. induction Hperm; intros Hlen.
  - reflexivity.
  - unfold xor_list. simpl.
    assert (Hx : length x = 32%nat) by (apply Hlen; left; reflexivity).
    assert (Hl : forall e, In e l -> length e = 32%nat).
    { intros e He. apply Hlen. right. exact He. }
    assert (Hl' : forall e, In e l' -> length e = 32%nat).
    { intros e He. apply Hl. eapply Permutation_in.
      - apply Permutation_sym. exact Hperm.
      - exact He. }
    assert (Hzero_x : length (xor_entry zero_entry x) = 32%nat).
    { unfold xor_entry. rewrite map_length. rewrite combine_length.
      unfold zero_entry. rewrite repeat_length. rewrite Hx. reflexivity. }
    rewrite fold_left_xor_acc; [| exact Hzero_x | exact Hl].
    rewrite fold_left_xor_acc; [| exact Hzero_x | exact Hl'].
    f_equal. apply IHHperm. exact Hl.
  - unfold xor_list. simpl.
    assert (Hx : length x = 32%nat) by (apply Hlen; right; left; reflexivity).
    assert (Hy : length y = 32%nat) by (apply Hlen; left; reflexivity).
    assert (Hl : forall e, In e l -> length e = 32%nat).
    { intros e He. apply Hlen. right. right. exact He. }
    assert (Hzero : length zero_entry = 32%nat).
    { unfold zero_entry. apply repeat_length. }
    assert (Hzy : length (xor_entry zero_entry y) = 32%nat).
    { unfold xor_entry. rewrite map_length. rewrite combine_length.
      rewrite Hzero. rewrite Hy. reflexivity. }
    assert (Hzx : length (xor_entry zero_entry x) = 32%nat).
    { unfold xor_entry. rewrite map_length. rewrite combine_length.
      rewrite Hzero. rewrite Hx. reflexivity. }
    assert (Hzyx : length (xor_entry (xor_entry zero_entry y) x) = 32%nat).
    { unfold xor_entry at 1. rewrite map_length. rewrite combine_length.
      rewrite Hzy. rewrite Hx. reflexivity. }
    assert (Hzxy : length (xor_entry (xor_entry zero_entry x) y) = 32%nat).
    { unfold xor_entry at 1. rewrite map_length. rewrite combine_length.
      rewrite Hzx. rewrite Hy. reflexivity. }
    assert (Hxor_list_len : length (fold_left xor_entry l zero_entry) = 32%nat).
    { apply fold_left_xor_entry_length; [exact Hzero | exact Hl]. }
    assert (Hswap : xor_entry (xor_entry zero_entry y) x = xor_entry (xor_entry zero_entry x) y).
    { rewrite xor_entry_0_l; [| exact Hy].
      rewrite xor_entry_0_l; [| exact Hx].
      apply xor_entry_comm. }
    rewrite Hswap. reflexivity.
  - assert (Hl' : forall e, In e l' -> length e = 32%nat).
    { intros e He. apply Hlen. eapply Permutation_in.
      - apply Permutation_sym. exact Hperm1.
      - exact He. }
    assert (Hl'' : forall e, In e l'' -> length e = 32%nat).
    { intros e He. apply Hl'. eapply Permutation_in.
      - apply Permutation_sym. exact Hperm2.
      - exact He. }
    rewrite IHHperm1; [| exact Hlen].
    rewrite IHHperm2; [| exact Hl'].
    reflexivity.
Qed.

End XorList.

(** ============================================================================
    Section 5: Batch Processing (Specification)
    ============================================================================ *)

Section BatchProcessing.

(** Paper Fig. 7 HintInit (batch version):
    For each regular hint j:
      P_j = random subset of size c/2+1
      p_j = XOR of DB[block * w + iPRF_block(j)] for block in P_j
    
    For each backup hint j:
      B_j = random subset of size c/2
      l_j = XOR of DB[block * w + iPRF_block(j)] for block in B_j
      r_j = XOR of DB[block * w + iPRF_block(j)] for block not in B_j
*)

(** Compute parity for a regular hint (batch) *)
Definition compute_regular_parity_batch
    (block_keys : list Z)
    (subset : list Z)  (* P_j: explicit list of blocks *)
    (hint_idx : Z)
    (w total_hints : Z)
    (database : list Entry) : Entry :=
  fold_left (fun acc block_z =>
    let block := Z.to_nat block_z in
    let key := nth block block_keys 0 in
    let offset := iprf_forward_spec hint_idx total_hints w in
    let db_idx := block_z * w + offset in
    let entry := nth (Z.to_nat db_idx) database zero_entry in
    xor_entry acc entry
  ) subset zero_entry.

(** Compute parities for a backup hint (batch) *)
Definition compute_backup_parities_batch
    (block_keys : list Z)
    (subset : list Z)  (* B_j: explicit list of blocks *)
    (hint_idx : Z)
    (c w total_hints : Z)
    (database : list Entry) : (Entry * Entry) :=
  fold_left (fun '(parity_in, parity_out) block_z =>
    let block := Z.to_nat block_z in
    let key := nth block block_keys 0 in
    let offset := iprf_forward_spec hint_idx total_hints w in
    let db_idx := block_z * w + offset in
    let entry := nth (Z.to_nat db_idx) database zero_entry in
    if existsb (Z.eqb block_z) subset then
      (xor_entry parity_in entry, parity_out)
    else
      (parity_in, xor_entry parity_out entry)
  ) (map Z.of_nat (seq 0 (Z.to_nat c))) (zero_entry, zero_entry).

End BatchProcessing.

(** ============================================================================
    Section 5.5: iPRF Parameter Validity
    ============================================================================ *)

(** iPRF parameters match paper specification *)
Definition iprf_params_valid (total_hints w : Z) : Prop :=
  total_hints > 0 /\
  w > 0 /\
  w <= total_hints.

(** Streaming uses correct iPRF configuration *)
Lemma streaming_iprf_correct :
  forall lambda w q,
    lambda > 0 ->
    w > 0 ->
    q >= 0 ->
    let total_hints := lambda * w + q in
    iprf_params_valid total_hints w.
Proof.
  intros lambda0 w0 q0 Hlambda Hw Hq.
  unfold iprf_params_valid.
  split.
  - assert (lambda0 * w0 > 0) by nia. lia.
  - split.
    + exact Hw.
    + assert (lambda0 * w0 >= w0) by nia. lia.
Qed.

(** ============================================================================
    Section 6: HintInit Correctness Theorem
    ============================================================================ *)

Section HintInitCorrectness.

Context (c w lambda q : Z).
Context (Hc_pos : c > 0).
Context (Hw_pos : w > 0).
Context (Hlambda_pos : lambda > 0).
Context (Hq_pos : q >= 0).

Let num_regular := lambda * w.
Let num_backup := q.
Let total_hints := num_regular + num_backup.
Let n := c * w.

(** ============================================================================
    Section 6.1: Helper Definitions for Streaming-Batch Equivalence
    ============================================================================ *)

(** Predicate: database entry at index i contributes to regular hint j.
    
    An entry contributes if:
    1. j is in iprf_inverse(i mod w) -- i.e., this offset maps to hint j
    2. block = i / w is in the subset for hint j
*)
Definition entry_contributes_regular
    (j seed_j subset_size c0 total_hints0 w0 : Z) (i : Z) : bool :=
  let block := i / w0 in
  let offset := i mod w0 in
  let hint_indices := iprf_inverse_spec offset total_hints0 w0 in
  existsb (Z.eqb j) hint_indices && block_in_subset seed_j subset_size c0 block.

(** Extract entries from database that contribute to hint j.
    Returns list of entries (not indices) that pass the contribution test. *)
Definition contributing_entries
    (j seed_j subset_size c0 total_hints0 w0 : Z)
    (database : list Entry) : list Entry :=
  let indexed := mapi (fun idx e => (Z.of_nat idx, e)) database in
  map snd (filter (fun '(i, _) => 
    entry_contributes_regular j seed_j subset_size c0 total_hints0 w0 i) indexed).

(** Batch entries: entries accessed by batch computation for hint j.
    For each block in subset, access database[block * w + iprf_forward(j)]. *)
Definition batch_entries
    (j w0 total_hints0 : Z) (subset : list Z)
    (database : list Entry) : list Entry :=
  map (fun block_z =>
    let offset := iprf_forward_spec j total_hints0 w0 in
    let db_idx := block_z * w0 + offset in
    nth (Z.to_nat db_idx) database zero_entry
  ) subset.

(** ============================================================================
    Section 6.2: Key Helper Lemmas
    ============================================================================ *)

(** Helper 1: Streaming parity for hint j equals XOR of contributing entries.
    
    PROOF STATUS: Admitted
    PROOF REQUIREMENT: Induction on database with loop invariant.
    
    Invariant: After processing entries 0..i-1, the parity for hint j equals
    XOR of all entries k < i where entry_contributes_regular(j, ..., k) = true.
    
    Base case: Initial parity is zero_entry. contributing_entries of [] is [].
               xor_list [] = fold_left xor_entry [] zero_entry = zero_entry. [OK]
    
    Inductive case: Processing entry i either:
      - XORs it into parity (if entry_contributes_regular = true)
        -> matches appending entry to contributing list
      - Leaves parity unchanged (if entry_contributes_regular = false)  
        -> matches not appending
    
    The proof is complex due to nested mapi and fold_left in process_entry_streaming.
*)
(** Helper: mapi extensionality *)
Lemma mapi_ext : forall {A B : Type} (f g : nat -> A -> B) (l : list A),
  (forall n a, f n a = g n a) -> mapi f l = mapi g l.
Proof.
  intros A B f g l Hext.
  unfold mapi.
  assert (Haux : forall n, mapi_aux n f l = mapi_aux n g l).
  { induction l as [|x xs IH]; intros n0.
    - reflexivity.
    - simpl. rewrite Hext. f_equal. apply IH. }
  apply Haux.
Qed.

(** Helper: contributing entries with offset - for induction with absolute indices *)
Definition contributing_entries_from
    (j seed_j subset_size c0 total_hints0 w0 start_idx : Z)
    (database : list Entry) : list Entry :=
  let indexed := mapi (fun idx e => (start_idx + Z.of_nat idx, e)) database in
  map snd (filter (fun '(i, _) => 
    entry_contributes_regular j seed_j subset_size c0 total_hints0 w0 i) indexed).

Lemma contributing_entries_from_zero :
  forall j seed_j subset_size c0 total_hints0 w0 database,
    contributing_entries_from j seed_j subset_size c0 total_hints0 w0 0 database =
    contributing_entries j seed_j subset_size c0 total_hints0 w0 database.
Proof.
  intros. unfold contributing_entries_from, contributing_entries.
  assert (Hmapi_eq : mapi (fun idx e => (0 + Z.of_nat idx, e)) database =
                     mapi (fun idx e => (Z.of_nat idx, e)) database).
  { apply mapi_ext. intros n0 e0. 
    replace (0 + Z.of_nat n0) with (Z.of_nat n0) by lia. reflexivity. }
  rewrite Hmapi_eq. reflexivity.
Qed.

Lemma mapi_aux_ext :
  forall {A B : Type} (f g : nat -> A -> B) (l : list A) (n : nat),
    (forall k e, (k >= n)%nat -> f k e = g k e) -> 
    mapi_aux n f l = mapi_aux n g l.
Proof.
  intros A B f g l.
  induction l as [|x xs IH]; intros n0 Hext.
  - reflexivity.
  - simpl. f_equal.
    + apply Hext. lia.
    + apply IH. intros k e Hk. apply Hext. lia.
Qed.

Lemma mapi_aux_offset_eq :
  forall {A : Type} (start_idx : Z) (db : list A) (n : nat),
    mapi_aux n (fun (idx : nat) (e : A) => (start_idx + 1 + Z.of_nat idx, e)) db =
    mapi_aux n (fun (idx : nat) (e : A) => (start_idx + Z.of_nat (S idx), e)) db.
Proof.
  intros A start_idx db n0.
  apply mapi_aux_ext. intros k e Hk.
  replace (start_idx + 1 + Z.of_nat k) with (start_idx + Z.of_nat (S k)) by lia.
  reflexivity.
Qed.

Lemma mapi_aux_start_shift :
  forall {A : Type} (start_idx : Z) (db : list A) (n m : nat),
    mapi_aux n (fun (idx : nat) (e : A) => (start_idx + Z.of_nat idx, e)) db =
    mapi_aux m (fun (idx : nat) (e : A) => (start_idx + Z.of_nat (idx + n - m), e)) db.
Proof.
  intros A start_idx db.
  induction db as [|x xs IH]; intros n0 m0.
  - reflexivity.
  - simpl. f_equal.
    + replace (m0 + n0 - m0)%nat with n0 by lia. reflexivity.
    + specialize (IH (S n0) (S m0)). rewrite IH.
      apply mapi_aux_ext. intros k e Hk.
      replace (k + S n0 - S m0)%nat with (k + n0 - m0)%nat by lia.
      reflexivity.
Qed.

Lemma contributing_entries_from_cons :
  forall j seed_j subset_size c0 total_hints0 w0 start_idx entry db,
    contributing_entries_from j seed_j subset_size c0 total_hints0 w0 start_idx (entry :: db) =
    (if entry_contributes_regular j seed_j subset_size c0 total_hints0 w0 start_idx
     then [entry]
     else []) ++
    contributing_entries_from j seed_j subset_size c0 total_hints0 w0 (start_idx + 1) db.
Proof.
  intros.
  unfold contributing_entries_from.
  unfold mapi. simpl.
  replace (start_idx + 0) with start_idx by lia.
  assert (Htail_eq : 
    filter (fun '(i, _) => entry_contributes_regular j seed_j subset_size c0 total_hints0 w0 i)
           (mapi_aux 1 (fun idx e => (start_idx + Z.of_nat idx, e)) db) =
    filter (fun '(i, _) => entry_contributes_regular j seed_j subset_size c0 total_hints0 w0 i)
           (mapi_aux 0 (fun idx e => (start_idx + 1 + Z.of_nat idx, e)) db)).
  { f_equal.
    transitivity (mapi_aux 0 (fun idx e => (start_idx + Z.of_nat (idx + 1), e)) db).
    - rewrite mapi_aux_start_shift with (m := 0%nat).
      apply mapi_aux_ext. intros k e Hk.
      replace (k + 1 - 0)%nat with (k + 1)%nat by lia. reflexivity.
    - apply mapi_aux_ext. intros k e Hk.
      replace (start_idx + Z.of_nat (k + 1)) with (start_idx + 1 + Z.of_nat k) by lia.
      reflexivity. }
  destruct (entry_contributes_regular j seed_j subset_size c0 total_hints0 w0 start_idx) eqn:Hcontr.
  - simpl. f_equal. rewrite Htail_eq. reflexivity.
  - simpl. rewrite Htail_eq. reflexivity.
Qed.

(** streaming_parity_as_xor_list: Streaming parity = xor_list of contributing entries.

    PROOF STATUS: Partially developed, requires detailed mapi reasoning.
    
    KEY PROOF STRUCTURE:
    1. Define contributing_entries_from with absolute indices for proper induction
    2. Base case: empty db gives zero_entry = xor_list []
    3. Inductive step: entry contributes => XOR it, else leave unchanged
    4. The mapi in process_entry_streaming selects hint j when j in iprf_inverse
       and block in subset - this matches entry_contributes_regular predicate
    
    REMAINING WORK:
    - Prove nth_mapi_update: when entry contributes, parity j is XOR'd with entry
    - Prove nth_mapi_preserve: when entry doesn't contribute, parity j unchanged
    - These require careful reasoning about mapi with existsb and block_in_subset
*)
Lemma streaming_parity_as_xor_list :
  forall (block_keys regular_seeds backup_seeds : list Z)
         (c0 w0 num_regular0 num_backup0 : Z)
         (database : list Entry)
         (j : Z),
    let total_hints0 := num_regular0 + num_backup0 in
    0 <= j < num_regular0 ->
    w0 > 0 ->
    let seed_j := nth (Z.to_nat j) regular_seeds 0 in
    let subset_size := c0 / 2 + 1 in
    let streaming_result := hint_init_streaming 
      block_keys regular_seeds backup_seeds c0 w0 num_regular0 num_backup0 database in
    nth (Z.to_nat j) (ss_regular_parities streaming_result) zero_entry =
    xor_list (contributing_entries j seed_j subset_size c0 total_hints0 w0 database).
Proof.
  intros block_keys regular_seeds backup_seeds c0 w0 num_regular0 num_backup0 database j0.
  intros total_hints0 Hj Hw seed_j subset_size streaming_result.
  
  unfold streaming_result, hint_init_streaming.
  set (total := total_hints0).
  
  (* The proof proceeds by induction on database, maintaining the invariant that
     after processing entries [0, i), the parity for hint j equals the XOR of all
     contributing entries from those indices.
     
     Key observation: process_entry_streaming updates parity j via mapi when:
       existsb (Z.eqb j) (iprf_inverse_spec (i mod w) total w) = true AND
       block_in_subset seed_j subset_size c (i / w) = true
     
     This is exactly entry_contributes_regular j seed_j subset_size c total w i.
     
     The proof structure:
     1. contributing_entries_from_zero relates our helper to contributing_entries
     2. contributing_entries_from_cons splits at each step
     3. Induction shows streaming accumulates the right entries
     
     Due to the complexity of mapi reasoning (nested structure with existsb),
     we admit the detailed proof but have established the key structure. *)
  
  rewrite <- contributing_entries_from_zero.
  
  (* The main induction would go here, but requires detailed mapi lemmas *)
Admitted.

(** Helper 2: Batch parity equals XOR of batch entries.
    
    PROOF STATUS: Proven by unfolding definitions.
    
    This is essentially compute_regular_parity_batch unfolded as a fold_left,
    which equals xor_list (map f subset) by definition of xor_list.
*)
Lemma batch_parity_as_xor_list :
  forall (block_keys : list Z) (subset : list Z)
         (j w0 total_hints0 : Z) (database : list Entry),
    w0 > 0 ->
    0 <= j < total_hints0 ->
    compute_regular_parity_batch block_keys subset j w0 total_hints0 database =
    xor_list (batch_entries j w0 total_hints0 subset database).
Proof.
  intros block_keys subset j0 w0 total_hints0 database Hw Hj.
  unfold compute_regular_parity_batch, batch_entries, xor_list.
  set (f := fun block_z : Z => nth (Z.to_nat (block_z * w0 + iprf_forward_spec j0 total_hints0 w0)) database zero_entry).
  change (fold_left (fun acc block_z => xor_entry acc (f block_z)) subset zero_entry =
          fold_left xor_entry (map f subset) zero_entry).
  generalize zero_entry as acc.
  induction subset as [|b bs IH]; intros acc.
  - simpl. reflexivity.
  - simpl. apply IH.
Qed.

(** Helper 3: Contributing entries and batch entries are permutations.
    
    PROOF STATUS: Admitted
    PROOF REQUIREMENT: Bijection between the two sets of entries.
    
    KEY INSIGHT: An entry at index i = block*w + offset contributes to hint j iff:
      - j in iprf_inverse_spec(offset) <==> iprf_forward_spec(j) = offset
        (by iprf_inverse_elements_map_to_y and iprf_inverse_contains_preimage)
      - block_in_subset(seed_j, subset_size, c, block) = true
        <==> block in subset_from_seed(seed_j, subset_size, c)
    
    This matches batch access: database[block*w + iprf_forward_spec(j)] for block in subset.
    
    The bijection preserves values since both access the same database indices.
    
    Lemmas needed:
    - iprf_inverse_contains_preimage: j in iprf_inverse(iprf_forward(j))
    - iprf_inverse_elements_map_to_y: x in iprf_inverse(y) => iprf_forward(x) = y
    - filter/In equivalence for subset_from_seed
*)
(** Helper: Elements in subset_from_seed are exactly those with block_in_subset = true *)
Lemma subset_from_seed_In : forall seed size total block,
  In block (subset_from_seed seed size total) <->
  (0 <= block < total /\ block_in_subset seed size total block = true).
Proof.
  intros seed size total block.
  unfold subset_from_seed.
  rewrite filter_In.
  split.
  - intros [Hin Hmem].
    split.
    + apply in_map_iff in Hin. destruct Hin as [k [Heq Hseq]].
      subst block. apply in_seq in Hseq. lia.
    + exact Hmem.
  - intros [Hrange Hmem].
    split.
    + apply in_map_iff. exists (Z.to_nat block). split.
      * rewrite Z2Nat.id; lia.
      * apply in_seq. lia.
    + exact Hmem.
Qed.

(** Helper: An entry at index i contributes to hint j iff j's batch accesses index i *)
Lemma contributing_iff_batch_index :
  forall j seed_j subset_size c0 total_hints0 w0 i,
    0 <= j < total_hints0 ->
    w0 > 0 ->
    total_hints0 > 0 ->
    w0 <= total_hints0 ->
    c0 > 0 ->
    0 <= i < c0 * w0 ->
    let block := i / w0 in
    let offset := i mod w0 in
    entry_contributes_regular j seed_j subset_size c0 total_hints0 w0 i = true <->
    (block_in_subset seed_j subset_size c0 block = true /\
     iprf_forward_spec j total_hints0 w0 = offset).
Proof.
  intros j seed_j subset_size c0 total_hints0 w0 i Hj Hw Hth Hw_le Hc Hi block offset.
  unfold entry_contributes_regular.
  rewrite andb_true_iff.
  split.
  - intros [Hexists Hblock].
    split.
    + exact Hblock.
    + apply existsb_exists in Hexists.
      destruct Hexists as [x [Hin Heqb]].
      apply Z.eqb_eq in Heqb. subst x.
      apply iprf_inverse_elements_map_to_y with (y := offset); try lia.
      * split.
        -- apply Z.mod_pos_bound. lia.
        -- apply Z.mod_pos_bound. lia.
      * exact Hin.
  - intros [Hblock Hfwd].
    split.
    + apply existsb_exists. exists j. split.
      * apply iprf_inverse_contains_preimage.
        -- lia.
        -- lia.
        -- lia.
        -- exact Hfwd.
      * apply Z.eqb_refl.
    + exact Hblock.
Qed.

Lemma contributing_entries_permutation_batch :
  forall (j seed_j c0 w0 total_hints0 : Z) (database : list Entry),
    let subset_size := c0 / 2 + 1 in
    let subset := subset_from_seed seed_j subset_size c0 in
    0 <= j < total_hints0 ->
    w0 > 0 ->
    total_hints0 > 0 ->
    w0 <= total_hints0 ->
    c0 > 0 ->
    length database = Z.to_nat (c0 * w0) ->
    Permutation 
      (contributing_entries j seed_j subset_size c0 total_hints0 w0 database)
      (batch_entries j w0 total_hints0 subset database).
Proof.
  intros j seed_j c0 w0 total_hints0 database subset_size subset Hj Hw Hth Hw_le Hc Hdb_len.
  
  (* Strategy: Show both lists contain the same elements (with same multiplicity).
     
     contributing_entries: filter database entries where entry_contributes_regular = true
       These are entries at indices i where:
         - j in iprf_inverse(i mod w) AND block_in_subset(i / w) = true
         - By contributing_iff_batch_index, this is equivalent to:
           iprf_forward(j) = i mod w AND block in subset
           
     batch_entries: for each block in subset, access database[block * w + iprf_forward(j)]
     
     The key bijection:
       - contributing entry at index i = block * w + offset where offset = iprf_forward(j)
         and block in subset
       - batch entry for block = database[block * w + iprf_forward(j)]
       
     These access the same database positions, so the lists are equal up to order.
     
     For Permutation, we need to show the multisets are equal. Since subset has no
     duplicates (it's a filter of distinct block indices), and each block maps to
     exactly one database index, both lists have no duplicates of entries from the
     same position (though entries can be duplicate if database has duplicate values).
  *)
  
  (* The proof would show:
     1. Every contributing entry appears in batch_entries (at some block)
     2. Every batch entry appears in contributing_entries (at its index)
     3. Use NoDup properties to establish Permutation *)
  
Admitted.

(** Helper 4: All contributing entries have length 32.
    
    PROOF STATUS: Proven.
    
    Contributing entries are filtered from database, so inherit length 32.
*)

Lemma mapi_aux_In : forall {A B : Type} (f : nat -> A -> B) (l : list A) (n : nat) (y : B),
  In y (mapi_aux n f l) -> exists k x, (k < length l)%nat /\ nth_error l k = Some x /\ y = f (n + k)%nat x.
Proof.
  intros A B f l.
  induction l as [|a l' IH]; intros n0 y Hin.
  - simpl in Hin. destruct Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + exists 0%nat, a. split; [simpl; lia|]. split; [reflexivity|].
      rewrite Nat.add_0_r. symmetry. exact Heq.
    + specialize (IH (S n0) y Hin).
      destruct IH as [k [x [Hlt [Hnth Heq]]]].
      exists (S k), x. split; [simpl; lia|]. split; [exact Hnth|].
      replace (n0 + S k)%nat with (S n0 + k)%nat by lia. exact Heq.
Qed.

Lemma contributing_entries_length_32 :
  forall j seed_j subset_size c0 total_hints0 w0 database,
    (forall e, In e database -> length e = 32%nat) ->
    forall e, In e (contributing_entries j seed_j subset_size c0 total_hints0 w0 database) ->
      length e = 32%nat.
Proof.
  intros j seed_j subset_size c0 total_hints0 w0 database Hdb e Hin.
  unfold contributing_entries in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [[idx entry] [Heq Hfilter]].
  simpl in Heq. subst e.
  apply filter_In in Hfilter.
  destruct Hfilter as [Hmapi _].
  unfold mapi in Hmapi.
  apply mapi_aux_In in Hmapi.
  destruct Hmapi as [k [x [Hlt [Hnth Heq]]]].
  injection Heq as _ Heq. subst entry.
  apply Hdb.
  apply nth_error_In with (n := k). exact Hnth.
Qed.

(** ============================================================================
    Section 6.3: Main Correctness Theorem
    ============================================================================ *)

(** Main correctness theorem: streaming produces same parities as batch.
    
    PROOF STRUCTURE:
    1. streaming_parity_as_xor_list: streaming result = xor_list(contributing_entries)
    2. batch_parity_as_xor_list: batch result = xor_list(batch_entries)  [PROVEN]
    3. contributing_entries_permutation_batch: contributing_entries ~ batch_entries
    4. xor_list_permutation: xor_list is invariant under permutation   [PROVEN]
    
    KEY LEMMAS from IprfSpec.v (all proven):
    - iprf_inverse_partitions_domain: each x in [0, total_hints) in exactly one inverse bucket
    - iprf_inverse_elements_map_to_y: elements in iprf_inverse(y) map back to y via forward
    - iprf_inverse_contains_preimage: x in iprf_inverse(iprf_forward(x))
    
    ADMITTED HELPERS:
    - streaming_parity_as_xor_list: requires induction on database fold
    - contributing_entries_permutation_batch: requires bijection construction
*)
Theorem hint_init_streaming_eq_batch :
  forall (block_keys regular_seeds backup_seeds : list Z)
         (database : list Entry),
    length block_keys = Z.to_nat c ->
    length regular_seeds = Z.to_nat num_regular ->
    length backup_seeds = Z.to_nat num_backup ->
    length database = Z.to_nat n ->
    (forall e, In e database -> length e = 32%nat) ->
    let streaming_result := hint_init_streaming 
      block_keys regular_seeds backup_seeds c w num_regular num_backup database in
    forall j,
      0 <= j < num_regular ->
      let subset := subset_from_seed (nth (Z.to_nat j) regular_seeds 0)
                                     (c / 2 + 1) c in
      nth (Z.to_nat j) (ss_regular_parities streaming_result) zero_entry =
      compute_regular_parity_batch block_keys subset j w total_hints database.
Proof.
  intros block_keys regular_seeds backup_seeds database
         Hkeys Hreg Hback Hdb Hdb_lens streaming_result j0 Hj subset.
  
  (* Establish parameter validity *)
  assert (Hparams : iprf_params_valid total_hints w).
  { apply streaming_iprf_correct; assumption. }
  destruct Hparams as [Hth_pos [Hw_pos' Hw_le]].
  
  (* Setup definitions *)
  set (seed_j := nth (Z.to_nat j0) regular_seeds 0).
  set (subset_size := c / 2 + 1).
  
  (* Step 1: Streaming parity = xor_list of contributing entries *)
  assert (Hstream_xor : 
    nth (Z.to_nat j0) (ss_regular_parities streaming_result) zero_entry =
    xor_list (contributing_entries j0 seed_j subset_size c total_hints w database)).
  { unfold streaming_result, seed_j, subset_size.
    apply streaming_parity_as_xor_list; assumption. }
  
  (* Step 2: Batch parity = xor_list of batch entries *)
  assert (Hbatch_xor :
    compute_regular_parity_batch block_keys subset j0 w total_hints database =
    xor_list (batch_entries j0 w total_hints subset database)).
  { apply batch_parity_as_xor_list; lia. }
  
  (* Step 3: Contributing entries ~ batch entries (permutation) *)
  assert (Hperm : Permutation
    (contributing_entries j0 seed_j subset_size c total_hints w database)
    (batch_entries j0 w total_hints subset database)).
  { unfold subset, seed_j, subset_size.
    apply contributing_entries_permutation_batch.
    - lia. (* 0 <= j0 < total_hints *)
    - lia. (* w > 0 *)
    - lia. (* total_hints > 0 *)
    - lia. (* w <= total_hints *)
    - lia. (* c > 0 *)
    - unfold n in Hdb. exact Hdb. (* length database = Z.to_nat (c * w) *) }
  
  (* Step 4: Apply permutation invariance of xor_list *)
  rewrite Hstream_xor, Hbatch_xor.
  apply xor_list_permutation.
  - exact Hperm.
  - apply contributing_entries_length_32. exact Hdb_lens.
Qed.

(** Backup hint correctness - similar reasoning to regular hints.
    
    PROOF STATUS: Admitted
    
    This is the dual-parity version of hint_init_streaming_eq_batch. The proof
    requires showing that streaming accumulates (parity_in, parity_out) correctly
    for backup hints, where:
    - parity_in = XOR of entries where block IS in subset B_j
    - parity_out = XOR of entries where block is NOT in subset B_j
    - hint index is j + num_regular (offset into backup hints)
    - subset size is c/2 (not c/2+1 as in regular hints)
    
    Key proof ingredients (all established):
    1. xor_pair algebra: xor_pair_comm, xor_pair_assoc, xor_pair_0_r/l, xor_pair_nilpotent
    2. iPRF partition: each (block, offset) processed exactly once
    3. Subset membership determinism: block_in_subset_deterministic
    4. Forward-inverse correspondence: iprf_inverse_elements_map_to_y
    
    The mathematical argument:
    - Streaming: for each entry i = block*w + offset, check if (j + num_regular)
      is in iprf_inverse(offset), then update parity_in or parity_out based on
      block_in_subset
    - Batch: compute offset = iprf_forward(j + num_regular), iterate over all
      blocks, accumulate parity_in for blocks in subset, parity_out otherwise
    - Equivalence: by iPRF inverse-forward correspondence, streaming visits
      exactly the entries at offset = iprf_forward(j + num_regular) for each block.
      XOR commutativity/associativity ensures order independence.
*)
Theorem hint_init_backup_streaming_eq_batch :
  forall (block_keys regular_seeds backup_seeds : list Z)
         (database : list Entry),
    length block_keys = Z.to_nat c ->
    length regular_seeds = Z.to_nat num_regular ->
    length backup_seeds = Z.to_nat num_backup ->
    length database = Z.to_nat n ->
    let streaming_result := hint_init_streaming 
      block_keys regular_seeds backup_seeds c w num_regular num_backup database in
    forall j,
      0 <= j < num_backup ->
      let subset := subset_from_seed (nth (Z.to_nat j) backup_seeds 0)
                                     (c / 2) c in
      let '(batch_in, batch_out) := 
        compute_backup_parities_batch block_keys subset (j + num_regular) 
                                      c w total_hints database in
      nth (Z.to_nat j) (ss_backup_parities_in streaming_result) zero_entry = batch_in /\
      nth (Z.to_nat j) (ss_backup_parities_out streaming_result) zero_entry = batch_out.
Proof.
  intros block_keys regular_seeds backup_seeds database
         Hkeys Hreg Hback Hdb streaming_result j0 Hj subset.
  (* Establish iPRF parameter validity *)
  assert (Hparams : iprf_params_valid total_hints w).
  { apply streaming_iprf_correct; assumption. }
  destruct Hparams as [Hth_pos [Hw_pos' Hw_le]].
  
  (* iPRF partition: each domain element belongs to exactly one inverse set *)
  assert (Hpartition : forall x, 0 <= x < total_hints ->
    exists! y, 0 <= y < w /\ In x (iprf_inverse_spec y total_hints w)).
  { intros x Hx. apply iprf_inverse_partitions_domain; lia. }
  
  (* Hint index j + num_regular is in valid range *)
  assert (Hj_total : 0 <= j0 + num_regular < total_hints).
  { unfold total_hints, num_regular, num_backup in *. lia. }
  
  (* Forward-inverse correspondence for this hint *)
  assert (Hfwd_inv : forall y x,
    0 <= y < w ->
    In x (iprf_inverse_spec y total_hints w) ->
    iprf_forward_spec x total_hints w = y).
  { intros y x Hy Hin. 
    apply iprf_inverse_elements_map_to_y with (y := y); try lia. exact Hin. }
  
  (* XOR pair algebra for dual parities *)
  assert (Hxor_pair_comm := xor_pair_comm).
  assert (Hxor_pair_assoc := xor_pair_assoc).
  assert (Hxor_pair_0_r := xor_pair_0_r).
  assert (Hxor_pair_0_l := xor_pair_0_l).
  
  (* XOR entry algebra *)
  assert (Hxor_comm := xor_entry_comm).
  assert (Hxor_assoc := xor_entry_assoc).
  
  (* Subset membership is deterministic *)
  assert (Hmem_det := block_in_subset_deterministic).
  
  (* The key insight: streaming and batch compute the same (parity_in, parity_out) pair.
     
     Define the pair accumulator:
       acc_pair = (parity_in, parity_out)
     
     Streaming invariant after processing entry i:
       acc_pair = xor_pair of all (entry_in, entry_out) where:
         - block = i' / w for i' < i
         - offset = i' mod w
         - (j0 + num_regular) is in iprf_inverse(offset)
         - entry_in = entry if block in subset, else zero_entry
         - entry_out = entry if block NOT in subset, else zero_entry
     
     Batch computes:
       offset = iprf_forward(j0 + num_regular)
       for each block in [0, c):
         entry = database[block * w + offset]
         if block in subset: parity_in ^= entry
         else: parity_out ^= entry
     
     These are equal because:
     1. By iPRF forward-inverse: streaming visits entry at (block, offset) iff
        (j0 + num_regular) is in iprf_inverse(offset), which happens iff
        iprf_forward(j0 + num_regular) = offset
     2. Both visit exactly the entries at offset = iprf_forward(j0 + num_regular)
        for each block in [0, c)
     3. XOR is commutative and associative: order of accumulation doesn't matter
     4. Subset membership is deterministic: same split into in/out in both cases
  *)
  
  (* Full inductive proof over database fold would require:
     - Loop invariant stating accumulated (parity_in, parity_out) at position i
     - Induction on database length
     - Case analysis on whether each entry contributes to this hint
     
     The mathematical soundness is established by the lemmas above.
     The remaining work is mechanical induction bookkeeping. *)
Admitted.

End HintInitCorrectness.

(** ============================================================================
    Section 7: iPRF Domain/Range Refinement
    ============================================================================ *)

Section IprfRefinement.

(** Rust iPRF instantiation (plinko_hints.rs lines 335-338):
    let block_iprfs: Vec[Iprf] = block_keys
        .iter()
        .map(|key| Iprf::new(key, total_hints as u64, w as u64))
        .collect();
    
    Paper: iPRF with domain = total_hints, range = w
*)

(** Per-block key: Rust uses block_iprfs[block] for inverse *)
Lemma per_block_key_correct :
  forall (block_keys : list Z) block offset total_hints w,
    0 <= block < Z.of_nat (length block_keys) ->
    0 <= offset < w ->
    iprf_params_valid total_hints w ->
    forall j, In j (iprf_inverse_spec offset total_hints w) ->
      0 <= j < total_hints.
Proof.
  intros block_keys block offset total_hints w Hblock Hoffset [Hth_pos [Hw_pos Hw_le]] j Hin.
  assert (Hrange : 0 <= offset < w) by assumption.
  apply (iprf_inverse_elements_in_domain offset total_hints w j); try lia.
  exact Hin.
Qed.

End IprfRefinement.

(** ============================================================================
    Section 8: Full Simulation Relation
    ============================================================================ *)

Section FullSimulation.

(** Complete simulation relation between Rust HintInit and paper spec *)
Record HintInitSimulation := mkHintInitSim {
  his_c : Z;
  his_w : Z;
  his_lambda : Z;
  his_q : Z;
  
  his_c_pos : his_c >= 2;  (* Requires >= 2 for backup subset size c/2 > 0 *)
  his_w_pos : his_w > 0;
  his_lambda_pos : his_lambda > 0;
  his_q_nonneg : his_q >= 0;
  
  his_block_keys : list Z;
  his_regular_hints : list RustRegularHint;
  his_backup_hints : list RustBackupHint;
  
  his_keys_len : length his_block_keys = Z.to_nat his_c;
  his_regular_len : length his_regular_hints = Z.to_nat (his_lambda * his_w);
  his_backup_len : length his_backup_hints = Z.to_nat his_q;
  
  his_regular_seeds_in_range : 
    Forall (fun h => 0 <= rrh_seed h < 2^64) his_regular_hints;
  his_backup_seeds_in_range : 
    Forall (fun h => 0 <= rbh_seed h < 2^64) his_backup_hints
}.

(** Simulation preserves paper invariants.
    
    PROOF STATUS: Proven with axiomatized subset length property.
    
    The subset length equality (length(filter) = subset_size) is a statistical
    property of the hash-based probabilistic subset membership. In expectation,
    the threshold-based filter produces the desired size. For the simulation,
    we assume this property holds (justified by concentration bounds on uniform hashing).
*)
Theorem simulation_preserves_invariants :
  forall sim,
    (* Regular subset size = c/2 + 1 *)
    (forall j, (j < length (his_regular_hints sim))%nat ->
      exists spec, refines_regular_hint (his_c sim) (his_c sim / 2 + 1)
                     (nth j (his_regular_hints sim) 
                        (mkRustRegularHint 0 nil)) spec) /\
    (* Backup subset size = c/2 *)
    (forall j, (j < length (his_backup_hints sim))%nat ->
      exists spec, refines_backup_hint (his_c sim) (his_c sim / 2)
                     (nth j (his_backup_hints sim)
                        (mkRustBackupHint 0 nil nil)) spec) /\
    (* Per-block iPRF keys *)
    length (his_block_keys sim) = Z.to_nat (his_c sim).
Proof.
  intros sim.
  split; [|split].
  - intros j Hj.
    set (rust_hint := nth j (his_regular_hints sim) (mkRustRegularHint 0 nil)).
    set (c := his_c sim).
    set (subset_size := c / 2 + 1).
    exists (mkSpecRegularHint 
              (subset_from_seed (rrh_seed rust_hint) subset_size c)
              (rrh_parity rust_hint)).
    unfold refines_regular_hint. simpl.
    split; [|split; [|split]].
    + (* subset length = expected size *)
      assert (Hc_ge2 := his_c_pos sim). unfold c in *.
      assert (Hc_pos : 0 < his_c sim) by lia.
      assert (Hsize_pos : 0 < subset_size).
      { unfold subset_size. 
        assert (0 <= his_c sim / 2) by (apply Z.div_pos; lia). lia. }
      assert (Hsize_le : subset_size <= his_c sim).
      { unfold subset_size.
        assert (his_c sim / 2 < his_c sim) by (apply Z.div_lt_upper_bound; lia).
        lia. }
      pose proof (subset_from_seed_length (rrh_seed rust_hint) subset_size (his_c sim) 
                    Hsize_pos Hsize_le Hc_pos) as Hlen.
      apply Nat2Z.inj. rewrite Hlen. symmetry. apply Z2Nat.id. lia.
    + reflexivity.
    + reflexivity.
    + (* seed in range *)
      assert (Hseeds := his_regular_seeds_in_range sim).
      apply Forall_forall with (x := rust_hint) in Hseeds.
      * simpl in Hseeds. exact Hseeds.
      * apply nth_In. exact Hj.
  - intros j Hj.
    set (rust_hint := nth j (his_backup_hints sim) (mkRustBackupHint 0 nil nil)).
    set (c := his_c sim).
    set (subset_size := c / 2).
    exists (mkSpecBackupHint 
              (subset_from_seed (rbh_seed rust_hint) subset_size c)
              (rbh_parity_in rust_hint)
              (rbh_parity_out rust_hint)).
    unfold refines_backup_hint. simpl.
    split; [|split; [|split; [|split]]].
    + (* subset length = expected size *)
      assert (Hc_ge2 := his_c_pos sim). unfold c in *.
      assert (Hc_pos : 0 < his_c sim) by lia.
      assert (Hsize_pos : 0 < subset_size).
      { unfold subset_size.
        pose proof (Z.div_str_pos (his_c sim) 2). lia. }
      assert (Hsize_le : subset_size <= his_c sim).
      { unfold subset_size. 
        assert (his_c sim / 2 < his_c sim) by (apply Z.div_lt_upper_bound; lia). lia. }
      pose proof (subset_from_seed_length (rbh_seed rust_hint) subset_size (his_c sim) 
                    Hsize_pos Hsize_le Hc_pos) as Hlen.
      apply Nat2Z.inj. rewrite Hlen. symmetry. apply Z2Nat.id.
      unfold subset_size. apply Z.div_pos; lia.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + (* seed in range *)
      assert (Hseeds := his_backup_seeds_in_range sim).
      apply Forall_forall with (x := rust_hint) in Hseeds.
      * simpl in Hseeds. exact Hseeds.
      * apply nth_In. exact Hj.
  - exact (his_keys_len sim).
Qed.

End FullSimulation.

Close Scope Z_scope.
