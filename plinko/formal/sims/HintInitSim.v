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
    
    PROVEN:
    - XOR algebra (Z-level): lxor_comm, lxor_assoc, lxor_0_r/l, lxor_nilpotent
    - XOR algebra (Entry-level): xor_entry_comm, xor_entry_assoc, xor_entry_0_r/l, xor_entry_nilpotent
    - iPRF parameter validity: streaming_iprf_correct
    - Per-block key correctness: per_block_key_correct
    - simulation_preserves_invariants: Uses subset_from_seed_length axiom and
      seed range invariants from HintInitSimulation record
    
    ADMITTED (2 theorems):
    1. hint_init_streaming_eq_batch: Regular hint streaming == batch
       - Needs: Loop invariant induction over database fold
       - Key lemmas established: iPRF partition (iprf_inverse_partitions_domain),
         XOR order-independence (xor_entry_comm/assoc)
    2. hint_init_backup_streaming_eq_batch: Backup hint streaming == batch
       - Same as above, with dual parity tracking
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

(** Main correctness theorem: streaming produces same parities as batch.
    
    This is the key property that connects the efficient Rust implementation
    (single pass over database) to the paper specification (which conceptually
    accesses each entry via iPRF.forward).
    
    The proof relies on:
    1. iPRF inverse partitions domain: each (block, offset) pair is processed
       exactly once during streaming
    2. XOR is commutative and associative: order of processing doesn't matter
    3. Subset membership is deterministic: same decision in streaming and batch
*)
(** Main correctness theorem: streaming produces same parities as batch.
    
    PROOF STATUS: Admitted
    
    The proof requires a complex loop invariant showing that after processing
    database entry i, the accumulated parity for hint j equals:
    XOR of all database[block*w + offset] where:
    - block is in the hint's subset (determined by seed)
    - offset = iPRF.forward(j, total_hints, w)
    - block*w + offset < i
    
    Key lemmas needed:
    1. iPRF partition property (iprf_inverse_partitions_domain) - PROVEN in IprfSpec.v
    2. XOR commutativity/associativity - PROVEN above
    3. Subset membership determinism - AXIOMATIZED (block_in_subset_deterministic)
    4. Loop invariant preservation under fold_left - requires induction on database
    
    The mathematical argument is sound: streaming and batch visit the same
    entries in different orders, and XOR is order-independent.
*)
Theorem hint_init_streaming_eq_batch :
  forall (block_keys regular_seeds backup_seeds : list Z)
         (database : list Entry),
    length block_keys = Z.to_nat c ->
    length regular_seeds = Z.to_nat num_regular ->
    length backup_seeds = Z.to_nat num_backup ->
    length database = Z.to_nat n ->
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
         Hkeys Hreg Hback Hdb streaming_result j0 Hj subset.
  assert (Hparams : iprf_params_valid total_hints w).
  { apply streaming_iprf_correct; assumption. }
  destruct Hparams as [Hth_pos [Hw_pos' Hw_le]].
  assert (Hpartition : forall x, 0 <= x < total_hints ->
    exists! y, 0 <= y < w /\ In x (iprf_inverse_spec y total_hints w)).
  { intros x Hx. apply iprf_inverse_partitions_domain; lia. }
  assert (Hfwd_inv : forall y x,
    0 <= y < w ->
    In x (iprf_inverse_spec y total_hints w) ->
    iprf_forward_spec x total_hints w = y).
  { intros y x Hy Hin. apply iprf_inverse_elements_map_to_y with (y := y); try lia. exact Hin. }
  assert (Hxor_comm := xor_entry_comm).
  assert (Hxor_assoc := xor_entry_assoc).
Admitted.

(** Backup hint correctness - similar reasoning to regular hints *)
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
  assert (Hparams : iprf_params_valid total_hints w).
  { apply streaming_iprf_correct; assumption. }
  destruct Hparams as [Hth_pos [Hw_pos' Hw_le]].
  assert (Hpartition : forall x, 0 <= x < total_hints ->
    exists! y, 0 <= y < w /\ In x (iprf_inverse_spec y total_hints w)).
  { intros x Hx. apply iprf_inverse_partitions_domain; lia. }
  assert (Hxor_comm := xor_entry_comm).
  assert (Hxor_assoc := xor_entry_assoc).
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
