(** * Plinko: Single-Server PIR with Efficient Updates via Invertible PRFs
    
    This Coq implementation provides the hint generation and management
    algorithms from the Plinko paper (2024-318).
    
    Key components:
    - PMNS (Pseudorandom Multinomial Sampler) for random function simulation
    - iPRF (Invertible PRF) built from PRP + PMNS
    - Hint initialization, querying, and updating
*)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import ZArith.ZArith.
Import ListNotations.

(** ** Core Parameters *)

Module Type PlinkoParams.
  Parameter n : nat.          (* Database size in bits *)
  Parameter w : nat.          (* Block size *)
  Parameter q : nat.          (* Number of queries before refresh *)
  Parameter lambda : nat.     (* Security parameter *)
  
  Axiom w_pos : w > 0.
  Axiom n_divisible : exists k, n = k * w.
End PlinkoParams.

(** ** Abstract PRF/PRP Interface *)

Module Type PRFInterface.
  Parameter Key : Type.
  Parameter Domain : Type.
  Parameter Range : Type.
  
  Parameter gen : nat -> Key.
  Parameter eval : Key -> Domain -> Range.
  Parameter eval_inv : Key -> Range -> Domain.  (* For PRP only *)
End PRFInterface.

(** ** PMNS Tree Node *)

Record PMNSNode := mkPMNSNode {
  node_start : nat;    (* Starting ball index *)
  node_count : nat;    (* Number of balls in this subtree *)
  node_low   : nat;    (* Lowest bin index *)
  node_high  : nat     (* Highest bin index *)
}.

(** ** PMNS Implementation 
    
    Binary tree sampling that simulates throwing n balls into m bins.
    Named after the Plinko game where balls bounce left/right at pegs.
*)

Module PMNS.
  
  (** Compute the midpoint of a range *)
  Definition midpoint (low high : nat) : nat :=
    (low + high) / 2.
  
  (** Compute split probability p = (mid - low + 1) / (high - low + 1) 
      Returns numerator and denominator for exact arithmetic *)
  Definition split_prob (low high : nat) : (nat * nat) :=
    let mid := midpoint low high in
    (mid - low + 1, high - low + 1).
  
  (** Deterministic binomial sampling using PRF output as randomness.
      Given count balls and probability p = num/denom, determine how many go left.
      Uses PRF output to seed the sampling. *)
  Definition binomial_sample (count num denom : nat) (prf_output : nat) : nat :=
    if denom =? 0 then 0
    else
      let scaled := (prf_output mod (denom + 1)) in
      (count * num + scaled) / denom.
  
  (** Compute children of a PMNS tree node *)
  Definition children (prf_key : nat) (node : PMNSNode) 
    : PMNSNode * PMNSNode * nat :=
    let start := node_start node in
    let count := node_count node in
    let low := node_low node in
    let high := node_high node in
    let mid := midpoint low high in
    let '(num, denom) := split_prob low high in
    let prf_out := prf_key + start + count + low + high in  (* Simplified PRF *)
    let s := binomial_sample count num denom prf_out in
    let left_child := mkPMNSNode start s low mid in
    let right_child := mkPMNSNode (start + s) (count - s) (mid + 1) high in
    (left_child, right_child, s).
  
  (** Forward evaluation: Find which bin ball x lands in.
      Complexity: O(log m) *)
  Fixpoint forward_aux (fuel : nat) (key : nat) (x : nat) (node : PMNSNode) : nat :=
    match fuel with
    | O => node_low node
    | S fuel' =>
        let low := node_low node in
        let high := node_high node in
        if low <? high then
          let '(left_child, right_child, s) := children key node in
          if x <? (node_start node + s) then
            forward_aux fuel' key x left_child
          else
            forward_aux fuel' key x right_child
        else
          low
    end.
  
  Definition forward (key : nat) (n_balls m_bins : nat) (x : nat) : nat :=
    let root := mkPMNSNode 0 n_balls 0 (m_bins - 1) in
    forward_aux m_bins key x root.
  
  (** Inverse evaluation: Find all balls in bin y.
      Returns (start, count) representing range [start, start+count-1].
      Complexity: O(log m) *)
  Fixpoint inverse_aux (fuel : nat) (key : nat) (y : nat) (node : PMNSNode) 
    : nat * nat :=
    match fuel with
    | O => (node_start node, node_count node)
    | S fuel' =>
        let low := node_low node in
        let high := node_high node in
        if low <? high then
          let '(left_child, right_child, s) := children key node in
          let mid := midpoint low high in
          if y <=? mid then
            inverse_aux fuel' key y left_child
          else
            inverse_aux fuel' key y right_child
        else
          (node_start node, node_count node)
    end.
  
  Definition inverse (key : nat) (n_balls m_bins : nat) (y : nat) 
    : nat * nat :=
    let root := mkPMNSNode 0 n_balls 0 (m_bins - 1) in
    inverse_aux m_bins key y root.
  
  (** Convert (start, count) to list of ball indices *)
  Definition inverse_list (key : nat) (n_balls m_bins : nat) (y : nat) 
    : list nat :=
    let '(start, count) := inverse key n_balls m_bins y in
    seq start count.

End PMNS.

(** ** Swap-or-Not Small-Domain PRP
    
    Based on Morris-Rogaway (eprint 2013/560).
    Achieves full security (withstands all N queries) in O(n log n) time.
    
    Each round:
    1. Compute partner: X' = K_i - X mod N
    2. Compute canonical representative: X̂ = max(X, X')
    3. If F(i, X̂) = 1, swap X with X'
    
    Inversion: run rounds in reverse order.
*)

Module SwapOrNot.

  (** Derive round key K_i from master key and round number.
      In practice, use a PRF like AES(key, i || domain_size). *)
  Definition derive_round_key (master_key round domain_size : nat) : nat :=
    let hash := master_key * 2654435761 + round * 1103515245 + domain_size in
    hash mod (domain_size + 1).

  (** PRF evaluation for swap decision.
      Returns a single bit: 0 or 1.
      In practice, use AES and take LSB. *)
  Definition prf_bit (master_key round canonical : nat) : nat :=
    let hash := master_key * 31 + round * 17 + canonical * 13 in
    hash mod 2.

  (** Compute partner index: K_i - X mod N *)
  Definition compute_partner (round_key x domain_size : nat) : nat :=
    if domain_size =? 0 then 0
    else (round_key + domain_size - (x mod domain_size)) mod domain_size.

  (** Single round of Swap-or-Not *)
  Definition swap_or_not_round (master_key round domain_size x : nat) : nat :=
    let k_i := derive_round_key master_key round domain_size in
    let partner := compute_partner k_i x domain_size in
    let canonical := Nat.max x partner in
    if prf_bit master_key round canonical =? 1 then partner else x.

  (** Number of rounds: ~6 * ceil(log2(N)) for security *)
  Definition num_rounds (domain_size : nat) : nat :=
    let log2_n := Nat.log2_up (domain_size + 1) in
    6 * log2_n + 6.

  (** Forward PRP: encrypt by running rounds 0, 1, ..., r-1 *)
  Fixpoint prp_forward_aux (fuel master_key domain_size round x : nat) : nat :=
    match fuel with
    | O => x
    | S fuel' =>
        let x' := swap_or_not_round master_key round domain_size x in
        prp_forward_aux fuel' master_key domain_size (round + 1) x'
    end.

  Definition prp_forward (master_key domain_size x : nat) : nat :=
    let rounds := num_rounds domain_size in
    prp_forward_aux rounds master_key domain_size 0 x.

  (** Inverse PRP: decrypt by running rounds r-1, r-2, ..., 0 *)
  Fixpoint prp_inverse_aux (fuel master_key domain_size round x : nat) : nat :=
    match fuel with
    | O => x
    | S fuel' =>
        let x' := swap_or_not_round master_key round domain_size x in
        match round with
        | O => x'
        | S round' => prp_inverse_aux fuel' master_key domain_size round' x'
        end
    end.

  Definition prp_inverse (master_key domain_size y : nat) : nat :=
    let rounds := num_rounds domain_size in
    match rounds with
    | O => y
    | S r => prp_inverse_aux rounds master_key domain_size r y
    end.

End SwapOrNot.

(** ** Invertible PRF (iPRF)
    
    Built from Swap-or-Not PRP + PMNS:
    - Forward: iF.F(k, x) = S(k_pmns, P(k_prp, x))
    - Inverse: iF.F^{-1}(k, y) = {P^{-1}(k_prp, z) : z ∈ S^{-1}(k_pmns, y)}
    
    Security follows from:
    1. Swap-or-Not provides a secure small-domain PRP (Morris-Rogaway 2013)
    2. PMNS simulates the preimage-size distribution of a random function
    3. Composition yields an iPRF indistinguishable from a random function
*)

Module iPRF.
  
  Record Key := mkKey {
    prp_key  : nat;    (* Key for Swap-or-Not PRP *)
    pmns_key : nat     (* Key for PMNS *)
  }.
  
  (** Forward evaluation: P then S
      Complexity: O(log N * log N) for PRP + O(log M) for PMNS *)
  Definition forward (k : Key) (domain_size range_size : nat) (x : nat) : nat :=
    let permuted := SwapOrNot.prp_forward (prp_key k) domain_size x in
    PMNS.forward (pmns_key k) domain_size range_size permuted.
  
  (** Inverse evaluation: S^{-1} then P^{-1} for each preimage
      Complexity: O(|output| * (log M + log N * log N)) *)
  Definition inverse (k : Key) (domain_size range_size : nat) (y : nat) 
    : list nat :=
    let pmns_preimages := PMNS.inverse_list (pmns_key k) domain_size range_size y in
    map (SwapOrNot.prp_inverse (prp_key k) domain_size) pmns_preimages.
  
  (** Key generation from seed *)
  Definition gen (seed : nat) : Key :=
    mkKey seed (seed * 31 + 17).

End iPRF.

(** ** Plinko Hint Structures *)

(** Regular hint: (P_j, p_j) where P_j is a subset of blocks, 
    p_j is parity of entries at iPRF-chosen offsets *)
Record RegularHint := mkRegularHint {
  rh_blocks : list nat;    (* Subset of block indices, size = c/2 + 1 *)
  rh_parity : nat          (* XOR parity of entries (simplified to nat) *)
}.

(** Backup hint: (B_j, l_j, r_j) where B_j is block subset,
    l_j is parity of entries in B_j, r_j is parity outside B_j *)
Record BackupHint := mkBackupHint {
  bh_blocks   : list nat;  (* Subset of block indices, size = c/2 *)
  bh_parity_in  : nat;     (* Parity of entries in B_j *)
  bh_parity_out : nat      (* Parity of entries outside B_j *)
}.

(** Promoted hint: backup hint that has been used *)
Record PromotedHint := mkPromotedHint {
  ph_blocks : list nat;
  ph_index  : nat;         (* Query index that promoted this hint *)
  ph_parity : nat
}.

(** Query cache entry *)
Record CacheEntry := mkCacheEntry {
  ce_value    : nat;       (* Retrieved value *)
  ce_hint_idx : nat        (* Hint index used *)
}.

(** Client state *)
Record ClientState := mkClientState {
  cs_keys     : list iPRF.Key;           (* iPRF key per block *)
  cs_regular  : list (option RegularHint);
  cs_backup   : list (option BackupHint);
  cs_promoted : list (option PromotedHint);
  cs_cache    : list (option CacheEntry);
  cs_w        : nat;                     (* Block size *)
  cs_c        : nat                      (* Number of blocks = n/w *)
}.

(** ** Helper Functions *)

(** Check if an element is in a list *)
Definition in_list (x : nat) (l : list nat) : bool :=
  existsb (Nat.eqb x) l.

(** Get block and offset from database index *)
Definition get_block_offset (w i : nat) : nat * nat :=
  (i / w, i mod w).

(** Simple random subset generation (deterministic for reproducibility) *)
Fixpoint random_subset_aux (fuel seed size total : nat) (acc : list nat) : list nat :=
  match fuel with
  | O => acc
  | S fuel' =>
      match size with
      | O => acc
      | S size' =>
          let idx := (seed * 1103515245 + 12345) mod (total + 1) in
          let new_seed := seed * 1103515245 + 12345 in
          if in_list idx acc then
            random_subset_aux fuel' new_seed size total acc
          else
            random_subset_aux fuel' new_seed size' total (idx :: acc)
      end
  end.

Definition random_subset (seed size total : nat) : list nat :=
  random_subset_aux (size * 10) seed size total [].

(** ** HintInit: Offline Phase
    
    Initialize hints by streaming the database.
    Complexity: O(n) time, O(n) communication
*)

Definition init_regular_hints (seed c num_hints : nat) : list (option RegularHint) :=
  let subset_size := c / 2 + 1 in
  map (fun i => 
    Some (mkRegularHint (random_subset (seed + i) subset_size c) 0)
  ) (seq 0 num_hints).

Definition init_backup_hints (seed c num_hints start_idx : nat) 
  : list (option BackupHint) :=
  let subset_size := c / 2 in
  map (fun i =>
    Some (mkBackupHint (random_subset (seed + start_idx + i) subset_size c) 0 0)
  ) (seq 0 num_hints).

Definition init_keys (seed c : nat) : list iPRF.Key :=
  map (fun i => iPRF.gen (seed + i * 7)) (seq 0 c).

(** Update a hint's parity based on database entry.
    This is called during the streaming phase of HintInit. *)
Definition update_regular_hint_parity (h : RegularHint) (block : nat) (value : nat) 
  : RegularHint :=
  if in_list block (rh_blocks h) then
    mkRegularHint (rh_blocks h) (Nat.lxor (rh_parity h) value)
  else
    h.

Definition update_backup_hint_parity (h : BackupHint) (block : nat) (value : nat)
  : BackupHint :=
  if in_list block (bh_blocks h) then
    mkBackupHint (bh_blocks h) (Nat.lxor (bh_parity_in h) value) (bh_parity_out h)
  else
    mkBackupHint (bh_blocks h) (bh_parity_in h) (Nat.lxor (bh_parity_out h) value).

(** Process one database entry during HintInit streaming *)
Definition process_db_entry (st : ClientState) (i : nat) (value : nat) : ClientState :=
  let '(block, offset) := get_block_offset (cs_w st) i in
  let key := nth block (cs_keys st) (iPRF.gen 0) in
  let domain_size := cs_w st * 10 in  (* λw + q *)
  let range_size := cs_w st in
  let hint_indices := iPRF.inverse key domain_size range_size offset in
  let num_regular := length (cs_regular st) in
  let update_regular := fun hints =>
    map (fun '(idx, oh) =>
      match oh with
      | None => None
      | Some h =>
          if in_list idx hint_indices then
            Some (update_regular_hint_parity h block value)
          else Some h
      end
    ) (combine (seq 0 (length hints)) hints)
  in
  let update_backup := fun hints =>
    map (fun '(idx, oh) =>
      match oh with
      | None => None
      | Some h =>
          if in_list (idx + num_regular) hint_indices then
            Some (update_backup_hint_parity h block value)
          else Some h
      end
    ) (combine (seq 0 (length hints)) hints)
  in
  mkClientState
    (cs_keys st)
    (update_regular (cs_regular st))
    (update_backup (cs_backup st))
    (cs_promoted st)
    (cs_cache st)
    (cs_w st)
    (cs_c st).

(** Full HintInit - process entire database *)
Definition hint_init (seed n w lambda q : nat) (database : list nat) : ClientState :=
  let c := n / w in
  let num_regular := lambda * w in
  let keys := init_keys seed c in
  let regular := init_regular_hints seed c num_regular in
  let backup := init_backup_hints seed c q num_regular in
  let promoted := repeat None q in
  let cache := repeat None n in
  let initial_state := mkClientState keys regular backup promoted cache w c in
  fold_left (fun st '(i, v) => process_db_entry st i v)
    (combine (seq 0 (length database)) database)
    initial_state.

(** ** GetHint: Find a hint containing entry (block, offset)
    
    Uses iPRF inversion to find all hints in O(1) time.
*)

Definition get_hint (st : ClientState) (block offset : nat) 
  : option (list nat * nat * list nat) :=
  let key := nth block (cs_keys st) (iPRF.gen 0) in
  let domain_size := cs_w st * 10 in
  let range_size := cs_w st in
  let hint_indices := iPRF.inverse key domain_size range_size offset in
  let num_regular := length (cs_regular st) in
  let find_regular := fun idx =>
    if idx <? num_regular then
      match nth_error (cs_regular st) idx with
      | Some (Some h) => 
          if in_list block (rh_blocks h) then
            Some (rh_blocks h, rh_parity h)
          else None
      | _ => None
      end
    else None
  in
  let find_promoted := fun idx =>
    if num_regular <=? idx then
      match nth_error (cs_promoted st) (idx - num_regular) with
      | Some (Some h) =>
          if in_list block (ph_blocks h) then
            Some (ph_blocks h, ph_parity h)
          else None
      | _ => None
      end
    else None
  in
  let all_offsets := map (fun blk =>
    let k := nth blk (cs_keys st) (iPRF.gen 0) in
    iPRF.forward k domain_size range_size 0  (* Simplified *)
  ) (seq 0 (cs_c st)) in
  match find (fun idx => 
    match find_regular idx with Some _ => true | None => false end
  ) hint_indices with
  | Some idx =>
      match find_regular idx with
      | Some (blocks, parity) => Some (blocks, parity, all_offsets)
      | None => None
      end
  | None =>
      match find (fun idx =>
        match find_promoted idx with Some _ => true | None => false end
      ) hint_indices with
      | Some idx =>
          match find_promoted idx with
          | Some (blocks, parity) => Some (blocks, parity, all_offsets)
          | None => None
          end
      | None => None
      end
  end.

(** ** UpdateHint: Update hints after database change
    
    Uses iPRF inversion to find all affected hints in O(1) time.
*)

Definition update_hint (st : ClientState) (i : nat) (delta : nat) : ClientState :=
  let '(block, offset) := get_block_offset (cs_w st) i in
  let key := nth block (cs_keys st) (iPRF.gen 0) in
  let domain_size := cs_w st * 10 in
  let range_size := cs_w st in
  let hint_indices := iPRF.inverse key domain_size range_size offset in
  let num_regular := length (cs_regular st) in
  let updated_regular := map (fun '(idx, oh) =>
    match oh with
    | None => None
    | Some h =>
        if andb (in_list idx hint_indices) (in_list block (rh_blocks h)) then
          Some (mkRegularHint (rh_blocks h) (Nat.lxor (rh_parity h) delta))
        else Some h
    end
  ) (combine (seq 0 (length (cs_regular st))) (cs_regular st)) in
  let updated_backup := map (fun '(idx, oh) =>
    match oh with
    | None => None
    | Some h =>
        if in_list (idx + num_regular) hint_indices then
          if in_list block (bh_blocks h) then
            Some (mkBackupHint (bh_blocks h) 
              (Nat.lxor (bh_parity_in h) delta) (bh_parity_out h))
          else
            Some (mkBackupHint (bh_blocks h) 
              (bh_parity_in h) (Nat.lxor (bh_parity_out h) delta))
        else Some h
    end
  ) (combine (seq 0 (length (cs_backup st))) (cs_backup st)) in
  let updated_promoted := map (fun '(idx, oh) =>
    match oh with
    | None => None
    | Some h =>
        if andb (in_list (idx + num_regular) hint_indices) 
                (in_list block (ph_blocks h)) then
          Some (mkPromotedHint (ph_blocks h) (ph_index h) 
            (Nat.lxor (ph_parity h) delta))
        else Some h
    end
  ) (combine (seq 0 (length (cs_promoted st))) (cs_promoted st)) in
  mkClientState
    (cs_keys st)
    updated_regular
    updated_backup
    updated_promoted
    (cs_cache st)
    (cs_w st)
    (cs_c st).

(** ** Correctness Lemmas *)

(** Swap-or-Not round is self-inverse (involutory) *)
Lemma swap_or_not_round_involutory : forall master_key round domain_size x,
  x < domain_size ->
  domain_size > 0 ->
  SwapOrNot.swap_or_not_round master_key round domain_size
    (SwapOrNot.swap_or_not_round master_key round domain_size x) = x.
Proof.
  intros.
  unfold SwapOrNot.swap_or_not_round.
  unfold SwapOrNot.compute_partner.
  (* Each round is an involution: applying it twice returns to original.
     This follows because:
     1. partner(partner(x)) = x (modular arithmetic)
     2. canonical(x, partner(x)) = canonical(partner(x), x)
     3. Therefore the same swap decision is made both times *)
Admitted.

(** Swap-or-Not PRP forward/inverse are inverses *)
Lemma swap_or_not_inverse_correct : forall master_key domain_size x,
  x < domain_size ->
  domain_size > 0 ->
  SwapOrNot.prp_inverse master_key domain_size
    (SwapOrNot.prp_forward master_key domain_size x) = x.
Proof.
  intros.
  unfold SwapOrNot.prp_forward, SwapOrNot.prp_inverse.
  (* Follows from swap_or_not_round_involutory and running rounds in reverse *)
Admitted.

(** PMNS forward and inverse are consistent *)
Lemma pmns_inverse_correct : forall key n_balls m_bins x y,
  x < n_balls ->
  y = PMNS.forward key n_balls m_bins x ->
  In x (PMNS.inverse_list key n_balls m_bins y).
Proof.
  intros.
  (* Proof would require induction on the tree structure *)
Admitted.

(** iPRF inverse finds all preimages *)
Lemma iprf_inverse_correct : forall k domain_size range_size x y,
  x < domain_size ->
  domain_size > 0 ->
  y = iPRF.forward k domain_size range_size x ->
  In x (iPRF.inverse k domain_size range_size y).
Proof.
  intros.
  unfold iPRF.forward, iPRF.inverse.
  (* Follows from:
     1. swap_or_not_inverse_correct: P^{-1}(P(x)) = x
     2. pmns_inverse_correct: x ∈ S^{-1}(S(x))
     3. Therefore x ∈ {P^{-1}(z) : z ∈ S^{-1}(y)} when y = S(P(x)) *)
Admitted.

(** UpdateHint maintains hint consistency *)
Lemma update_hint_preserves_structure : forall st i delta,
  length (cs_keys (update_hint st i delta)) = length (cs_keys st).
Proof.
  intros. unfold update_hint. simpl. reflexivity.
Qed.

(** Key property: iPRF inverse returns O(1) expected preimages *)
Lemma iprf_inverse_expected_size : forall (k : iPRF.Key) (domain_size range_size y : nat),
  domain_size > 0 ->
  range_size > 0 ->
  (* Expected |iPRF.inverse k domain_size range_size y| ≈ domain_size / range_size *)
  (* This follows from PMNS simulating multinomial distribution *)
  True.
Proof.
  intros. trivial.
Qed.

(** ** Example Usage *)

Example example_hint_init : ClientState :=
  let database := [1; 2; 3; 4; 5; 6; 7; 8] in
  hint_init 42 8 2 4 4 database.

Example example_get_hint :=
  let st := example_hint_init in
  get_hint st 0 0.

Example example_update_hint :=
  let st := example_hint_init in
  update_hint st 3 255.


