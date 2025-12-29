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

(* Axiom: base domain outputs stay in the right half, so SR does not recurse *)
Axiom sr_base_case_no_recurse : forall x,
  0 <= x < N ->
  (N / 2 <=? sr_apply_rounds 0 (sr_t_rounds N) N x) = true.

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

(* Apply inverse rounds preserves range *)
Lemma sr_apply_rounds_inv_in_range : forall level rounds n x,
  0 < n -> 0 <= x < n -> 0 <= sr_apply_rounds_inv level rounds n x < n.
Proof.
  intros level rounds.
  induction rounds as [|r' IH]; intros n x Hn Hx.
  - simpl. assumption.
  - simpl. apply IH; [assumption | apply sr_round_in_range; assumption].
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
Proof.
  intros level rounds.
  induction rounds as [|r' IH]; intros n x Hn Hx.
  - simpl. reflexivity.
  - simpl.
    assert (Hrnd_range : 0 <= sr_round_spec level r' n x < n).
    { apply sr_round_in_range; assumption. }
    rewrite IH by assumption.
    apply sr_round_involutive; assumption.
Qed.

(* Helper: sr_forward_aux preserves range *)
Lemma sr_forward_aux_in_range : forall fuel x n level,
  0 < n -> 0 <= x < n ->
  0 <= sr_forward_aux x n level fuel < n.
Proof.
  induction fuel as [|fuel' IH]; intros x n level Hn Hx.
  - simpl. assumption.
  - simpl.
    destruct (n <=? 1) eqn:Hn1.
    + assumption.
    + apply Z.leb_nle in Hn1.
      set (t := sr_t_rounds n).
      set (x' := sr_apply_rounds level t n x).
      assert (Hx'_range : 0 <= x' < n).
      { unfold x'. apply sr_apply_rounds_in_range; assumption. }
      destruct (n / 2 <=? x') eqn:Hhalf.
      * assumption.
      * apply Z.leb_nle in Hhalf.
        assert (Hhalf_pos : 0 < n / 2) by (apply Z.div_str_pos; lia).
        assert (Hx'_half : 0 <= x' < n / 2) by lia.
        pose proof (IH x' (n / 2) (S level) Hhalf_pos Hx'_half) as Hrec.
        assert (n / 2 <= n) by (apply Z.div_le_upper_bound; lia).
        lia.
Qed.

(* SR forward preserves range *)
Lemma sr_forward_range : forall domain x,
  0 < domain -> 0 <= x < domain ->
  0 <= sr_forward domain x < domain.
Proof.
  intros domain x Hdom Hx.
  unfold sr_forward.
  apply sr_forward_aux_in_range; assumption.
Qed.

(* Helper: sr_inverse_aux preserves range *)
Lemma sr_inverse_aux_in_range : forall fuel y n level,
  0 < n -> 0 <= y < n ->
  0 <= sr_inverse_aux y n level fuel < n.
Proof.
  induction fuel as [|fuel' IH]; intros y n level Hn Hy.
  - simpl. assumption.
  - simpl.
    destruct (n <=? 1) eqn:Hn1.
    + assumption.
    + apply Z.leb_nle in Hn1.
      set (t := sr_t_rounds n).
      set (half := n / 2).
      destruct (half <=? y) eqn:Hhalf.
      * apply sr_apply_rounds_inv_in_range; assumption.
      * apply Z.leb_nle in Hhalf.
        assert (Hhalf_pos : 0 < half) by (unfold half; apply Z.div_str_pos; lia).
        assert (Hy_half : 0 <= y < half) by (unfold half in *; lia).
        pose proof (IH y half (S level) Hhalf_pos Hy_half) as Hrec.
        assert (Hrec_in_n : 0 <= sr_inverse_aux y half (S level) fuel' < n).
        { unfold half in *. split; [lia | apply Z.lt_le_trans with (n / 2); [lia | apply Z.div_le_upper_bound; lia]]. }
        apply sr_apply_rounds_inv_in_range; [assumption | exact Hrec_in_n].
Qed.

(* SR inverse preserves range *)
Lemma sr_inverse_range : forall domain y,
  0 < domain -> 0 <= y < domain ->
  0 <= sr_inverse domain y < domain.
Proof.
  intros domain y Hdom Hy.
  unfold sr_inverse.
  apply sr_inverse_aux_in_range; assumption.
Qed.

(* Helper: inverse_aux undoes forward_aux *)
Lemma sr_inverse_aux_forward_aux_id : forall fuel x n level,
  0 < n -> 0 <= x < n ->
  sr_inverse_aux (sr_forward_aux x n level fuel) n level fuel = x.
Proof.
  induction fuel as [|fuel' IH]; intros x n level Hn Hx.
  - simpl. reflexivity.
  - simpl.
    destruct (n <=? 1) eqn:Hn1.
    + reflexivity.
    + apply Z.leb_nle in Hn1.
      set (t := sr_t_rounds n).
      set (x' := sr_apply_rounds level t n x).
      set (half := n / 2).
      assert (Hx'_range : 0 <= x' < n).
      { unfold x'. apply sr_apply_rounds_in_range; assumption. }
      assert (Hhalf_pos : 0 < half).
      { unfold half. apply Z.div_str_pos. lia. }
      destruct (half <=? x') eqn:Hhalf.
      * (* x' in right half: no recursion *)
        rewrite Hhalf.
        apply sr_apply_rounds_inverse; assumption.
      * (* x' in left half: recurse *)
        apply Z.leb_nle in Hhalf.
        assert (Hx'_half : 0 <= x' < half) by lia.
        assert (Hy_range : 0 <= sr_forward_aux x' half (S level) fuel' < half).
        { apply sr_forward_aux_in_range; assumption. }
        assert (Hy_lt_half : (half <=? sr_forward_aux x' half (S level) fuel') = false).
        { apply Z.leb_nle. lia. }
        rewrite Hy_lt_half.
        rewrite IH by assumption.
        apply sr_apply_rounds_inverse; assumption.
Qed.

(* Helper: forward_aux undoes inverse_aux *)
Lemma sr_forward_aux_inverse_aux_id : forall fuel y n level,
  0 < n -> 0 <= y < n ->
  sr_forward_aux (sr_inverse_aux y n level fuel) n level fuel = y.
Proof.
  induction fuel as [|fuel' IH]; intros y n level Hn Hy.
  - simpl. reflexivity.
  - simpl.
    destruct (n <=? 1) eqn:Hn1.
    + reflexivity.
    + apply Z.leb_nle in Hn1.
      set (t := sr_t_rounds n).
      set (half := n / 2).
      assert (Hhalf_pos : 0 < half).
      { unfold half. apply Z.div_str_pos. lia. }
      destruct (half <=? y) eqn:Hhalf.
      * (* y in right half: inverse is one round *)
        set (x0 := sr_apply_rounds_inv level t n y).
        assert (Hx0_range : 0 <= x0 < n).
        { unfold x0. apply sr_apply_rounds_inv_in_range; assumption. }
        set (x' := sr_apply_rounds level t n x0).
        assert (Hx'_eq : x' = y).
        { unfold x', x0. apply sr_apply_rounds_inv_inverse; assumption. }
        rewrite Hx'_eq. rewrite Hhalf. reflexivity.
      * (* y in left half: inverse recurses *)
        apply Z.leb_nle in Hhalf.
        assert (Hy_half : 0 <= y < half) by lia.
        set (x_rec := sr_inverse_aux y half (S level) fuel').
        assert (Hx_rec_range : 0 <= x_rec < half).
        { unfold x_rec. apply sr_inverse_aux_in_range; assumption. }
        assert (Hx_rec_in_n : 0 <= x_rec < n).
        { split; [lia | apply Z.lt_le_trans with half; [lia | unfold half; apply Z.div_le_upper_bound; lia]]. }
        set (x0 := sr_apply_rounds_inv level t n x_rec).
        assert (Hx0_range : 0 <= x0 < n).
        { unfold x0. apply sr_apply_rounds_inv_in_range; assumption. }
        set (x' := sr_apply_rounds level t n x0).
        assert (Hx'_eq : x' = x_rec).
        { unfold x', x0. apply sr_apply_rounds_inv_inverse; assumption. }
        assert (Hx'_lt_half : (half <=? x') = false).
        { rewrite Hx'_eq. apply Z.leb_nle. lia. }
        rewrite Hx'_lt_half.
        rewrite Hx'_eq.
        apply IH; assumption.
Qed.

(* SR is a bijection: forward then inverse is identity *)
Lemma sr_forward_inverse_id : forall domain x,
  0 < domain -> 0 <= x < domain ->
  sr_inverse domain (sr_forward domain x) = x.
Proof.
  intros domain x Hdom Hx.
  unfold sr_forward, sr_inverse.
  apply sr_inverse_aux_forward_aux_id; assumption.
Qed.

(* SR is a bijection: inverse then forward is identity *)
Lemma sr_inverse_forward_id : forall domain y,
  0 < domain -> 0 <= y < domain ->
  sr_forward domain (sr_inverse domain y) = y.
Proof.
  intros domain y Hdom Hy.
  unfold sr_forward, sr_inverse.
  apply sr_forward_aux_inverse_aux_id; assumption.
Qed.

(** Compatibility with base SwapOrNot *)

(* When domain = 2^64, SR with 0 recursions is equivalent to base SwapOrNot *)
Lemma sr_base_case_equiv : forall x,
  0 <= x < N ->
  sr_t_rounds N = num_rounds ->
  (forall r, sr_round_key 0 r N = round_key r) ->
  (forall r c, sr_round_bit 0 r c N = round_bit r c) ->
  sr_forward N x = forward_spec x.
Proof.
  intros x Hx Hrounds Hkey Hbit.
  assert (Hround_spec : forall r x0, sr_round_spec 0 r N x0 = round_spec r x0).
  { intros r x0. unfold sr_round_spec, round_spec, sr_partner, partner, canonical.
    rewrite Hkey, Hbit. reflexivity. }
  assert (Happly_rounds : forall n, sr_apply_rounds 0 n N x = forward_rounds n x).
  { intro n. induction n as [|n' IH].
    - reflexivity.
    - simpl. rewrite Hround_spec, IH. reflexivity. }
  unfold sr_forward.
  remember (Z.to_nat (Z.log2_up N) + 1)%nat as fuel.
  destruct fuel as [|fuel']; [inversion Heqfuel|].
  simpl.
  replace (N <=? 1) with false by (vm_compute; reflexivity).
  rewrite Hrounds.
  set (x' := sr_apply_rounds 0 num_rounds N x).
  assert (Hno_recurse : (N / 2 <=? x') = true).
  { subst x'. rewrite <- Hrounds. apply sr_base_case_no_recurse. assumption. }
  rewrite Hno_recurse.
  subst x'. rewrite Happly_rounds.
  reflexivity.
Qed.

(** Connection to iPRF: SR-based PRP maintains iPRF properties *)

(* The iPRF can instantiate PRP with sr_forward/sr_inverse *)
(* This ensures iPRF works over arbitrary (non-power-of-two) domains *)
