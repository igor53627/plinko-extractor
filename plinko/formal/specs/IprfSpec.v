(** * IprfSpec: Specification of the Invertible PRF (iPRF) *)
(**
   The iPRF combines:
   - SwapOrNot PRP (P): a small-domain pseudorandom permutation
   - PMNS (S): Pseudorandom Multinomial Sampler via trace_ball

   Forward: iF.F(k, x) = S(k_pmns, P(k_prp, x))
   Inverse: iF.F^{-1}(k, y) = {P^{-1}(k_prp, z) : z in S^{-1}(k_pmns, y)}
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import Plinko.Specs.CommonTypes.
Require Import Plinko.Specs.BinomialSpec.
Require Import Plinko.Specs.SwapOrNotSrSpec.

Import ListNotations.
Open Scope Z_scope.

(** ** Abstract parameters *)

Section IprfParams.

(** PRF for node evaluation in PMNS tree *)
Parameter prf_eval : Z -> Z.

(** Node ID encoding: (low, high, n) -> node_id *)
Parameter encode_node : Z -> Z -> Z -> Z.

(** PRP forward permutation - instantiated via SwapOrNot SR *)
Definition prp_forward (n x : Z) : Z := sr_forward n x.

(** PRP inverse permutation - instantiated via SwapOrNot SR *)
Definition prp_inverse (n y : Z) : Z := sr_inverse n y.

(** PRP lemmas: PRP is a valid permutation on [0, n) - proved via SR *)
Lemma prp_forward_in_range : forall n x,
  0 <= x < n ->
  0 <= prp_forward n x < n.
Proof.
  intros n x Hx.
  unfold prp_forward.
  apply sr_forward_range; lia.
Qed.

Lemma prp_inverse_in_range : forall n x,
  0 <= x < n ->
  0 <= prp_inverse n x < n.
Proof.
  intros n x Hx.
  unfold prp_inverse.
  apply sr_inverse_range; lia.
Qed.

Lemma prp_forward_inverse : forall n x,
  0 <= x < n ->
  prp_inverse n (prp_forward n x) = x.
Proof.
  intros n x Hx.
  unfold prp_forward, prp_inverse.
  apply sr_forward_inverse_id; lia.
Qed.

Lemma prp_inverse_forward : forall n x,
  0 <= x < n ->
  prp_forward n (prp_inverse n x) = x.
Proof.
  intros n x Hx.
  unfold prp_forward, prp_inverse.
  apply sr_inverse_forward_id; lia.
Qed.

(** ** PMNS: Pseudorandom Multinomial Sampler *)

(** State for trace_ball computation *)
Record trace_state : Type := mkTraceState {
  ts_low : Z;
  ts_high : Z;
  ts_ball_count : Z;
  ts_ball_index : Z
}.

(** Single step of trace_ball loop *)
Definition trace_ball_step (st : trace_state) : trace_state :=
  let low := ts_low st in
  let high := ts_high st in
  let ball_count := ts_ball_count st in
  let ball_index := ts_ball_index st in
  let mid := (low + high) / 2 in
  let left_bins := mid - low + 1 in
  let total_bins := high - low + 1 in
  let node_id := encode_node low high ball_count in
  let prf_output := prf_eval node_id in
  let left_count := binomial_sample_spec ball_count left_bins total_bins prf_output in
  if ball_index <? left_count then
    mkTraceState low mid left_count ball_index
  else
    mkTraceState (mid + 1) high (ball_count - left_count) (ball_index - left_count).

(** Fuel-based fixpoint for trace_ball (mirrors the while loop) *)
Fixpoint trace_ball_fuel (fuel : nat) (st : trace_state) : Z :=
  match fuel with
  | O => ts_low st
  | S fuel' =>
      if ts_low st <? ts_high st then
        trace_ball_fuel fuel' (trace_ball_step st)
      else
        ts_low st
  end.

(** trace_ball specification: determines which bin a ball falls into *)
Definition trace_ball_spec (x_prime n m : Z) : Z :=
  if Z.eqb m 1 then
    0
  else
    let initial_state := mkTraceState 0 (m - 1) n x_prime in
    let fuel := Z.to_nat (2 * m) in
    trace_ball_fuel fuel initial_state.

(** ** PMNS Inverse: trace_ball_inverse *)

(** State for trace_ball_inverse computation *)
Record trace_inv_state : Type := mkTraceInvState {
  tis_low : Z;
  tis_high : Z;
  tis_ball_count : Z;
  tis_ball_start : Z
}.

(** Single step of trace_ball_inverse loop *)
Definition trace_ball_inverse_step (y : Z) (st : trace_inv_state) : trace_inv_state :=
  let low := tis_low st in
  let high := tis_high st in
  let ball_count := tis_ball_count st in
  let ball_start := tis_ball_start st in
  let mid := (low + high) / 2 in
  let left_bins := mid - low + 1 in
  let total_bins := high - low + 1 in
  let node_id := encode_node low high ball_count in
  let prf_output := prf_eval node_id in
  let left_count := binomial_sample_spec ball_count left_bins total_bins prf_output in
  if y <=? mid then
    mkTraceInvState low mid left_count ball_start
  else
    mkTraceInvState (mid + 1) high (ball_count - left_count) (ball_start + left_count).

(** Fuel-based fixpoint for trace_ball_inverse *)
Fixpoint trace_ball_inverse_fuel (fuel : nat) (y : Z) (st : trace_inv_state) : (Z * Z) :=
  match fuel with
  | O => (tis_ball_start st, tis_ball_count st)
  | S fuel' =>
      if tis_low st <? tis_high st then
        trace_ball_inverse_fuel fuel' y (trace_ball_inverse_step y st)
      else
        (tis_ball_start st, tis_ball_count st)
  end.

(** Generate list [start, start+1, ..., start+count-1] *)
Fixpoint range_list (start count : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => nil
  | S fuel' =>
      if count <=? 0 then
        nil
      else
        start :: range_list (start + 1) (count - 1) fuel'
  end.

(** trace_ball_inverse specification: returns all ball indices that map to bin y *)
Definition trace_ball_inverse_spec (y n m : Z) : list Z :=
  if Z.eqb m 1 then
    range_list 0 n (Z.to_nat n)
  else
    let initial_state := mkTraceInvState 0 (m - 1) n 0 in
    let fuel := Z.to_nat (2 * m) in
    let '(start, count) := trace_ball_inverse_fuel fuel y initial_state in
    range_list start count (Z.to_nat count).

(** ** iPRF Forward and Inverse *)

(** iPRF forward: apply PRP then PMNS *)
Definition iprf_forward_spec (x n m : Z) : Z :=
  if (x <? 0) || (n <=? x) then
    0
  else
    let permuted := prp_forward n x in
    trace_ball_spec permuted n m.

(** iPRF inverse: find PMNS preimages then apply inverse PRP to each *)
Definition iprf_inverse_spec (y n m : Z) : list Z :=
  if (y <? 0) || (m <=? y) then
    nil
  else
    let pmns_preimages := trace_ball_inverse_spec y n m in
    map (prp_inverse n) pmns_preimages.

(** ** Lemmas for trace_ball_step *)

(** Auxiliary lemma: mid is in range *)
Lemma mid_in_range : forall low high : Z,
  low <= high ->
  low <= (low + high) / 2 <= high.
Proof.
  intros low high Hle.
  split.
  - apply Z.div_le_lower_bound; lia.
  - apply Z.div_le_upper_bound; lia.
Qed.

(** Auxiliary lemma: left branch shrinks range (when low < high) *)
Lemma left_branch_shrinks : forall low high : Z,
  low < high ->
  (low + high) / 2 - low < high - low.
Proof.
  intros low high Hlt.
  assert (Hmid : (low + high) / 2 < high).
  { apply Z.div_lt_upper_bound; lia. }
  lia.
Qed.

(** Auxiliary lemma: right branch shrinks range (when low < high) *)
Lemma right_branch_shrinks : forall low high : Z,
  low < high ->
  high - ((low + high) / 2 + 1) < high - low.
Proof.
  intros low high Hlt.
  assert (Hmid : low <= (low + high) / 2).
  { apply Z.div_le_lower_bound; lia. }
  lia.
Qed.

(** trace_ball_step preserves invariants and makes progress *)
Lemma trace_ball_step_invariants : forall st,
  ts_low st < ts_high st ->
  0 <= ts_ball_index st < ts_ball_count st ->
  ts_ball_count st > 0 ->
  let st' := trace_ball_step st in
  ts_low st' <= ts_high st' /\
  ts_high st' - ts_low st' < ts_high st - ts_low st /\
  0 <= ts_ball_index st' < ts_ball_count st'.
Proof.
  intros st Hrange Hball_idx Hball_pos.
  unfold trace_ball_step.
  set (low := ts_low st).
  set (high := ts_high st).
  set (ball_count := ts_ball_count st).
  set (ball_index := ts_ball_index st).
  set (mid := (low + high) / 2).
  set (left_bins := mid - low + 1).
  set (total_bins := high - low + 1).
  set (node_id := encode_node low high ball_count).
  set (prf_output := prf_eval node_id).
  set (left_count := binomial_sample_spec ball_count left_bins total_bins prf_output).
  assert (Hmid_range : low <= mid < high).
  { split.
    - apply Z.div_le_lower_bound; lia.
    - apply Z.div_lt_upper_bound; lia. }
  assert (Hleft_bins_pos : 0 < left_bins) by (unfold left_bins; lia).
  assert (Htotal_bins_pos : 0 < total_bins) by (unfold total_bins; lia).
  assert (Hleft_lt_total : left_bins < total_bins) by (unfold left_bins, total_bins; lia).
  assert (Hleft_count_range : 0 <= left_count <= ball_count).
  { apply binomial_sample_range; lia. }
  destruct Hleft_count_range as [Hlc_lo Hlc_hi].
  pose proof (left_branch_shrinks low high Hrange) as Hleft_shrink.
  pose proof (right_branch_shrinks low high Hrange) as Hright_shrink.
  destruct (ball_index <? left_count) eqn:Hcmp.
  - apply Z.ltb_lt in Hcmp.
    simpl. repeat split; lia.
  - apply Z.ltb_ge in Hcmp.
    simpl. repeat split; lia.
Qed.

(** ** Lemmas for range_list *)

Lemma range_list_spec : forall start count fuel x,
  count <= Z.of_nat fuel ->
  0 <= count ->
  In x (range_list start count fuel) <-> (start <= x < start + count).
Proof.
  intros start count fuel.
  generalize dependent count.
  generalize dependent start.
  induction fuel as [|fuel' IH]; intros start count x Hfuel Hcount.
  - simpl. assert (count = 0) by lia. subst.
    split; [intros []|lia].
  - simpl.
    destruct (count <=? 0) eqn:Hcmp.
    + apply Z.leb_le in Hcmp.
      assert (count = 0) by lia. subst.
      split; [intros []|lia].
    + apply Z.leb_gt in Hcmp.
      simpl. rewrite IH by lia.
      split.
      * intros [Heq | Hin].
        -- subst. lia.
        -- lia.
      * intros Hrange.
        destruct (Z.eq_dec x start).
        -- left. auto.
        -- right. lia.
Qed.

(** ** Lemmas for trace_ball *)

(** Helper: trace_ball_fuel preserves low <= result < high + 1 *)
Lemma trace_ball_fuel_bounds : forall fuel st,
  ts_low st <= ts_high st ->
  ts_low st <= trace_ball_fuel fuel st <= ts_high st.
Proof.
  induction fuel as [|fuel' IH]; intros st Hrange.
  - simpl. lia.
  - simpl.
    destruct (ts_low st <? ts_high st) eqn:Hcmp.
    + apply Z.ltb_lt in Hcmp.
      set (st' := trace_ball_step st).
      assert (Hst'_range : ts_low st' <= ts_high st').
      { unfold st', trace_ball_step.
        set (mid := (ts_low st + ts_high st) / 2).
        assert (Hmid : ts_low st <= mid < ts_high st).
        { split.
          - apply Z.div_le_lower_bound; lia.
          - apply Z.div_lt_upper_bound; lia. }
        destruct (ts_ball_index st <? _); simpl; lia. }
      assert (Hst'_in_orig : ts_low st <= ts_low st' /\ ts_high st' <= ts_high st).
      { unfold st', trace_ball_step.
        set (mid := (ts_low st + ts_high st) / 2).
        assert (Hmid : ts_low st <= mid < ts_high st).
        { split.
          - apply Z.div_le_lower_bound; lia.
          - apply Z.div_lt_upper_bound; lia. }
        destruct (ts_ball_index st <? _); simpl; lia. }
      specialize (IH st' Hst'_range).
      lia.
    + apply Z.ltb_ge in Hcmp.
      assert (ts_low st = ts_high st) by lia.
      simpl. lia.
Qed.

(** trace_ball output is in valid range *)
Lemma trace_ball_in_range :
  forall x n m,
    0 <= x < n ->
    0 < m ->
    m <= n ->
    0 <= trace_ball_spec x n m < m.
Proof.
  intros x n m Hx Hm Hmn.
  unfold trace_ball_spec.
  destruct (m =? 1) eqn:Hm1.
  - apply Z.eqb_eq in Hm1. lia.
  - apply Z.eqb_neq in Hm1.
    set (initial := mkTraceState 0 (m - 1) n x).
    set (fuel := Z.to_nat (2 * m)).
    assert (Hinit_range : ts_low initial <= ts_high initial).
    { simpl. lia. }
    pose proof (trace_ball_fuel_bounds fuel initial Hinit_range) as Hbounds.
    simpl in Hbounds.
    destruct Hbounds as [Hlo Hhi].
    split.
    + exact Hlo.
    + assert (m - 1 < m) by lia. lia.
Qed.

(** ** Lemmas for trace_ball_inverse *)

Lemma binomial_sample_range_aux :
  forall count num denom prf_output,
    0 <= count ->
    0 <= num ->
    num < denom ->
    0 < denom ->
    0 <= binomial_sample_spec count num denom prf_output <= count.
Proof.
  intros count num denom prf_output Hcount Hnum Hnum_lt Hdenom.
  apply binomial_sample_range_full; assumption.
Qed.



(** Invariant for trace_ball_inverse_fuel: the (start, count) returned satisfy bounds.
    Note: relies on binomial_sample_range_aux for count >= 0. *)
Lemma trace_ball_inverse_fuel_bounds : forall fuel y st n,
  0 <= tis_ball_start st ->
  0 <= tis_ball_count st ->
  tis_ball_start st + tis_ball_count st <= n ->
  let '(start, count) := trace_ball_inverse_fuel fuel y st in
  0 <= start /\ 0 <= count /\ start + count <= n.
Proof.
  induction fuel as [|fuel' IH]; intros y st n0 Hstart_pos Hcount_pos Hbound.
  - simpl. lia.
  - simpl.
    destruct (tis_low st <? tis_high st) eqn:Hcmp.
    + apply Z.ltb_lt in Hcmp.
      unfold trace_ball_inverse_step.
      set (low := tis_low st).
      set (high := tis_high st).
      set (ball_count := tis_ball_count st).
      set (ball_start := tis_ball_start st).
      set (mid := (low + high) / 2).
      set (left_bins := mid - low + 1).
      set (total_bins := high - low + 1).
      set (node_id := encode_node low high ball_count).
      set (prf_output := prf_eval node_id).
      set (left_count := binomial_sample_spec ball_count left_bins total_bins prf_output).
      assert (Hmid_range : low <= mid < high).
      { split.
        - apply Z.div_le_lower_bound; lia.
        - apply Z.div_lt_upper_bound; lia. }
      assert (Hleft_bins_pos : 0 < left_bins) by (unfold left_bins; lia).
      assert (Htotal_bins_pos : 0 < total_bins) by (unfold total_bins; lia).
      assert (Hleft_lt_total : left_bins < total_bins) by (unfold left_bins, total_bins; lia).
      assert (Hleft_count_range : 0 <= left_count <= ball_count).
      { unfold left_count. apply binomial_sample_range_aux; unfold ball_count; lia. }
      destruct (y <=? mid) eqn:Hbranch.
      * simpl. apply IH; simpl; lia.
      * simpl. apply IH; simpl; lia.
    + lia.
Qed.

(** The returned start is at least the initial ball_start *)
Lemma trace_ball_inverse_fuel_start_lower_bound : forall fuel y st,
  0 <= tis_ball_count st ->
  let '(start, count) := trace_ball_inverse_fuel fuel y st in
  tis_ball_start st <= start.
Proof.
  induction fuel as [|fuel' IH]; intros y st Hcount_pos.
  - simpl. lia.
  - simpl.
    destruct (tis_low st <? tis_high st) eqn:Hcmp.
    + apply Z.ltb_lt in Hcmp.
      set (low := tis_low st).
      set (high := tis_high st).
      set (ball_count := tis_ball_count st).
      set (ball_start := tis_ball_start st).
      set (mid := (low + high) / 2).
      set (left_bins := mid - low + 1).
      set (total_bins := high - low + 1).
      set (node_id := encode_node low high ball_count).
      set (prf_output := prf_eval node_id).
      set (left_count := binomial_sample_spec ball_count left_bins total_bins prf_output).
      assert (Hmid_range : low <= mid < high).
      { subst mid low high. split.
        - apply Z.div_le_lower_bound; lia.
        - apply Z.div_lt_upper_bound; lia. }
      assert (Hleft_bins_pos : 0 < left_bins) by (subst left_bins mid low high; lia).
      assert (Htotal_bins_pos : 0 < total_bins) by (subst total_bins low high; lia).
      assert (Hleft_lt_total : left_bins < total_bins) by (subst left_bins total_bins mid low high; lia).
      assert (Hlc_range : 0 <= left_count <= ball_count).
      { subst left_count ball_count. apply binomial_sample_range_aux; lia. }
      set (st' := trace_ball_inverse_step y st).
      assert (Hstart' : ball_start <= tis_ball_start st').
      { unfold st', trace_ball_inverse_step.
        fold low high ball_count ball_start mid left_bins total_bins node_id prf_output left_count.
        destruct (y <=? mid); simpl; lia. }
      assert (Hcount' : 0 <= tis_ball_count st').
      { unfold st', trace_ball_inverse_step.
        fold low high ball_count ball_start mid left_bins total_bins node_id prf_output left_count.
        destruct (y <=? mid); simpl; lia. }
      specialize (IH y st' Hcount').
      destruct (trace_ball_inverse_fuel fuel' y st') as [start count].
      lia.
    + lia.
Qed.
(** All elements in trace_ball_inverse are in valid domain range *)
Lemma trace_ball_inverse_range :
  forall y n m x,
    0 <= y < m ->
    0 < m ->
    m <= n ->
    In x (trace_ball_inverse_spec y n m) ->
    0 <= x < n.
Proof.
  intros y n0 m0 x Hy Hm_pos Hm_le_n Hin.
  unfold trace_ball_inverse_spec in Hin.
  destruct (m0 =? 1) eqn:Hm1.
  - apply Z.eqb_eq in Hm1.
    apply range_list_spec in Hin.
    + lia.
    + rewrite Z2Nat.id; lia.
    + lia.
  - apply Z.eqb_neq in Hm1.
    remember (mkTraceInvState 0 (m0 - 1) n0 0) as initial_state eqn:Hinit.
    remember (Z.to_nat (2 * m0)) as fuel eqn:Hfuel_def.
    destruct (trace_ball_inverse_fuel fuel y initial_state) as [start count] eqn:Hfuel.
    assert (Hbounds : 0 <= start /\ 0 <= count /\ start + count <= n0).
    { pose proof (trace_ball_inverse_fuel_bounds fuel y initial_state n0) as Hinv.
      rewrite Hfuel in Hinv.
      apply Hinv; subst initial_state; simpl; lia. }
    destruct Hbounds as [Hstart_pos [Hcount_pos Hbound]].
    apply range_list_spec in Hin.
    + lia.
    + rewrite Z2Nat.id; lia.
    + assumption.
Qed.

(** Helper: forward and inverse traverse the same path.
    This is the core lemma showing that if forward ends at bin y, 
    then running inverse with y returns an interval containing x. *)
Lemma trace_ball_fuel_inverse_contains :
  forall fuel x st ist,
    ts_low st = tis_low ist ->
    ts_high st = tis_high ist ->
    ts_ball_count st = tis_ball_count ist ->
    ts_ball_index st = x - tis_ball_start ist ->
    0 <= ts_ball_index st < ts_ball_count st ->
    ts_low st <= ts_high st ->
    let y := trace_ball_fuel fuel st in
    let '(start, count) := trace_ball_inverse_fuel fuel y ist in
    start <= x < start + count.
Proof.
  induction fuel as [|fuel IH]; intros x st ist Hlow Hhigh Hcount Hidx Hball Hrange.
  - simpl. lia.
  - simpl.
    destruct (ts_low st <? ts_high st) eqn:Hlt.
    + apply Z.ltb_lt in Hlt.
      assert (Hlt_inv : (tis_low ist <? tis_high ist) = true).
      { rewrite <- Hlow, <- Hhigh. apply Z.ltb_lt. exact Hlt. }
      rewrite Hlt_inv.
      set (low := ts_low st).
      set (high := ts_high st).
      set (ball_count := ts_ball_count st).
      set (ball_index := ts_ball_index st).
      set (ball_start := tis_ball_start ist).
      set (mid := (low + high) / 2).
      set (left_bins := mid - low + 1).
      set (total_bins := high - low + 1).
      set (node_id := encode_node low high ball_count).
      set (prf_output := prf_eval node_id).
      set (left_count := binomial_sample_spec ball_count left_bins total_bins prf_output).
      assert (Hmid_range : low <= mid < high).
      { subst mid low high. split.
        - apply Z.div_le_lower_bound; lia.
        - apply Z.div_lt_upper_bound; lia. }
      assert (Hleft_bins_pos : 0 < left_bins) by (subst left_bins mid low high; lia).
      assert (Htotal_bins_pos : 0 < total_bins) by (subst total_bins low high; lia).
      assert (Hleft_lt_total : left_bins < total_bins) by (subst left_bins total_bins mid low high; lia).
      assert (Hlc_range : 0 <= left_count <= ball_count).
      { subst left_count ball_count. apply binomial_sample_range_aux; lia. }
      destruct Hlc_range as [Hlc_lo Hlc_hi].
      assert (Htis_low_eq : tis_low ist = low).
      { subst low. exact (eq_sym Hlow). }
      assert (Htis_high_eq : tis_high ist = high).
      { subst high. exact (eq_sym Hhigh). }
      assert (Htis_ball_count_eq : tis_ball_count ist = ball_count).
      { subst ball_count. exact (eq_sym Hcount). }
      assert (Hinv_step_left : forall y, y <= mid ->
        trace_ball_inverse_step y ist = mkTraceInvState low mid left_count ball_start).
      { intros y0 Hy0.
        unfold trace_ball_inverse_step.
        rewrite Htis_low_eq, Htis_high_eq, Htis_ball_count_eq.
        subst mid left_bins total_bins node_id prf_output left_count ball_start.
        destruct (y0 <=? _) eqn:Htest.
        - reflexivity.
        - apply Z.leb_gt in Htest. lia. }
      assert (Hinv_step_right : forall y, y > mid ->
        trace_ball_inverse_step y ist = 
          mkTraceInvState (mid + 1) high (ball_count - left_count) (ball_start + left_count)).
      { intros y0 Hy0.
        unfold trace_ball_inverse_step.
        rewrite Htis_low_eq, Htis_high_eq, Htis_ball_count_eq.
        subst mid left_bins total_bins node_id prf_output left_count ball_start ball_count.
        destruct (y0 <=? _) eqn:Htest.
        - apply Z.leb_le in Htest. lia.
        - reflexivity. }
      destruct (ball_index <? left_count) eqn:Hbranch_fwd.
      * set (st' := mkTraceState low mid left_count ball_index).
        set (ist' := mkTraceInvState low mid left_count ball_start).
        assert (Hbranch_fwd_lt : ball_index < left_count).
        { apply Z.ltb_lt. exact Hbranch_fwd. }
        assert (Hst'_range : ts_low st' <= ts_high st').
        { subst st'. simpl. lia. }
        assert (Hy_bounds : ts_low st' <= trace_ball_fuel fuel st' <= ts_high st').
        { apply trace_ball_fuel_bounds. exact Hst'_range. }
        assert (Hy_le_mid : trace_ball_fuel fuel st' <= mid).
        { subst st'. simpl in Hy_bounds. lia. }
        assert (Hst'_eq : trace_ball_step st = st').
        { unfold trace_ball_step. subst st' low high ball_count ball_index mid 
            left_bins total_bins node_id prf_output left_count.
          rewrite Hbranch_fwd. reflexivity. }
        assert (Hist'_eq : trace_ball_inverse_step (trace_ball_fuel fuel st') ist = ist').
        { subst ist'. apply Hinv_step_left. exact Hy_le_mid. }
        rewrite Hst'_eq, Hist'_eq.
        apply IH; subst st' ist' low high ball_count ball_index ball_start 
            mid left_bins total_bins node_id prf_output left_count; simpl; 
          [reflexivity | reflexivity | reflexivity | exact Hidx | | lia]; lia.
      * set (st' := mkTraceState (mid + 1) high (ball_count - left_count) (ball_index - left_count)).
        set (ist' := mkTraceInvState (mid + 1) high (ball_count - left_count) (ball_start + left_count)).
        assert (Hbranch_fwd_ge : left_count <= ball_index).
        { rewrite Z.ltb_ge in Hbranch_fwd. exact Hbranch_fwd. }
        assert (Hst'_range : ts_low st' <= ts_high st').
        { subst st'. simpl. lia. }
        assert (Hy_bounds : ts_low st' <= trace_ball_fuel fuel st' <= ts_high st').
        { apply trace_ball_fuel_bounds. exact Hst'_range. }
        assert (Hy_gt_mid : mid < trace_ball_fuel fuel st').
        { subst st'. simpl in Hy_bounds. lia. }
        assert (Hst'_eq : trace_ball_step st = st').
        { unfold trace_ball_step. subst st' low high ball_count ball_index mid
            left_bins total_bins node_id prf_output left_count.
          rewrite Hbranch_fwd. reflexivity. }
        assert (Hist'_eq : trace_ball_inverse_step (trace_ball_fuel fuel st') ist = ist').
        { subst ist'. apply Hinv_step_right. lia. }
        rewrite Hst'_eq, Hist'_eq.
        apply IH; subst st' ist' low high ball_count ball_index ball_start 
            mid left_bins total_bins node_id prf_output left_count; simpl; 
          try reflexivity; try lia.
    + apply Z.ltb_ge in Hlt.
      assert (Hlt_inv : (tis_low ist <? tis_high ist) = false).
      { rewrite <- Hlow, <- Hhigh. apply Z.ltb_ge. lia. }
      rewrite Hlt_inv. simpl. lia.
Qed.

(** trace_ball_inverse contains the original input *)
Lemma trace_ball_inverse_contains_original :
  forall x n m,
    0 <= x < n ->
    0 < m ->
    m <= n ->
    In x (trace_ball_inverse_spec (trace_ball_spec x n m) n m).
Proof.
  intros x n m Hx Hm Hmn.
  unfold trace_ball_inverse_spec, trace_ball_spec.
  destruct (m =? 1) eqn:Hm1.
  - apply Z.eqb_eq in Hm1.
    apply range_list_spec.
    + rewrite Z2Nat.id; lia.
    + lia.
    + lia.
  - apply Z.eqb_neq in Hm1.
    set (init_st := mkTraceState 0 (m - 1) n x).
    set (init_ist := mkTraceInvState 0 (m - 1) n 0).
    set (fuel := Z.to_nat (2 * m)).
    set (y := trace_ball_fuel fuel init_st).
    assert (Hinv : let '(start, count) := trace_ball_inverse_fuel fuel y init_ist in
                   start <= x < start + count).
    { apply trace_ball_fuel_inverse_contains; simpl; lia. }
    destruct (trace_ball_inverse_fuel fuel y init_ist) as [start count] eqn:Hresult.
    apply range_list_spec.
    + rewrite Z2Nat.id; lia.
    + lia.
    + lia.
Qed.

(** Helper: inverse elements at different y values have disjoint ball_start ranges *)
Lemma trace_ball_inverse_fuel_disjoint :
  forall fuel y1 y2 ist,
    y1 <> y2 ->
    tis_low ist <= y1 <= tis_high ist ->
    tis_low ist <= y2 <= tis_high ist ->
    tis_low ist < tis_high ist ->
    tis_high ist - tis_low ist < Z.of_nat fuel ->
    0 <= tis_ball_start ist ->
    0 <= tis_ball_count ist ->
    let '(s1, c1) := trace_ball_inverse_fuel fuel y1 ist in
    let '(s2, c2) := trace_ball_inverse_fuel fuel y2 ist in
    s1 + c1 <= s2 \/ s2 + c2 <= s1.
Proof.
  induction fuel as [|fuel' IH]; intros y1 y2 ist Hneq Hy1 Hy2 Hlt Hfuel Hstart_pos Hcount_pos.
  - simpl in Hfuel. lia.
  - simpl.
    destruct (tis_low ist <? tis_high ist) eqn:Hcmp.
    + apply Z.ltb_lt in Hcmp.
      set (low := tis_low ist).
      set (high := tis_high ist).
      set (ball_count := tis_ball_count ist).
      set (ball_start := tis_ball_start ist).
      set (mid := (low + high) / 2).
      set (left_bins := mid - low + 1).
      set (total_bins := high - low + 1).
      set (node_id := encode_node low high ball_count).
      set (prf_output := prf_eval node_id).
      set (left_count := binomial_sample_spec ball_count left_bins total_bins prf_output).
      assert (Hmid_range : low <= mid < high).
      { subst mid low high. split.
        - apply Z.div_le_lower_bound; lia.
        - apply Z.div_lt_upper_bound; lia. }
      assert (Hleft_bins_pos : 0 < left_bins) by (subst left_bins mid low high; lia).
      assert (Htotal_bins_pos : 0 < total_bins) by (subst total_bins low high; lia).
      assert (Hleft_lt_total : left_bins < total_bins) by (subst left_bins total_bins mid low high; lia).
      assert (Hlc_range : 0 <= left_count <= ball_count).
      { subst left_count ball_count. apply binomial_sample_range_aux; lia. }
      destruct Hlc_range as [Hlc_lo Hlc_hi].
      destruct (y1 <=? mid) eqn:Hy1_branch; destruct (y2 <=? mid) eqn:Hy2_branch.
      * apply Z.leb_le in Hy1_branch.
        apply Z.leb_le in Hy2_branch.
        set (ist' := mkTraceInvState low mid left_count ball_start).
        assert (Hist1 : trace_ball_inverse_step y1 ist = ist').
        { unfold trace_ball_inverse_step.
          fold low high ball_count ball_start mid left_bins total_bins node_id prf_output left_count.
          destruct (y1 <=? mid) eqn:Htest; [reflexivity | apply Z.leb_gt in Htest; lia]. }
        assert (Hist2 : trace_ball_inverse_step y2 ist = ist').
        { unfold trace_ball_inverse_step.
          fold low high ball_count ball_start mid left_bins total_bins node_id prf_output left_count.
          destruct (y2 <=? mid) eqn:Htest; [reflexivity | apply Z.leb_gt in Htest; lia]. }
        rewrite Hist1, Hist2.
        destruct (low <? mid) eqn:Hlt'.
        -- apply Z.ltb_lt in Hlt'.
           apply IH; simpl; try lia.
        -- apply Z.ltb_ge in Hlt'.
           assert (low = mid) by lia.
           assert (y1 = mid) by lia.
           assert (y2 = mid) by lia.
           lia.
      * apply Z.leb_le in Hy1_branch.
        apply Z.leb_gt in Hy2_branch.
        set (ist1' := mkTraceInvState low mid left_count ball_start).
        set (ist2' := mkTraceInvState (mid + 1) high (ball_count - left_count) (ball_start + left_count)).
        assert (Hist1 : trace_ball_inverse_step y1 ist = ist1').
        { unfold trace_ball_inverse_step.
          fold low high ball_count ball_start mid left_bins total_bins node_id prf_output left_count.
          destruct (y1 <=? mid) eqn:Htest; [reflexivity | apply Z.leb_gt in Htest; lia]. }
        assert (Hist2 : trace_ball_inverse_step y2 ist = ist2').
        { unfold trace_ball_inverse_step.
          fold low high ball_count ball_start mid left_bins total_bins node_id prf_output left_count.
          destruct (y2 <=? mid) eqn:Htest; [apply Z.leb_le in Htest; lia | reflexivity]. }
        rewrite Hist1, Hist2.
        destruct (trace_ball_inverse_fuel fuel' y1 ist1') as [s1 c1] eqn:Hres1.
        destruct (trace_ball_inverse_fuel fuel' y2 ist2') as [s2 c2] eqn:Hres2.
        assert (Hbounds1 : 0 <= s1 /\ 0 <= c1 /\ s1 + c1 <= ball_start + left_count).
        { pose proof (trace_ball_inverse_fuel_bounds fuel' y1 ist1' (ball_start + left_count)) as Hb.
          rewrite Hres1 in Hb. apply Hb; simpl; lia. }
        assert (Hbounds2 : ball_start + left_count <= s2).
        { pose proof (trace_ball_inverse_fuel_start_lower_bound fuel' y2 ist2') as Hlb.
          rewrite Hres2 in Hlb. apply Hlb. simpl. lia. }
        left. lia.
      * apply Z.leb_gt in Hy1_branch.
        apply Z.leb_le in Hy2_branch.
        set (ist1' := mkTraceInvState (mid + 1) high (ball_count - left_count) (ball_start + left_count)).
        set (ist2' := mkTraceInvState low mid left_count ball_start).
        assert (Hist1 : trace_ball_inverse_step y1 ist = ist1').
        { unfold trace_ball_inverse_step.
          fold low high ball_count ball_start mid left_bins total_bins node_id prf_output left_count.
          destruct (y1 <=? mid) eqn:Htest; [apply Z.leb_le in Htest; lia | reflexivity]. }
        assert (Hist2 : trace_ball_inverse_step y2 ist = ist2').
        { unfold trace_ball_inverse_step.
          fold low high ball_count ball_start mid left_bins total_bins node_id prf_output left_count.
          destruct (y2 <=? mid) eqn:Htest; [reflexivity | apply Z.leb_gt in Htest; lia]. }
        rewrite Hist1, Hist2.
        destruct (trace_ball_inverse_fuel fuel' y1 ist1') as [s1 c1] eqn:Hres1.
        destruct (trace_ball_inverse_fuel fuel' y2 ist2') as [s2 c2] eqn:Hres2.
        assert (Hbounds2 : 0 <= s2 /\ 0 <= c2 /\ s2 + c2 <= ball_start + left_count).
        { pose proof (trace_ball_inverse_fuel_bounds fuel' y2 ist2' (ball_start + left_count)) as Hb.
          rewrite Hres2 in Hb. apply Hb; simpl; lia. }
        assert (Hbounds1 : ball_start + left_count <= s1).
        { pose proof (trace_ball_inverse_fuel_start_lower_bound fuel' y1 ist1') as Hlb.
          rewrite Hres1 in Hlb. apply Hlb. simpl. lia. }
        right. lia.
      * apply Z.leb_gt in Hy1_branch.
        apply Z.leb_gt in Hy2_branch.
        set (ist' := mkTraceInvState (mid + 1) high (ball_count - left_count) (ball_start + left_count)).
        assert (Hist1 : trace_ball_inverse_step y1 ist = ist').
        { unfold trace_ball_inverse_step.
          fold low high ball_count ball_start mid left_bins total_bins node_id prf_output left_count.
          destruct (y1 <=? mid) eqn:Htest; [apply Z.leb_le in Htest; lia | reflexivity]. }
        assert (Hist2 : trace_ball_inverse_step y2 ist = ist').
        { unfold trace_ball_inverse_step.
          fold low high ball_count ball_start mid left_bins total_bins node_id prf_output left_count.
          destruct (y2 <=? mid) eqn:Htest; [apply Z.leb_le in Htest; lia | reflexivity]. }
        rewrite Hist1, Hist2.
        destruct (mid + 1 <? high) eqn:Hlt'.
        -- apply Z.ltb_lt in Hlt'.
           apply IH; simpl; try lia.
        -- apply Z.ltb_ge in Hlt'.
           assert (mid + 1 = high) by lia.
           assert (y1 = high) by lia.
           assert (y2 = high) by lia.
           lia.
    + apply Z.ltb_ge in Hcmp. lia.
Qed.
(** Helper: if x is in the inverse range, forward(x) = y *)
Lemma trace_ball_inverse_fuel_consistent :
  forall fuel y x st ist,
    ts_low st = tis_low ist ->
    ts_high st = tis_high ist ->
    ts_ball_count st = tis_ball_count ist ->
    ts_ball_index st = x - tis_ball_start ist ->
    tis_low ist <= y <= tis_high ist ->
    ts_low st <= ts_high st ->
    ts_high st - ts_low st < Z.of_nat fuel ->
    0 <= tis_ball_start ist ->
    let '(start, count) := trace_ball_inverse_fuel fuel y ist in
    start <= x < start + count ->
    0 <= ts_ball_index st < ts_ball_count st ->
    trace_ball_fuel fuel st = y.
Proof.
  induction fuel as [|fuel' IH]; intros y x st ist Hlow Hhigh Hcount Hidx Hy_range Hst_range Hfuel Hball_start_pos.
  - simpl in Hfuel. lia.
  - simpl.
    destruct (ts_low st <? ts_high st) eqn:Hlt.
    + apply Z.ltb_lt in Hlt.
      assert (Hlt_inv : (tis_low ist <? tis_high ist) = true).
      { rewrite <- Hlow, <- Hhigh. apply Z.ltb_lt. exact Hlt. }
      rewrite Hlt_inv.
      set (low := ts_low st).
      set (high := ts_high st).
      set (ball_count := ts_ball_count st).
      set (ball_index := ts_ball_index st).
      set (ball_start := tis_ball_start ist).
      set (mid := (low + high) / 2).
      set (left_bins := mid - low + 1).
      set (total_bins := high - low + 1).
      set (node_id := encode_node low high ball_count).
      set (prf_output := prf_eval node_id).
      set (left_count := binomial_sample_spec ball_count left_bins total_bins prf_output).
      assert (Hmid_range : low <= mid < high).
      { subst mid low high. split.
        - apply Z.div_le_lower_bound; lia.
        - apply Z.div_lt_upper_bound; lia. }
      assert (Hleft_bins_pos : 0 < left_bins) by (subst left_bins mid low high; lia).
      assert (Htotal_bins_pos : 0 < total_bins) by (subst total_bins low high; lia).
      assert (Hleft_lt_total : left_bins < total_bins) by (subst left_bins total_bins mid low high; lia).
      assert (Htis_low_eq : tis_low ist = low).
      { subst low. exact (eq_sym Hlow). }
      assert (Htis_high_eq : tis_high ist = high).
      { subst high. exact (eq_sym Hhigh). }
      assert (Htis_ball_count_eq : tis_ball_count ist = ball_count).
      { subst ball_count. exact (eq_sym Hcount). }
      assert (Hinv_step_left : y <= mid ->
        trace_ball_inverse_step y ist = mkTraceInvState low mid left_count ball_start).
      { intros Hy0.
        unfold trace_ball_inverse_step.
        rewrite Htis_low_eq, Htis_high_eq, Htis_ball_count_eq.
        subst mid left_bins total_bins node_id prf_output left_count ball_start.
        destruct (y <=? _) eqn:Htest.
        - reflexivity.
        - apply Z.leb_gt in Htest. lia. }
      assert (Hinv_step_right : y > mid ->
        trace_ball_inverse_step y ist = 
          mkTraceInvState (mid + 1) high (ball_count - left_count) (ball_start + left_count)).
      { intros Hy0.
        unfold trace_ball_inverse_step.
        rewrite Htis_low_eq, Htis_high_eq, Htis_ball_count_eq.
        subst mid left_bins total_bins node_id prf_output left_count ball_start ball_count.
        destruct (y <=? _) eqn:Htest.
        - apply Z.leb_le in Htest. lia.
        - reflexivity. }
      destruct (y <=? mid) eqn:Hy_branch.
      * apply Z.leb_le in Hy_branch.
        rewrite Hinv_step_left by assumption.
        set (st' := mkTraceState low mid left_count ball_index).
        set (ist' := mkTraceInvState low mid left_count ball_start).
        destruct (trace_ball_inverse_fuel fuel' y ist') as [start' count'] eqn:Hinv_res'.
        intros Hx_in_range Hball_valid.
        assert (Hball_count_pos : 0 < ball_count).
        { subst ball_count ball_index. lia. }
        assert (Hlc_range : 0 <= left_count <= ball_count).
        { subst left_count ball_count. apply binomial_sample_range_aux; lia. }
        destruct Hlc_range as [Hlc_lo Hlc_hi].
        assert (Hball_index_lt : ball_index < left_count).
        { pose proof (trace_ball_inverse_fuel_start_lower_bound fuel' y ist') as Hlb.
          rewrite Hinv_res' in Hlb.
          assert (Hstart_lb : ball_start <= start') by (apply Hlb; simpl; lia).
          pose proof (trace_ball_inverse_fuel_bounds fuel' y ist' (ball_start + left_count)) as Hb.
          rewrite Hinv_res' in Hb.
          assert (Hbounds : 0 <= start' /\ 0 <= count' /\ start' + count' <= ball_start + left_count).
          { apply Hb; simpl; subst ball_start; lia. }
          subst ball_index. lia. }
        assert (Hbranch_fwd : (ball_index <? left_count) = true).
        { apply Z.ltb_lt. exact Hball_index_lt. }
        assert (Hst'_eq : trace_ball_step st = st').
        { unfold trace_ball_step. subst st' low high ball_count ball_index mid 
            left_bins total_bins node_id prf_output left_count.
          rewrite Hbranch_fwd. reflexivity. }
        rewrite Hst'_eq.
        pose proof (IH y x st' ist') as IH'.
        rewrite Hinv_res' in IH'.
        apply IH'; simpl.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- subst ball_index. exact Hidx.
        -- lia.
        -- lia.
        -- lia.
        -- subst ball_start. exact Hball_start_pos.
        -- exact Hx_in_range.
        -- lia.
      * apply Z.leb_gt in Hy_branch.
        assert (Hstep_right_eq : trace_ball_inverse_step y ist = 
          mkTraceInvState (mid + 1) high (ball_count - left_count) (ball_start + left_count)).
        { apply Hinv_step_right. lia. }
        rewrite Hstep_right_eq.
        set (st' := mkTraceState (mid + 1) high (ball_count - left_count) (ball_index - left_count)).
        set (ist' := mkTraceInvState (mid + 1) high (ball_count - left_count) (ball_start + left_count)).
        destruct (trace_ball_inverse_fuel fuel' y ist') as [start' count'] eqn:Hinv_res'.
        intros Hx_in_range Hball_valid.
        assert (Hball_count_pos : 0 < ball_count).
        { subst ball_count ball_index. lia. }
        assert (Hlc_range : 0 <= left_count <= ball_count).
        { subst left_count ball_count. apply binomial_sample_range_aux; lia. }
        destruct Hlc_range as [Hlc_lo Hlc_hi].
        assert (Hball_index_ge : left_count <= ball_index).
        { pose proof (trace_ball_inverse_fuel_start_lower_bound fuel' y ist') as Hlb.
          rewrite Hinv_res' in Hlb.
          assert (Hstart_lb : ball_start + left_count <= start') by (apply Hlb; simpl; lia).
          subst ball_index. lia. }
        assert (Hbranch_fwd : (ball_index <? left_count) = false).
        { apply Z.ltb_ge. exact Hball_index_ge. }
        assert (Hst'_eq : trace_ball_step st = st').
        { unfold trace_ball_step. subst st' low high ball_count ball_index mid 
            left_bins total_bins node_id prf_output left_count.
          rewrite Hbranch_fwd. reflexivity. }
        rewrite Hst'_eq.
        pose proof (IH y x st' ist') as IH'.
        rewrite Hinv_res' in IH'.
        apply IH'; simpl; try lia; try exact Hx_in_range.
    + apply Z.ltb_ge in Hlt.
      assert (Hlow_eq_high : ts_low st = ts_high st) by lia.
      assert (Hlt_inv : (tis_low ist <? tis_high ist) = false).
      { rewrite <- Hlow, <- Hhigh. apply Z.ltb_ge. lia. }
      rewrite Hlt_inv.
      simpl. intros Hx_range Hball_valid.
      assert (y = tis_low ist) by lia.
      rewrite Hlow. lia.
Qed.

(** Inverse elements map back to y via the forward function.
    The proof uses the key insight that forward and inverse follow the same tree path.
    If x is in inverse(y), then running forward on x must end at y because:
    - inverse(y) descends the tree to find all balls in bin y
    - forward(x) descends the tree following the same branching decisions for ball x
    - At each step, x in the left/right range iff y in left/right subtree *)
Lemma trace_ball_inverse_consistent : forall y n m x,
  0 <= y < m ->
  0 < m ->
  m <= n ->
  In x (trace_ball_inverse_spec y n m) ->
  trace_ball_spec x n m = y.
Proof.
  intros y n0 m0 x Hy Hm_pos Hm_le_n Hin.
  unfold trace_ball_inverse_spec in Hin.
  unfold trace_ball_spec.
  destruct (m0 =? 1) eqn:Hm1.
  - apply Z.eqb_eq in Hm1.
    assert (y = 0) by lia. subst. reflexivity.
  - apply Z.eqb_neq in Hm1.
    set (init_st := mkTraceState 0 (m0 - 1) n0 x).
    set (init_ist := mkTraceInvState 0 (m0 - 1) n0 0).
    set (fuel := Z.to_nat (2 * m0)).
    change (mkTraceInvState 0 (m0 - 1) n0 0) with init_ist in Hin.
    change (Z.to_nat (2 * m0)) with fuel in Hin.
    remember (trace_ball_inverse_fuel fuel y init_ist) as res eqn:Hinv_result in *.
    destruct res as [start count].
    assert (Hx_in_range : start <= x < start + count).
    { apply range_list_spec in Hin.
      - exact Hin.
      - pose proof (trace_ball_inverse_fuel_bounds fuel y init_ist n0) as Hb.
        rewrite <- Hinv_result in Hb.
        assert (Hbounds : 0 <= start /\ 0 <= count /\ start + count <= n0).
        { apply Hb; simpl; lia. }
        rewrite Z2Nat.id; lia.
      - pose proof (trace_ball_inverse_fuel_bounds fuel y init_ist n0) as Hb.
        rewrite <- Hinv_result in Hb.
        assert (Hbounds : 0 <= start /\ 0 <= count /\ start + count <= n0).
        { apply Hb; simpl; lia. }
        lia. }
    assert (Hball_valid : 0 <= x - 0 < n0).
    { pose proof (trace_ball_inverse_fuel_bounds fuel y init_ist n0) as Hb.
      rewrite <- Hinv_result in Hb.
      assert (Hbounds : 0 <= start /\ 0 <= count /\ start + count <= n0).
      { apply Hb; simpl; lia. }
      pose proof (trace_ball_inverse_fuel_start_lower_bound fuel y init_ist) as Hlb.
      rewrite <- Hinv_result in Hlb.
      assert (Hstart_lb : 0 <= start) by (apply Hlb; simpl; lia).
      lia. }
    pose proof (trace_ball_inverse_fuel_consistent fuel y x init_st init_ist) as Hcons.
    rewrite <- Hinv_result in Hcons.
    apply Hcons; simpl; subst fuel; try (rewrite Z2Nat.id; lia); try lia.
Qed.
(** Union of all inverse(y) for y in [0,m) equals [0,n) exactly once *)
Lemma trace_ball_inverse_partition :
  forall n m,
    0 < m ->
    m <= n ->
    forall x, 0 <= x < n ->
      exists! y, 0 <= y < m /\ In x (trace_ball_inverse_spec y n m).
Proof.
  intros n0 m0 Hm Hmn x Hx.
  set (y := trace_ball_spec x n0 m0).
  exists y.
  split.
  - split.
    + apply trace_ball_in_range; assumption.
    + apply trace_ball_inverse_contains_original; assumption.
  - intros y' [Hy'_range Hy'_in].
    assert (Hcons : trace_ball_spec x n0 m0 = y').
    { apply trace_ball_inverse_consistent with (n := n0) (x := x); assumption. }
    unfold y. exact Hcons.
Qed.

(** ** Lemmas for iPRF *)

(** iPRF forward output is in valid range *)
Lemma iprf_forward_in_range :
  forall x n m,
    0 <= x < n ->
    0 < m ->
    m <= n ->
    0 <= iprf_forward_spec x n m < m.
Proof.
  intros x n0 m0 Hx Hm Hmn.
  unfold iprf_forward_spec.
  destruct ((x <? 0) || (n0 <=? x)) eqn:Hguard.
  - apply orb_true_iff in Hguard.
    destruct Hguard as [Hlt | Hle].
    + apply Z.ltb_lt in Hlt. lia.
    + apply Z.leb_le in Hle. lia.
  - apply trace_ball_in_range.
    + apply prp_forward_in_range. assumption.
    + assumption.
    + assumption.
Qed.

(** iPRF inverse contains the preimage *)
Lemma iprf_inverse_contains_preimage :
  forall x y n m,
    0 <= x < n ->
    0 < m ->
    m <= n ->
    iprf_forward_spec x n m = y ->
    In x (iprf_inverse_spec y n m).
Proof.
  intros x y n0 m0 Hx Hm Hmn Hfwd.
  subst y.
  assert (Hy_range : 0 <= iprf_forward_spec x n0 m0 < m0).
  { apply iprf_forward_in_range; assumption. }
  unfold iprf_inverse_spec.
  destruct ((iprf_forward_spec x n0 m0 <? 0) || (m0 <=? iprf_forward_spec x n0 m0)) eqn:Hguard.
  - apply orb_true_iff in Hguard.
    destruct Hguard as [Hlt | Hle].
    + apply Z.ltb_lt in Hlt. lia.
    + apply Z.leb_le in Hle. lia.
  - unfold iprf_forward_spec.
    destruct ((x <? 0) || (n0 <=? x)) eqn:Hguard2.
    + apply orb_true_iff in Hguard2.
      destruct Hguard2 as [Hlt | Hle].
      * apply Z.ltb_lt in Hlt. lia.
      * apply Z.leb_le in Hle. lia.
    + set (x' := prp_forward n0 x).
      set (y := trace_ball_spec x' n0 m0).
      assert (Hx'_range : 0 <= x' < n0).
      { unfold x'. apply prp_forward_in_range. assumption. }
      assert (Hx'_in_inv : In x' (trace_ball_inverse_spec y n0 m0)).
      { unfold y. apply trace_ball_inverse_contains_original; assumption. }
      apply in_map_iff.
      exists x'.
      split.
      * unfold x'. rewrite prp_forward_inverse; [reflexivity | assumption].
      * exact Hx'_in_inv.
Qed.

(** All elements in iPRF inverse are in valid domain range *)
Lemma iprf_inverse_elements_in_domain :
  forall y n m x,
    0 <= y < m ->
    0 < m ->
    m <= n ->
    In x (iprf_inverse_spec y n m) ->
    0 <= x < n.
Proof.
  intros y n0 m0 x Hy Hm Hmn Hin.
  unfold iprf_inverse_spec in Hin.
  destruct ((y <? 0) || (m0 <=? y)) eqn:Hguard.
  - apply orb_true_iff in Hguard.
    destruct Hguard as [Hlt | Hle].
    + apply Z.ltb_lt in Hlt. lia.
    + apply Z.leb_le in Hle. lia.
  - apply in_map_iff in Hin.
    destruct Hin as [z [Hz_eq Hz_in]].
    assert (Hz_range : 0 <= z < n0).
    { apply trace_ball_inverse_range with (y := y) (m := m0); assumption. }
    subst x.
    apply prp_inverse_in_range. assumption.
Qed.

(** All elements in iPRF inverse map back to y *)
Lemma iprf_inverse_elements_map_to_y :
  forall y n m x,
    0 <= y < m ->
    0 < m ->
    m <= n ->
    In x (iprf_inverse_spec y n m) ->
    iprf_forward_spec x n m = y.
Proof.
  intros y n0 m0 x Hy Hm Hmn Hin.
  unfold iprf_inverse_spec in Hin.
  destruct ((y <? 0) || (m0 <=? y)) eqn:Hguard.
  - apply orb_true_iff in Hguard.
    destruct Hguard as [Hlt | Hle].
    + apply Z.ltb_lt in Hlt. lia.
    + apply Z.leb_le in Hle. lia.
  - apply in_map_iff in Hin.
    destruct Hin as [z [Hz_eq Hz_in]].
    assert (Hz_range : 0 <= z < n0).
    { apply trace_ball_inverse_range with (y := y) (m := m0); assumption. }
    assert (Hx_range : 0 <= x < n0).
    { subst x. apply prp_inverse_in_range. assumption. }
    assert (Hz_maps_to_y : trace_ball_spec z n0 m0 = y).
    { apply trace_ball_inverse_consistent with (n := n0) (x := z); assumption. }
    unfold iprf_forward_spec.
    destruct ((x <? 0) || (n0 <=? x)) eqn:Hguard2.
    + apply orb_true_iff in Hguard2.
      destruct Hguard2 as [Hlt | Hle].
      * apply Z.ltb_lt in Hlt. lia.
      * apply Z.leb_le in Hle. lia.
    + subst x.
      rewrite prp_inverse_forward; [exact Hz_maps_to_y | assumption].
Qed.

(** iPRF inverses partition the domain *)
Lemma iprf_inverse_partitions_domain :
  forall n m,
    0 < m ->
    m <= n ->
    forall x, 0 <= x < n ->
      exists! y, 0 <= y < m /\ In x (iprf_inverse_spec y n m).
Proof.
  intros n0 m0 Hm Hmn x Hx.
  set (y := iprf_forward_spec x n0 m0).
  exists y.
  split.
  - split.
    + apply iprf_forward_in_range; assumption.
    + apply iprf_inverse_contains_preimage; [assumption | assumption | assumption | reflexivity].
  - intros y' [Hy'_range Hy'_in].
    assert (Hfwd : iprf_forward_spec x n0 m0 = y').
    { apply iprf_inverse_elements_map_to_y with (y := y'); assumption. }
    unfold y. exact Hfwd.
Qed.

End IprfParams.

Close Scope Z_scope.
