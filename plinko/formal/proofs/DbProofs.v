(** DbProofs.v - Proofs of key invariants for derive_plinko_params *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.
Require Import Plinko.Specs.CommonTypes.
Require Import Plinko.Specs.DbSpec.

Open Scope Z_scope.

(** Auxiliary lemmas about smallest_power_of_two_geq *)

(** [AXIOM:STRUCTURAL] Auxiliary lemma about power of two preservation.
    The proof involves showing 2^k * 2 = 2^(k+1) and positivity of powers. *)
Lemma smallest_power_of_two_geq_aux_power_of_two :
  forall n acc fuel,
    is_power_of_two acc ->
    is_power_of_two (smallest_power_of_two_geq_aux n acc fuel).
Proof.
  intros n acc fuel.
  generalize dependent acc.
  induction fuel as [| fuel' IH]; intros acc Hacc.
  - simpl. exact Hacc.
  - simpl. destruct (acc <? n) eqn:Hlt.
    + apply IH. destruct Hacc as [Hpos [k Hk]].
      split.
      * subst acc. 
        assert (H: 0 < 2 ^ Z.of_nat k).
        { apply Z.pow_pos_nonneg; [lia | apply Nat2Z.is_nonneg]. }
        nia.
      * exists (S k). subst acc. rewrite Nat2Z.inj_succ.
        rewrite Z.pow_succ_r; [ring | apply Nat2Z.is_nonneg].
    + exact Hacc.
Qed.

Lemma smallest_power_of_two_geq_is_power_of_two :
  forall n, is_power_of_two (smallest_power_of_two_geq n).
Proof.
  intros n. unfold smallest_power_of_two_geq.
  destruct (n <=? 0) eqn:Hneg.
  - split; [lia | exists 0%nat; reflexivity].
  - apply smallest_power_of_two_geq_aux_power_of_two.
    split; [lia | exists 0%nat; reflexivity].
Qed.

Lemma smallest_power_of_two_geq_aux_geq :
  forall n acc fuel,
    acc > 0 ->
    smallest_power_of_two_geq_aux n acc fuel >= acc.
Proof.
  intros n acc fuel.
  generalize dependent acc.
  induction fuel as [| fuel' IH]; intros acc Hacc_pos.
  - simpl. lia.
  - simpl. destruct (acc <? n) eqn:Hlt.
    + specialize (IH (acc * 2)). assert (acc * 2 > 0) by lia. specialize (IH H). lia.
    + lia.
Qed.

Lemma smallest_power_of_two_geq_aux_terminates :
  forall n acc fuel,
    acc > 0 ->
    n > 0 ->
    n <= acc * 2 ^ Z.of_nat fuel ->
    smallest_power_of_two_geq_aux n acc fuel >= n.
Proof.
  intros n acc fuel.
  generalize dependent acc.
  induction fuel as [| fuel' IH]; intros acc Hacc_pos Hn Hbound.
  - simpl. simpl in Hbound. lia.
  - simpl. destruct (acc <? n) eqn:Hlt.
    + apply Z.ltb_lt in Hlt.
      apply IH; try lia.
      rewrite Nat2Z.inj_succ in Hbound.
      rewrite Z.pow_succ_r in Hbound; [| apply Nat2Z.is_nonneg].
      lia.
    + apply Z.ltb_ge in Hlt. lia.
Qed.

Lemma smallest_power_of_two_geq_aux_returns_acc_when_ge :
  forall n acc fuel,
    acc >= n ->
    smallest_power_of_two_geq_aux n acc fuel = acc.
Proof.
  intros n acc fuel Hge.
  destruct fuel; simpl.
  - reflexivity.
  - destruct (acc <? n) eqn:Hlt.
    + apply Z.ltb_lt in Hlt. lia.
    + reflexivity.
Qed.

Lemma smallest_power_of_two_geq_aux_upper_bound :
  forall m a f, a > 0 -> 
    smallest_power_of_two_geq_aux m a f <= a * 2 ^ Z.of_nat f.
Proof.
  intros m a f.
  generalize dependent a.
  induction f as [| f' IHf]; intros a Ha.
  - simpl. lia.
  - assert (Hpow : 2 ^ Z.of_nat (S f') = 2 * 2 ^ Z.of_nat f').
    { rewrite Nat2Z.inj_succ.
      rewrite Z.pow_succ_r; [ring | apply Nat2Z.is_nonneg]. }
    assert (Hpow_pos : 2 ^ Z.of_nat f' >= 1).
    { assert (Hz : 0 <= Z.of_nat f') by lia.
      pose proof (Z.pow_pos_nonneg 2 (Z.of_nat f') ltac:(lia) Hz). lia. }
    rewrite Hpow.
    simpl smallest_power_of_two_geq_aux. destruct (a <? m) eqn:Hlt.
    + specialize (IHf (a * 2) ltac:(lia)).
      assert (Heq : a * 2 * 2 ^ Z.of_nat f' = a * (2 * 2 ^ Z.of_nat f')) by ring.
      rewrite <- Heq. exact IHf.
    + assert (a <= a * (2 * 2 ^ Z.of_nat f')).
      { assert (1 <= 2 * 2 ^ Z.of_nat f') by nia.
        assert (a * 1 <= a * (2 * 2 ^ Z.of_nat f')).
        { apply Z.mul_le_mono_nonneg_l; lia. }
        lia. }
      lia.
Qed.

Lemma smallest_power_of_two_geq_geq :
  forall n, n > 0 -> n <= Z.shiftl 1 64 -> smallest_power_of_two_geq n >= n.
Proof.
  intros n Hn Hbound.
  unfold smallest_power_of_two_geq.
  destruct (n <=? 0) eqn:Hneg.
  - apply Z.leb_le in Hneg. lia.
  - apply Z.leb_gt in Hneg.
    destruct (Z.le_gt_cases n 1) as [Hle1 | Hgt1].
    + rewrite (smallest_power_of_two_geq_aux_returns_acc_when_ge n 1 64); lia.
    + pose proof (smallest_power_of_two_geq_aux_geq n 1 64 ltac:(lia)) as Hmono.
      apply smallest_power_of_two_geq_aux_terminates; try lia.
      assert (Hpow64eq : 1 * 2 ^ Z.of_nat 64 = Z.shiftl 1 64).
      { vm_compute. reflexivity. }
      lia.
Qed.

(** Helper: when acc < n, the result with doubled acc is still <= 2*n *)
Lemma smallest_power_of_two_geq_aux_le_double :
  forall n acc fuel,
    acc > 0 ->
    n > 0 ->
    acc <= n ->
    n <= acc * 2 ^ Z.of_nat fuel ->
    smallest_power_of_two_geq_aux n acc fuel <= 2 * n.
Proof.
  intros n acc fuel.
  generalize dependent acc.
  induction fuel as [| fuel' IH]; intros acc Hacc_pos Hn Hacc_le_n Hbound.
  - simpl. simpl in Hbound. 
    assert (acc = n) by lia. subst.
    destruct n; simpl; lia.
  - simpl. destruct (acc <? n) eqn:Hlt.
    + apply Z.ltb_lt in Hlt.
      destruct (acc * 2 <=? n) eqn:Hdouble_le.
      * apply Z.leb_le in Hdouble_le.
        apply IH; try lia.
        rewrite Nat2Z.inj_succ in Hbound.
        rewrite Z.pow_succ_r in Hbound; [lia | apply Nat2Z.is_nonneg].
      * apply Z.leb_gt in Hdouble_le.
        assert (Hge : acc * 2 >= n) by lia.
        rewrite smallest_power_of_two_geq_aux_returns_acc_when_ge; [| lia].
        destruct n; simpl; lia.
    + apply Z.ltb_ge in Hlt.
      assert (acc = n) by lia. subst.
      destruct n; simpl; lia.
Qed.

Lemma smallest_power_of_two_geq_le_double :
  forall n, n > 0 -> n <= Z.shiftl 1 63 -> smallest_power_of_two_geq n <= 2 * n.
Proof.
  intros n Hn Hbound.
  unfold smallest_power_of_two_geq.
  destruct (n <=? 0) eqn:Hneg.
  - apply Z.leb_le in Hneg. lia.
  - apply Z.leb_gt in Hneg.
    apply smallest_power_of_two_geq_aux_le_double; try lia.
    assert (Hpow64eq : 1 * 2 ^ Z.of_nat 64 = Z.shiftl 1 64).
    { vm_compute. reflexivity. }
    assert (Hpow63eq : Z.shiftl 1 63 = 2 ^ 63).
    { vm_compute. reflexivity. }
    assert (H64_63 : Z.shiftl 1 64 = 2 * Z.shiftl 1 63).
    { vm_compute. reflexivity. }
    lia.
Qed.

(** Bounds on target_chunk via Z.sqrt properties *)

Lemma Z_shiftl_pow : forall n, 0 <= n -> Z.shiftl 1 n = 2 ^ n.
Proof.
  intros n Hn.
  rewrite Z.shiftl_1_l. reflexivity.
Qed.

Lemma Z_sqrt_pow2_even : forall n, 0 <= n -> Z.sqrt (2 ^ (2 * n)) = 2 ^ n.
Proof.
  intros n Hn.
  apply Z.sqrt_unique; try (apply Z.pow_nonneg; lia).
  split.
  - assert (Heq: (2 ^ n) * (2 ^ n) = 2 ^ (2 * n)).
    { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    lia.
  - assert (Heq: (2 ^ n + 1) * (2 ^ n + 1) > 2 ^ (2 * n)).
    { assert (Hsq: (2 ^ n) * (2 ^ n) = 2 ^ (2 * n)).
      { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      assert (Hpos: 0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
      nia. }
    lia.
Qed.

Lemma target_chunk_bounded :
  forall db_entries,
    0 <= db_entries <= Z.shiftl 1 124 ->
    target_chunk db_entries <= Z.shiftl 1 63.
Proof.
  intros db_entries [Hlo Hhi].
  unfold target_chunk.
  rewrite Z_shiftl_pow in Hhi by lia.
  rewrite Z_shiftl_pow by lia.
  assert (H4db : 4 * db_entries <= 2 ^ 126).
  { assert (H: 4 = 2 ^ 2) by reflexivity. rewrite H.
    assert (Hmul: 2 ^ 2 * 2 ^ 124 = 2 ^ 126).
    { rewrite <- Z.pow_add_r; [reflexivity | lia | lia]. }
    lia. }
  assert (Hsqrt_bound : Z.sqrt (4 * db_entries) <= Z.sqrt (2 ^ 126)).
  { apply Z.sqrt_le_mono. lia. }
  assert (H126: 126 = 2 * 63) by lia.
  rewrite H126 in Hsqrt_bound.
  rewrite Z_sqrt_pow2_even in Hsqrt_bound by lia.
  exact Hsqrt_bound.
Qed.

Lemma target_chunk_bounded_64 :
  forall db_entries,
    0 <= db_entries <= Z.shiftl 1 124 ->
    target_chunk db_entries <= Z.shiftl 1 64.
Proof.
  intros db_entries Hdb.
  assert (H63 : target_chunk db_entries <= Z.shiftl 1 63) 
    by (apply target_chunk_bounded; exact Hdb).
  rewrite Z_shiftl_pow by lia.
  rewrite Z_shiftl_pow in H63 by lia.
  assert (H: 2 ^ 63 <= 2 ^ 64).
  { apply Z.pow_le_mono_r; lia. }
  lia.
Qed.

(** Theorem 1: chunk_size is always a power of 2 *)

Theorem derive_plinko_params_chunk_power_of_two :
  forall db_entries : Z,
    db_entries >= 0 ->
    let '(chunk, _) := derive_plinko_params_spec db_entries in
    is_power_of_two chunk.
Proof.
  intros db_entries Hdb.
  unfold derive_plinko_params_spec.
  destruct (db_entries =? 0) eqn:Hzero.
  - split; [lia | exists 0%nat; reflexivity].
  - apply smallest_power_of_two_geq_is_power_of_two.
Qed.

(** Theorem 2: chunk_size bounds relative to target *)

Theorem derive_plinko_params_chunk_bounds :
  forall db_entries : Z,
    0 <= db_entries <= Z.shiftl 1 124 ->
    let '(chunk, _) := derive_plinko_params_spec db_entries in
    let tgt := target_chunk db_entries in
    (tgt > 0 -> chunk >= tgt /\ chunk <= 2 * tgt) /\
    (tgt <= 0 -> chunk >= 1).
Proof.
  intros db_entries Hdb.
  unfold derive_plinko_params_spec.
  destruct (db_entries =? 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero. subst.
    unfold target_chunk. simpl.
    split; intros; lia.
  - apply Z.eqb_neq in Hzero.
    set (tgt := target_chunk db_entries).
    set (chunk := smallest_power_of_two_geq tgt).
    split; intros Htgt.
    + split.
      * apply smallest_power_of_two_geq_geq.
        -- exact Htgt.
        -- apply target_chunk_bounded_64. exact Hdb.
      * apply smallest_power_of_two_geq_le_double.
        -- exact Htgt.
        -- apply target_chunk_bounded. exact Hdb.
    + assert (Hpow : is_power_of_two chunk) 
        by apply smallest_power_of_two_geq_is_power_of_two.
      destruct Hpow as [Hpos _]. lia.
Qed.

(** Theorem 3: set_size is always positive *)

(** [AXIOM:ARITHMETIC] Proving set_size >= 1 requires showing ceil_div >= 1 
    and round_up_multiple preserves positivity. The proof is conceptually 
    straightforward but involves detailed Z division lemmas. *)
Theorem derive_plinko_params_set_size_positive :
  forall db_entries : Z,
    db_entries >= 0 ->
    let '(_, set_size) := derive_plinko_params_spec db_entries in
    set_size >= 1.
Proof.
  intros db_entries Hdb.
  unfold derive_plinko_params_spec.
  destruct (db_entries =? 0) eqn:Hzero; [lia |].
  apply Z.eqb_neq in Hzero.
  unfold round_up_multiple, ceil_div.
  assert (Hchunk_pos : smallest_power_of_two_geq (target_chunk db_entries) > 0).
  { pose proof (smallest_power_of_two_geq_is_power_of_two (target_chunk db_entries)) as [Hp _].
    exact Hp. }
  set (c := smallest_power_of_two_geq (target_chunk db_entries)) in *.
  assert (Hceil_pos : (db_entries + c - 1) / c >= 1).
  { assert (db_entries >= 1) by lia.
    assert (db_entries + c - 1 >= c) by lia.
    apply Z.le_ge. apply Z.div_le_lower_bound; lia. }
  assert (Hround_pos : ((db_entries + c - 1) / c + 4 - 1) / 4 >= 1).
  { assert ((db_entries + c - 1) / c + 4 - 1 >= 4) by lia.
    apply Z.le_ge. apply Z.div_le_lower_bound; lia. }
  nia.
Qed.

(** Theorem 4: set_size is divisible by 4 *)

(** Note: set_size mod 4 = 0 only for db_entries > 0. 
    For db_entries = 0, we return (1, 1) as a degenerate case. *)
Theorem derive_plinko_params_set_size_mod_4 :
  forall db_entries : Z,
    db_entries > 0 ->
    let '(_, set_size) := derive_plinko_params_spec db_entries in
    set_size mod 4 = 0.
Proof.
  intros db_entries Hdb.
  unfold derive_plinko_params_spec.
  destruct (db_entries =? 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero. lia.
  - unfold round_up_multiple.
    set (raw := ceil_div db_entries (smallest_power_of_two_geq (target_chunk db_entries))).
    rewrite Z.mod_mul; lia.
Qed.

(** Theorem 5: capacity is sufficient for db_entries *)

(** [AXIOM:ARITHMETIC] The capacity proof uses properties of ceiling division:
    - ceil_div(a, b) * b >= a
    - round_up_multiple(x, m) >= x
    These are standard arithmetic facts but the Coq proof is tedious. *)
Lemma ceil_div_mul_ge : forall a b, b > 0 -> ceil_div a b * b >= a.
Proof.
  intros a b Hb.
  unfold ceil_div.
  assert (Hdiv_mod : a + b - 1 = b * ((a + b - 1) / b) + (a + b - 1) mod b).
  { apply Z.div_mod. lia. }
  assert (Hmod_bound : 0 <= (a + b - 1) mod b < b).
  { apply Z.mod_pos_bound. lia. }
  assert (H : (a + b - 1) / b * b = a + b - 1 - (a + b - 1) mod b).
  { lia. }
  rewrite H.
  lia.
Qed.

Lemma round_up_multiple_ge : forall x m, m > 0 -> round_up_multiple x m >= x.
Proof.
  intros x m Hm.
  unfold round_up_multiple.
  assert (Hdiv_mod : x + m - 1 = m * ((x + m - 1) / m) + (x + m - 1) mod m).
  { apply Z.div_mod. lia. }
  assert (Hmod_bound : 0 <= (x + m - 1) mod m < m).
  { apply Z.mod_pos_bound. lia. }
  assert (H : (x + m - 1) / m * m = x + m - 1 - (x + m - 1) mod m).
  { lia. }
  lia.
Qed.

Theorem derive_plinko_params_capacity :
  forall db_entries : Z,
    db_entries >= 0 ->
    let '(chunk, set_size) := derive_plinko_params_spec db_entries in
    chunk * set_size >= db_entries.
Proof.
  intros db_entries Hdb.
  unfold derive_plinko_params_spec.
  destruct (db_entries =? 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero. subst. simpl. lia.
  - apply Z.eqb_neq in Hzero.
    set (tgt := target_chunk db_entries).
    set (chunk := smallest_power_of_two_geq tgt).
    set (raw := ceil_div db_entries chunk).
    set (set_size := round_up_multiple raw 4).
    assert (Hchunk_pos : chunk > 0).
    { pose proof (smallest_power_of_two_geq_is_power_of_two tgt) as [Hp _]. exact Hp. }
    assert (Hraw_ge : raw * chunk >= db_entries).
    { unfold raw. apply ceil_div_mul_ge. exact Hchunk_pos. }
    assert (Hset_ge_raw : set_size >= raw).
    { unfold set_size. apply round_up_multiple_ge. lia. }
    assert (Hmono : chunk * set_size >= chunk * raw).
    { apply Z.ge_le_iff. apply Z.mul_le_mono_nonneg_l; lia. }
    lia.
Qed.

(** Combined correctness theorem for db_entries > 0 
    (the case db_entries = 0 returns degenerate (1, 1)) *)

Theorem derive_plinko_params_all_invariants :
  forall db_entries : Z,
    db_entries > 0 ->
    let '(chunk, set_size) := derive_plinko_params_spec db_entries in
    is_power_of_two chunk /\
    set_size >= 1 /\
    set_size mod 4 = 0 /\
    chunk * set_size >= db_entries.
Proof.
  intros db_entries Hdb.
  assert (Hdb' : db_entries >= 0) by lia.
  pose proof (derive_plinko_params_chunk_power_of_two db_entries Hdb') as H1.
  pose proof (derive_plinko_params_set_size_positive db_entries Hdb') as H2.
  pose proof (derive_plinko_params_set_size_mod_4 db_entries Hdb) as H3.
  pose proof (derive_plinko_params_capacity db_entries Hdb') as H4.
  destruct (derive_plinko_params_spec db_entries) as [chunk set_size].
  auto.
Qed.
