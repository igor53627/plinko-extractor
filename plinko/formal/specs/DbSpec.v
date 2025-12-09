(** DbSpec.v - Specification for derive_plinko_params from db.rs *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.
Require Import Plinko.Specs.CommonTypes.

Open Scope Z_scope.

(** Helper: smallest power of 2 >= n *)

Fixpoint smallest_power_of_two_geq_aux (n : Z) (acc : Z) (fuel : nat) : Z :=
  match fuel with
  | O => acc
  | S fuel' =>
      if acc <? n then smallest_power_of_two_geq_aux n (acc * 2) fuel'
      else acc
  end.

Definition smallest_power_of_two_geq (n : Z) : Z :=
  if n <=? 0 then 1
  else smallest_power_of_two_geq_aux n 1 64.

(** Target chunk computation: floor(2 * sqrt(db_entries)) *)

Definition target_chunk (db_entries : Z) : Z :=
  Z.sqrt (4 * db_entries).

(** Spec definition mirroring Rust logic *)

Definition derive_plinko_params_spec (db_entries : Z) : Z * Z :=
  if db_entries =? 0 then (1, 1)
  else
    let tgt := target_chunk db_entries in
    let chunk_size := smallest_power_of_two_geq tgt in
    let set_size_raw := ceil_div db_entries chunk_size in
    let set_size := round_up_multiple set_size_raw 4 in
    (chunk_size, set_size).

(** Key predicates for invariants *)

Definition chunk_is_power_of_two (chunk : Z) : Prop :=
  is_power_of_two chunk.

Definition chunk_ge_target (chunk db_entries : Z) : Prop :=
  chunk >= target_chunk db_entries.

Definition chunk_le_double_target (chunk db_entries : Z) : Prop :=
  chunk <= 2 * target_chunk db_entries \/ target_chunk db_entries <= 0.

Definition set_size_positive (set_size : Z) : Prop :=
  set_size >= 1.

Definition set_size_multiple_of_4 (set_size : Z) : Prop :=
  (set_size mod 4 = 0)%Z.

Definition capacity_sufficient (chunk set_size db_entries : Z) : Prop :=
  chunk * set_size >= db_entries.

(** Combined validity predicate *)

Definition valid_plinko_params (chunk set_size db_entries : Z) : Prop :=
  chunk_is_power_of_two chunk /\
  chunk_ge_target chunk db_entries /\
  chunk_le_double_target chunk db_entries /\
  set_size_positive set_size /\
  set_size_multiple_of_4 set_size /\
  capacity_sufficient chunk set_size db_entries.

(** Auxiliary lemmas for correctness proof *)

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
      rewrite Z.pow_succ_r in Hbound; [lia | apply Nat2Z.is_nonneg].
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

(** Specification correctness statement *)

Theorem derive_plinko_params_spec_valid :
  forall db_entries : Z,
    db_entries > 0 ->
    db_entries <= Z.shiftl 1 124 ->
    let '(chunk, set_size) := derive_plinko_params_spec db_entries in
    valid_plinko_params chunk set_size db_entries.
Proof.
  intros db_entries Hdb Hbound.
  unfold valid_plinko_params.
  unfold chunk_is_power_of_two, chunk_ge_target, chunk_le_double_target,
         set_size_positive, set_size_multiple_of_4, capacity_sufficient.
  unfold derive_plinko_params_spec.
  destruct (db_entries =? 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero. lia.
  - apply Z.eqb_neq in Hzero.
    set (tgt := target_chunk db_entries).
    set (chunk := smallest_power_of_two_geq tgt).
    set (raw := ceil_div db_entries chunk).
    set (ss := round_up_multiple raw 4).
    assert (Hchunk_pow2 : is_power_of_two chunk)
      by apply smallest_power_of_two_geq_is_power_of_two.
    assert (Hchunk_pos : chunk > 0) by (destruct Hchunk_pow2; lia).
    split; [exact Hchunk_pow2 |].
    split.
    + destruct (Z.le_gt_cases tgt 0) as [Htgt_le | Htgt_gt].
      * assert (Hgeq : chunk >= 1).
        { pose proof (smallest_power_of_two_geq_is_power_of_two tgt) as [Hp _]. lia. }
        unfold tgt. lia.
      * apply smallest_power_of_two_geq_geq; [lia |].
        unfold tgt, target_chunk.
        assert (Hsqrt124_64 : Z.sqrt (4 * Z.shiftl 1 124) <= Z.shiftl 1 64).
        { rewrite !Z.shiftl_1_l. 
          replace (4 * 2 ^ 124) with (2 ^ 63 * 2 ^ 63).
          2: { rewrite <- Z.pow_add_r by lia. reflexivity. }
          rewrite Z.sqrt_square by (apply Z.pow_nonneg; lia).
          apply Z.pow_le_mono_r; lia. }
        assert (H4db : Z.sqrt (4 * db_entries) <= Z.sqrt (4 * Z.shiftl 1 124)).
        { apply Z.sqrt_le_mono. lia. }
        lia.
    + split.
      * destruct (Z.le_gt_cases tgt 0) as [Htgt_le | Htgt_gt].
        -- right. unfold tgt. exact Htgt_le.
        -- left. apply smallest_power_of_two_geq_le_double; [lia |].
           unfold tgt, target_chunk.
           assert (Hsqrt124_63 : Z.sqrt (4 * Z.shiftl 1 124) <= Z.shiftl 1 63).
           { rewrite !Z.shiftl_1_l. 
             replace (4 * 2 ^ 124) with (2 ^ 63 * 2 ^ 63).
             2: { rewrite <- Z.pow_add_r by lia. reflexivity. }
             rewrite Z.sqrt_square by (apply Z.pow_nonneg; lia).
             lia. }
           assert (H4db : Z.sqrt (4 * db_entries) <= Z.sqrt (4 * Z.shiftl 1 124)).
           { apply Z.sqrt_le_mono. lia. }
           lia.
      * split.
        -- unfold ss, raw.
           assert (Hceil_pos : ceil_div db_entries chunk >= 1).
           { unfold ceil_div.
             assert (db_entries >= 1) by lia.
             assert (db_entries + chunk - 1 >= chunk) by lia.
             apply Z.le_ge. apply Z.div_le_lower_bound; lia. }
           assert (Hround_pos : round_up_multiple (ceil_div db_entries chunk) 4 >= 1).
           { unfold round_up_multiple.
             assert ((ceil_div db_entries chunk + 4 - 1) / 4 >= 1).
             { assert (ceil_div db_entries chunk + 4 - 1 >= 4) by lia.
               apply Z.le_ge. apply Z.div_le_lower_bound; lia. }
             nia. }
           exact Hround_pos.
        -- split.
           ++ unfold ss. unfold round_up_multiple.
              rewrite Z.mod_mul; lia.
           ++ unfold ss, raw.
              assert (Hraw_ge : ceil_div db_entries chunk * chunk >= db_entries).
              { unfold ceil_div.
                assert (Hdiv_mod : db_entries + chunk - 1 = 
                        chunk * ((db_entries + chunk - 1) / chunk) + 
                        (db_entries + chunk - 1) mod chunk).
                { apply Z.div_mod. lia. }
                assert (Hmod_bound : 0 <= (db_entries + chunk - 1) mod chunk < chunk).
                { apply Z.mod_pos_bound. lia. }
                nia. }
              assert (Hset_ge_raw : round_up_multiple (ceil_div db_entries chunk) 4 >= 
                                    ceil_div db_entries chunk).
              { unfold round_up_multiple.
                assert (Hdiv_mod : ceil_div db_entries chunk + 4 - 1 = 
                        4 * ((ceil_div db_entries chunk + 4 - 1) / 4) + 
                        (ceil_div db_entries chunk + 4 - 1) mod 4).
                { apply Z.div_mod. lia. }
                assert (Hmod_bound : 0 <= (ceil_div db_entries chunk + 4 - 1) mod 4 < 4).
                { apply Z.mod_pos_bound. lia. }
                nia. }
              assert (Hmono : chunk * round_up_multiple (ceil_div db_entries chunk) 4 >= 
                              chunk * ceil_div db_entries chunk).
              { apply Z.ge_le_iff. apply Z.mul_le_mono_nonneg_l; lia. }
              lia.
Qed.
