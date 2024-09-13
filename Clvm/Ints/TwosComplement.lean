import Mathlib

import Clvm.Ints.ListHelpers
import Clvm.Ints.Bases


def base_b_be_to_neg (digits: List Nat) (b: Nat) : Int :=
  Int.negSucc (b ^ digits.length - base_b_be_to_nat digits b - 1)

#eval base_b_be_to_neg [1, 2, 1, 0] 3

/--
For a given n, this structure returns the `k` value s.t. `pow=b^k` exceeds `n` along
with proofs that `pow = b ^ k` and `pow > n`.
-/

structure MinPowerExceeding (n b: Nat) :=
  k: Nat
  pow: Nat
  eq: pow = b ^ k
  gt: pow > n
  ngtz_kgtz: n > 0 → k > 0


def min_power_of_b_exceeding_n_and_exponent (b n: Nat) (hb: b>1) : MinPowerExceeding n b:=
  let rec loop (b_k k: Nat) ( hbk: b_k > 0 ) (eq: b_k = b ^ k) (ngtz_kgtz: b_k > n → n > 0 → k > 0): MinPowerExceeding n b :=
    if hn: b_k > n then
      MinPowerExceeding.mk k b_k eq hn (ngtz_kgtz hn)
    else
      let new_b_k := b_k * b
      have h_new_b_k : new_b_k = b_k * b := by rfl
      have _: n + 1 - b_k * b < n + 1 - b_k := by
        refine Nat.sub_lt_sub_left ?_ ?_
        linarith
        exact (lt_mul_iff_one_lt_right hbk).mpr hb
      have h_newbk: new_b_k > 0 := by exact lt_mul_of_lt_of_one_lt' hbk hb
      have h_new_eq: new_b_k = b ^ (k+1) := by
        rw [h_new_b_k, eq]
        ring
      have new_ngtz_kgtz: new_b_k > n → n > 0 → k + 1 > 0 := by
        intros _ _
        simp
      loop new_b_k (k + 1) h_newbk h_new_eq new_ngtz_kgtz
  termination_by (n + 1 - b_k)

  have ngtz_kgtz: 1 > n → n > 0 → 0 > 0 := by
    intros h0 h1
    linarith
  loop 1 0 (by decide) (by linarith) ngtz_kgtz


#eval (min_power_of_b_exceeding_n_and_exponent 2 12 (by linarith)).pow


example: (min_power_of_b_exceeding_n_and_exponent b n hb).pow > n := by exact
  (min_power_of_b_exceeding_n_and_exponent b n hb).gt



#eval (min_power_of_b_exceeding_n_and_exponent 2 131000 (by linarith)).pow


def neg_to_base_b_be {b: Nat} (z: Int) (hb: b>1): List Nat :=
  nat_to_base_b_be_partial (power_exp.pow - z.natAbs) (power_exp.k - 1) hb
    where power_exp := min_power_of_b_exceeding_n_and_exponent b z.natAbs hb


example: Int.natAbs (Int.negSucc n0) > 0 := by simp


example: n > 0 → (min_power_of_b_exceeding_n_and_exponent b n hb).k > 0 := by
  intro hn
  exact (min_power_of_b_exceeding_n_and_exponent b n hb).ngtz_kgtz hn


lemma neg_z: z < 0 → Int.negSucc (Int.natAbs z - 1) = z := by
  induction z with
  | ofNat n0 =>
    intro h0
    simp at h0
    linarith
  | negSucc n0 => simp


lemma abs_neg_gt_0 : z < 0 → Int.natAbs z > 0 := by
  intro hz
  unfold Int.natAbs
  cases z with
  | ofNat n => simp only [gt_iff_lt] ; simp only [Int.ofNat_eq_coe] at hz ; linarith
  | negSucc _ => linarith


theorem round_trip_neg {hb: b > 1}: (z < 0) → base_b_be_to_neg (neg_to_base_b_be z hb) b = z := by
  intro h_z_lt_0
  unfold neg_to_base_b_be
  unfold base_b_be_to_neg
  unfold base_b_be_to_nat
  simp [partial_round_trip]
  simp [nat_to_base_b_partial_length]
  simp [neg_to_base_b_be.power_exp]
  have h_abs_neg_gt_0: Int.natAbs z > 0 := abs_neg_gt_0 h_z_lt_0
  have h_k_gt_0: (min_power_of_b_exceeding_n_and_exponent b (Int.natAbs z) hb).k ≥ 1 := by
    exact (min_power_of_b_exceeding_n_and_exponent b (Int.natAbs z) hb).ngtz_kgtz h_abs_neg_gt_0
  simp [h_k_gt_0]
  rw [← (min_power_of_b_exceeding_n_and_exponent b (Int.natAbs z) hb).eq]
  have h_pow_ge : Int.natAbs z ≤ (min_power_of_b_exceeding_n_and_exponent b (Int.natAbs z) hb).pow := by
    have h_pow_gt: Int.natAbs z < (min_power_of_b_exceeding_n_and_exponent b (Int.natAbs z) hb).pow := (min_power_of_b_exceeding_n_and_exponent b (Int.natAbs z) hb).gt
    linarith
  simp [h_pow_ge, Nat.sub_sub_self]
  exact neg_z h_z_lt_0
    where kmpb := min_power_of_b_exceeding_n_and_exponent b z.natAbs hb


lemma prefix_idemopotent_neg_to_base_b_be {hb: b>1} : base_b_be_to_neg ((b-1) :: ns) b = base_b_be_to_neg ns b := by
  unfold base_b_be_to_neg
  simp [base_b_be_to_nat]
  rw [Nat.pow_add]
  simp [base_b_be_to_nat_inner]
  conv_lhs => rw [base_b_be_to_nat_inner_extract_k]
  rw [Nat.sub_add_eq, Nat.mul_comm, ← Nat.mul_sub_right_distrib, Nat.sub_sub_self]
  simp
  linarith


lemma prefix_idemopotent_nat_to_base_b_be {b: Nat} (ns: List Nat) : base_b_be_to_nat (0 :: ns) b = base_b_be_to_nat ns b := by
  simp [base_b_be_to_nat, base_b_be_to_nat_inner]


def neg_to_twos_comp (z: Int) : List Nat :=
  if is_msb_set as_nat then
    as_nat
  else
    0xff :: as_nat
  where as_nat := neg_to_base_b_be z (by decide : 256 > 1)


def pos_to_twos_comp (n: Nat) : List Nat :=
  if is_msb_set as_nat then
    0x00 :: as_nat
  else
    as_nat
  where as_nat := nat_to_base_b_be n (by decide : 256 > 1)


def int_to_twos_comp (z: Int) : List Nat :=
  if z = 0 then
    []
  else if z < 0 then
    neg_to_twos_comp z
  else
    pos_to_twos_comp z.natAbs


theorem pos_to_twos_comp_has_msb_not_set : ¬ is_msb_set (pos_to_twos_comp z) := by
  unfold pos_to_twos_comp
  if h1: is_msb_set (pos_to_twos_comp.as_nat z) = true then
    simp [h1]
    rfl
  else
    simp [h1]


def twos_comp_offset_for_value (v: Nat) : Int :=
  if v = 0 then 1 else twos_comp_offset_for_value (v / 256) * 256



def nat_val_as_neg_int (z: Int) : Int :=
  z - twos_comp_offset_for_value z.natAbs


def twos_comp_to_int (twos_comp: List Nat) : Int :=
  if is_msb_set twos_comp then
    base_b_be_to_neg twos_comp 256
  else
    base_b_be_to_nat twos_comp 256


lemma round_trip_twos_comp_zero : twos_comp_to_int (int_to_twos_comp 0) = 0 := by rfl


lemma round_trip_twos_comp_pos : z > 0 → twos_comp_to_int (int_to_twos_comp z) = z := by
  intro h_z_gt_0
  rw [int_to_twos_comp]
  have h_z_ne_0 : z ≠ 0 := by linarith
  have h_z_nlt_0 : ¬ z < 0 := by linarith
  simp [h_z_ne_0, h_z_nlt_0]
  rw [twos_comp_to_int]
  simp [pos_to_twos_comp_has_msb_not_set]
  unfold pos_to_twos_comp
  if h: is_msb_set (pos_to_twos_comp.as_nat (Int.natAbs z)) = true then
    simp [h]
    unfold pos_to_twos_comp.as_nat
    rw [prefix_idemopotent_nat_to_base_b_be]
    simp [nat_round_trip]
    linarith
  else
    simp [h]
    unfold pos_to_twos_comp.as_nat
    simp [nat_round_trip]
    linarith


lemma neg_to_twos_comp_has_msb_set: is_msb_set (neg_to_twos_comp z) = true := by
  unfold neg_to_twos_comp
  if h: is_msb_set (neg_to_twos_comp.as_nat z) = true then
    simp [h]
  else
    simp [h]
    rfl


lemma round_trip_twos_comp_neg : z < 0 → twos_comp_to_int (int_to_twos_comp z) = z := by
  intro h_z_lt_0
  rw [int_to_twos_comp]
  have h_z_ne_0 : z ≠ 0 := by linarith
  simp [h_z_ne_0, h_z_lt_0]
  rw [twos_comp_to_int]
  simp [neg_to_twos_comp_has_msb_set]
  unfold neg_to_twos_comp
  if h: (is_msb_set (neg_to_twos_comp.as_nat z) = true) then
    simp [h]
    unfold neg_to_twos_comp.as_nat
    exact (round_trip_neg h_z_lt_0)
  else
    simp [h]
    have h255: 255 = 256 - 1 := by rfl
    rw [h255]
    rw [prefix_idemopotent_neg_to_base_b_be]
    unfold neg_to_twos_comp.as_nat
    apply round_trip_neg
    exact h_z_lt_0
    simp


@[simp]
theorem round_trip_twos_comp : twos_comp_to_int (int_to_twos_comp z) = z := by
  if h0: z = 0 then
    rw [h0]
    exact round_trip_twos_comp_zero
  else if h1: z < 0 then
    exact round_trip_twos_comp_neg h1
  else
    have h2: z > 0 := by
      by_contra h3
      have h4: z = 0 := by linarith
      simp [h4] at h0
    exact round_trip_twos_comp_pos h2
