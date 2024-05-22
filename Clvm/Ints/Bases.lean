-- goals:
-- show that our simplest formula for getting the nth digit of a number in base b is correct
--
-- show that the round-trip works, ie. is idempotent
--
-- prove that our more efficient mechanism to generate the digits of a number in base b matches
--  the simple mechanism
--


import Mathlib

import Clvm.Ints.ListHelpers


@[simp]
def nth_digit_of_nat_in_base_b_le {b : Nat} (n v: Nat) (_: b>1) : Nat :=
  (v / (b ^ n)) % b


@[simp]
def most_sig_digit_of_v_in_base_b_be {b : Nat} (v digits: Nat) (_: b>1) : Nat :=
  v / (b ^ digits)


def digit_count {b : Nat} (v: Nat) (_: b>1) : Nat :=
  if v = 0 then 0 else 1 + Nat.log b v


def nat_to_base_b_be_partial {b: Nat} (v extra_digits: Nat) (hb: b>1): List Nat :=
  if extra_digits = 0 then
    [v]
  else
    let new_digit := most_sig_digit_of_v_in_base_b_be v extra_digits hb
    new_digit :: nat_to_base_b_be_partial (v - new_digit * b ^ extra_digits) (extra_digits - 1) hb


lemma nat_to_base_b_partial_length_helper {b: Nat} (extra_digits: Nat) (hb: b>1): ∀ v, (nat_to_base_b_be_partial v extra_digits hb).length = extra_digits + 1 := by
  induction extra_digits with
  | zero => simp [nat_to_base_b_be_partial]
  | succ n ih =>
    intro v
    unfold List.length nat_to_base_b_be_partial
    simp
    rw [ih]


lemma nat_to_base_b_partial_length  {b: Nat} (extra_digits: Nat) (hb: b>1): ∀ v, (nat_to_base_b_be_partial v extra_digits hb).length = extra_digits + 1 := by
  exact nat_to_base_b_partial_length_helper extra_digits hb


def nat_to_base_b_be {b: Nat} (v: Nat) (hb: b>1): List Nat :=
  nat_to_base_b_be_partial v ((digit_count v hb) - 1) hb


lemma len_nat_to_base_b_be_partial {b: Nat} (hb: b>1): ∀ d, (∀ v, (nat_to_base_b_be_partial v d hb).length = d + 1) := by
  intros d
  induction d with
  | zero => simp ; simp [nat_to_base_b_be_partial]
  | succ d ih =>
    unfold nat_to_base_b_be_partial
    simp [ih]


def base_b_be_to_nat_inner (acc: Nat) (ds: List Nat) (b: Nat) : Nat :=
  match ds with
  | [] => acc
  | d0 :: tail => base_b_be_to_nat_inner (acc + d0 * b ^ tail.length) tail b


def base_b_be_to_nat := base_b_be_to_nat_inner 0


lemma base_b_be_to_nat_inner_extract_k_helper: ∀ k, base_b_be_to_nat_inner k ds b = k + base_b_be_to_nat_inner 0 ds b := by
  induction ds with
  | nil => unfold base_b_be_to_nat_inner ; simp
  | cons head tail ih =>
    intro k0
    unfold base_b_be_to_nat_inner
    simp
    rw [ih]
    conv_rhs => rw [ih]
    ring


theorem base_b_be_to_nat_inner_extract_k: base_b_be_to_nat_inner k ds b = k + base_b_be_to_nat_inner 0 ds b := by
  exact base_b_be_to_nat_inner_extract_k_helper k


theorem partial_round_trip {b d : Nat} {hb: b > 1}: ∀ n, (base_b_be_to_nat_inner 0 (nat_to_base_b_be_partial n d hb) b = n) := by
  induction d with
  | zero =>
    simp [base_b_be_to_nat_inner, nat_to_base_b_be_partial]
  | succ d0 ih =>
    intro n0
    unfold nat_to_base_b_be_partial
    simp
    unfold base_b_be_to_nat_inner
    simp
    rw [base_b_be_to_nat_inner_extract_k]
    rw [len_nat_to_base_b_be_partial]
    rw [ih]
    have hr: Nat.succ d0 = d0 + 1 := by simp
    rw [hr]
    ring_nf
    rw [Nat.add_comm]
    apply Nat.sub_add_cancel
    rw [Nat.mul_comm]
    simp [Nat.div_mul_le_self n0 (b * b ^ d0)]


theorem nat_round_trip {b n : Nat} {hb: b > 1}: base_b_be_to_nat (nat_to_base_b_be n hb) b = n := by
  unfold nat_to_base_b_be
  unfold base_b_be_to_nat
  exact partial_round_trip n
