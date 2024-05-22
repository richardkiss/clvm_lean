import Clvm.Ints.TwosComplement


lemma mod_formula (a b: Nat) : a - ((a/b) * b) = a % b := by
  refine Nat.sub_eq_of_eq_add' ?h
  exact (Nat.div_add_mod' a b).symm


example {a b: Nat} {hb: b ≥ 1} : a - ((a/b) * b) < b := by
  rw [mod_formula]
  exact Nat.mod_lt a hb


lemma nat_to_base_b_be_partial_bounded_helper {b: Nat} {hb: b > 1}: ∀ d0, ∀ d, ∀ v, d < d0 → v < b ^ (d + 1) → ∀ n ∈ nat_to_base_b_be_partial v d hb, n ≤ b - 1  := by
  -- as long as d is large enough for a given v value, all digits that come out of
  -- nat_to_base_b_be_partial are bounded by b - 1
  intro d0
  induction d0 with
  | zero => simp
  | succ d0 ih =>
    intro d
    intro v
    intro h
    intro h1
    unfold nat_to_base_b_be_partial
    simp
    if hd: d = 0 then
      simp [hd]
      simp [hd] at h1
      exact Nat.le_sub_one_of_lt h1
    else
      simp [hd]
      constructor
      have h2: v / b ^ d < b := by
        exact Nat.div_lt_of_lt_mul h1
      exact Nat.le_sub_one_of_lt h2
      have hd_ge_1: d ≥ 1 := by
        exact Nat.one_le_iff_ne_zero.mpr hd
      have h3: d - 1 < d0 := by
        refine Nat.sub_lt_right_of_lt_add ?H h
        exact hd_ge_1
      have h_bd: b ^ d ≥ 1 := by
        have hb0: b > 0 := by linarith
        have hbd0: b ^ d > 0 := by
          exact pow_pos hb0 d
        exact hbd0
      have h4: (v - v / b ^ d * b ^ d) < b ^ (d - 1 + 1) := by
        simp [hd_ge_1]
        rw [mod_formula]
        exact Nat.mod_lt v h_bd
      exact ih (d-1) (v - v / b ^ d * b ^ d) h3 h4


lemma nat_to_base_b_be_partial_bounded {b v: Nat} {hb: b > 1} {d: Nat} (h: v < b ^ (d + 1)) :
    ∀ n ∈ nat_to_base_b_be_partial v d hb, n ≤ b - 1 := by
  have hdd: d < d + 1 := by linarith
  exact (nat_to_base_b_be_partial_bounded_helper (d+1) d v hdd h)


example {a b : Nat} {ha: a ≥ 1} {hb: b > 0 }: a - b < a := by
  exact Nat.sub_lt ha hb


lemma nat_to_base_b_be_partial_form_bounded: z ≠ 0 → ∀ n ∈ nat_to_base_b_be_partial ((neg_to_base_b_be.power_exp z neg_to_twos_comp.as_nat.proof_1).pow - Int.natAbs z)
      ((neg_to_base_b_be.power_exp z neg_to_twos_comp.as_nat.proof_1).k - 1) neg_to_twos_comp.as_nat.proof_1,
      n ≤ 255 := by
        intro h_z_ne_0
        apply nat_to_base_b_be_partial_bounded
        have h_z_1: (neg_to_base_b_be.power_exp z neg_to_twos_comp.as_nat.proof_1).pow = 256 ^ (neg_to_base_b_be.power_exp z neg_to_twos_comp.as_nat.proof_1).k := by
          exact (neg_to_base_b_be.power_exp z neg_to_twos_comp.as_nat.proof_1).eq
        rw [h_z_1]
        have h_abs_z_gt_0: Int.natAbs z > 0 := by
          induction z with
          | ofNat a0 =>
            simp [Int.natAbs]
            by_contra h1
            have h2: a0 = 0 := by linarith
            rw [h2] at h_z_ne_0
            simp at h_z_ne_0
          | negSucc _ => simp [Int.natAbs]
        have h_z999: (neg_to_base_b_be.power_exp z neg_to_twos_comp.as_nat.proof_1).k ≥ 1 := by
          apply (neg_to_base_b_be.power_exp z neg_to_twos_comp.as_nat.proof_1).ngtz_kgtz
          exact h_abs_z_gt_0
        simp [h_z999]
        apply Nat.sub_lt
        exact Fin.size_pos'
        exact h_abs_z_gt_0


lemma nat_to_base_b_be_form_bounded {hb: 256 > 1} {n : Nat }: n ≠ 0 → ∀ a ∈ nat_to_base_b_be n hb, a ≤ 255 := by
  intro h_n_ne_0
  unfold nat_to_base_b_be
  unfold digit_count
  simp [h_n_ne_0]
  apply nat_to_base_b_be_partial_bounded
  exact Nat.lt_pow_succ_log_self hb n


theorem int_to_twos_comp_bounded: ∀ n ∈ int_to_twos_comp z, n ≤ 255 := by
  rw [int_to_twos_comp]
  if h_z_0: z = 0 then
    simp [h_z_0]
  else
    simp [h_z_0]
    if h_z_lt_0: z < 0 then
      simp [h_z_lt_0]
      rw [neg_to_twos_comp]
      if h_msb: is_msb_set (neg_to_twos_comp.as_nat z) = true then
        simp [h_msb]
        unfold neg_to_twos_comp.as_nat neg_to_base_b_be
        exact nat_to_base_b_be_partial_form_bounded h_z_0
      else
        simp [h_msb]
        unfold neg_to_twos_comp.as_nat neg_to_base_b_be
        exact nat_to_base_b_be_partial_form_bounded h_z_0
    else
      simp [h_z_lt_0]
      rw [pos_to_twos_comp]
      have h_abs_ne_0: Int.natAbs z ≠ 0 := by exact Int.natAbs_ne_zero.mpr h_z_0
      if h_msb: is_msb_set (pos_to_twos_comp.as_nat (Int.natAbs z)) = true then
        simp [h_msb]
        unfold pos_to_twos_comp.as_nat
        exact nat_to_base_b_be_form_bounded h_abs_ne_0
      else
        simp [h_msb]
        unfold pos_to_twos_comp.as_nat
        exact nat_to_base_b_be_form_bounded h_abs_ne_0
