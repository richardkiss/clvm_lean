import Clvm.Atom


lemma powers_cancel (k n: Nat): k * (2 ^ (n + 1) / 2) = k * 2 ^ n := by
  rw [Nat.div_eq_of_eq_mul_left]
  simp only [Nat.ofNat_pos]
  ring


-- this may be useful with the serde stuff
lemma and_shifted_too_far_0 (b k: Nat): ∀ c, (2 ^ b) > c → Nat.bitwise and c (k * (2 ^ b)) = 0 := by
  induction b with
  | zero => intro c h; simp at h ; simp [h]
  | succ n ih =>
    intro c h
    unfold Nat.bitwise

    if h_c: c = 0 then
      simp [h_c]
    else
      simp only [h_c, ↓reduceIte, mul_eq_zero, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero,
        and_false, not_false_eq_true, pow_eq_zero_iff, OfNat.ofNat_ne_zero, or_false,
        Bool.and_false, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq, ite_eq_left_iff]
      if h_k: k = 0 then
        simp [h_k]
      else
        simp only [h_k, not_false_eq_true, true_implies]
        ring_nf
        simp only [Nat.mul_mod_left, zero_ne_one, and_false, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, mul_div_cancel_right₀, mul_eq_zero, or_false]

        apply ih
        by_contra h1
        simp only [not_lt] at h1
        have: 2 ^ (n + 1) ≤ c := calc
          2 ^ (n + 1) = 2 * 2 ^ n := by ring
          _ ≤ 2 ^ n + 2 ^ n := by linarith
          _ ≤ c / 2 + c / 2 := by linarith
          _ = c / 2 * 2:= by ring
          _ ≤ c := by exact Nat.div_mul_le_self c 2
        linarith


lemma small_pos_to_twos_comp: n > 0 → n < 128 → pos_to_twos_comp n = [n] := by
  intro h_n0 h_n128
  simp only [pos_to_twos_comp]
  simp only [pos_to_twos_comp.as_nat]
  simp only [nat_to_base_b_be]
  unfold nat_to_base_b_be_partial
  simp only [digit_count, most_sig_digit_of_v_in_base_b_be]
  have h_n_ne_0: n ≠ 0 := by linarith
  simp only [h_n_ne_0, ↓reduceIte, add_tsub_cancel_left, Nat.log_eq_zero_iff, Nat.not_ofNat_le_one,
    or_false]
  have h_n_lt_256: n < 256 := by linarith
  simp only [h_n_lt_256, ↓reduceIte, ite_eq_right_iff, List.cons_ne_self, imp_false,
    Bool.not_eq_true]
  simp only [is_msb_set, decide_eq_false_iff_not, ne_eq]
  obtain h_and_0 := (and_shifted_too_far_0 7 1 n)
  simp only [Nat.reducePow, gt_iff_lt, h_n128, one_mul, true_implies] at h_and_0
  simp only [HAnd.hAnd, AndOp.and, Nat.land]
  simp only [h_and_0, OfNat.zero_ne_ofNat, not_false_eq_true]


lemma proof_for_small_int (z: Int) (h_z_gt_0: z > 0) (h_z_lt_128: z < 128) : ∀ n ∈ [z.natAbs], n ≤ 255 := by
  induction z with
  | negSucc _ => simp at h_z_gt_0
  | ofNat n =>
    if h_n: n ≤ 255 then
      simp [h_n]
    else
      simp only [Int.ofNat_eq_coe, Nat.cast_lt_ofNat] at h_z_lt_128
      linarith


theorem zero_to_atom: int_to_atom 0 = Atom.mk [] (by decide) := by rfl


theorem small_int_to_atom (z: Int) {h_z_gt_0: z > 0} {h_z_lt_128: z < 128}
  : int_to_atom z = ⟨ [z.natAbs], (proof_for_small_int z h_z_gt_0 h_z_lt_128) ⟩ := by

  unfold int_to_atom
  unfold int_to_twos_comp
  simp only [Atom.mk.injEq]

  have h_z_ne_0: z ≠ 0 := by linarith
  simp only [h_z_ne_0, ↓reduceIte]
  have h_z_nlt_0: ¬ z < 0 := by linarith
  simp only [h_z_nlt_0, ↓reduceIte]
  apply small_pos_to_twos_comp
  simp only [gt_iff_lt, Int.natAbs_pos, ne_eq, h_z_ne_0, not_false_eq_true]

  cases z with
  | ofNat k =>
    by_contra h1
    simp only [Int.ofNat_eq_coe, Int.natAbs_ofNat, not_lt] at h1
    simp only [Int.ofNat_eq_coe, Nat.cast_lt_ofNat] at h_z_lt_128
    linarith
  | negSucc k => simp only [gt_iff_lt, Int.negSucc_not_pos] at h_z_gt_0
