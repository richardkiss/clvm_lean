import Clvm.Atom


lemma powers_cancel (k n: Nat): k * (2 ^ (n + 1) / 2) = k * 2 ^ n := by
  rw [Nat.div_eq_of_eq_mul_left]
  simp
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
      simp [h_c]
      if h_k: k = 0 then
        simp [h_k]
      else
        simp [h_k]
        ring_nf
        simp [powers_cancel k n]

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
  simp [pos_to_twos_comp]
  simp [pos_to_twos_comp.as_nat]
  simp [nat_to_base_b_be]
  unfold nat_to_base_b_be_partial
  simp [digit_count]
  have h_n_ne_0: n ≠ 0 := by linarith
  simp [h_n_ne_0]
  have h_n_lt_256: n < 256 := by linarith
  simp [h_n_lt_256]
  simp [is_msb_set]
  obtain h_and_0 := (and_shifted_too_far_0 7 1 n)
  simp [h_n128] at h_and_0
  simp [HAnd.hAnd, AndOp.and, Nat.land]
  simp [h_and_0]


lemma proof_for_small_int (z: Int) (h_z_gt_0: z > 0) (h_z_lt_128: z < 128) : ∀ n ∈ [z.natAbs], n ≤ 255 := by
  induction z with
  | negSucc _ => simp at h_z_gt_0
  | ofNat n =>
    if h_n: n ≤ 255 then
      simp [h_n]
    else
      simp [h_n] at h_z_lt_128
      linarith


theorem zero_to_atom: int_to_atom 0 = Atom.mk [] (by decide) := by rfl


theorem small_int_to_atom (z: Int) {h_z_gt_0: z > 0} {h_z_lt_128: z < 128}
  : int_to_atom z = ⟨ [z.natAbs], (proof_for_small_int z h_z_gt_0 h_z_lt_128) ⟩ := by

  unfold int_to_atom
  unfold int_to_twos_comp
  simp [h_z_gt_0, h_z_lt_128]

  have h_z_ne_0: z ≠ 0 := by linarith
  simp [h_z_ne_0]
  have h_z_nlt_0: ¬ z < 0 := by linarith
  simp [h_z_nlt_0]
  apply small_pos_to_twos_comp
  simp only [gt_iff_lt, Int.natAbs_pos, ne_eq, h_z_ne_0, not_false_eq_true]

  cases z with
  | ofNat k =>
    by_contra h1
    simp only [Int.ofNat_eq_coe, Int.natAbs_ofNat, not_lt] at h1
    simp [h1] at h_z_lt_128
    linarith
  | negSucc k => simp only [gt_iff_lt, Int.negSucc_not_pos] at h_z_gt_0

--#print small_int_to_atom

/-
lemma int_lt_nat_lt (m n: Nat): Int.ofNat m ≤ Int.ofNat n → m ≤ n := by
  intro h

  have z : Int.ofNat m + Int.ofNat (n - m) = Int.ofNat n := by sorry
  rw [← z] at h
  have h_sum: n = m + (n - m) := by
    sorry
  rw [h_sum]
  linarith


example {k: Nat} : ∀ (z: Int), z ≥ 0 → z ≤ k → z.natAbs ≤ k := by
  intro z h_z_ge_0 h_z_lt_k
  induction z with
  | negSucc _ => simp at h_z_ge_0
  | ofNat n =>
    simp [int_nat_abs_id]
    by_contra h
    obtain z := int_nat_abs_id n
    induction k with
    | zero =>
      by_contra h
      simp at h
      induction n with
      | zero => simp at h
      | succ n ih =>
        simp at h_z_lt_k
        linarith
    | succ n0 ih =>
      simp at h_z_lt_k
      sorry



lemma pos_z_of_nat_abs: z ≥ 0 → z = Int.ofNat z.natAbs := by
  intro h
  induction z with
  | ofNat k => simp
  | negSucc k => simp at h


lemma proof_for_small (z: Int) (h_z_gt_0: z > 0) (h_z_lt_128: z < 128) : ∀ n ∈ [z.natAbs], n ≤ 255 := by
  have h_n_gt_0: z.natAbs > 0 := by
    simp
    simp at h_z_gt_0

  have h_z_ge_0: z ≥ 0 := by linarith

  obtain z0 := pos_z_of_nat_abs h_z_ge_0
  rw [z0] at h_z_lt_128



  have h_n_lt_128: z.natAbs < 128 := by
    have h1: z = Int.ofNat z.natAbs := by

      sorry
    rw [h1]
    unfold Int.natAbs
    simp
    rw [h1]
    simp

    sorry

  exact proof_for_small_nat z.natAbs h_n_gt_0 h_n_lt_128


theorem small_int_to_atom1 (z: Int) (h_z_gt_0: z > 0) (h_z_lt_128: z < 128)
  : int_to_atom z = ⟨ [z.natAbs], (proof_for_small z h_z_gt_0 h_z_lt_128) ⟩ := by
  unfold int_to_atom
  unfold int_to_twos_comp
  simp [h_z_gt_0, h_z_lt_128]

  have h_z_ne_0: z ≠ 0 := by linarith
  simp [h_z_ne_0]
  have h_z_nlt_0: ¬ z < 0 := by linarith
  simp [h_z_nlt_0]

  apply small_pos_to_twos_comp
  simp only [gt_iff_lt, Int.natAbs_pos, ne_eq, h_z_ne_0, not_false_eq_true]

  cases z with
  | ofNat k =>
    by_contra h1
    simp only [Int.ofNat_eq_coe, Int.natAbs_ofNat, not_lt] at h1
    simp [h1] at h_z_lt_128
    linarith
  | negSucc k => simp only [gt_iff_lt, Int.negSucc_not_pos] at h_z_gt_0
-/


lemma int_nat_abs_id (k: Nat): (Int.ofNat k).natAbs = k := by rfl


lemma int_of_nat_sum_dist (m n: Nat) : Int.ofNat (m + n) = (Int.ofNat m) + (Int.ofNat n) := by rfl


lemma int_of_nat_eq (k m: Nat): Int.ofNat k = Int.ofNat m → k = m := by
  intro h
  simp at h
  exact h


lemma int_of_nat_sum (k m n: Nat): Int.ofNat k + Int.ofNat m = Int.ofNat n → k + m = n := by
  intro h0
  rw [← int_of_nat_sum_dist k m] at h0
  apply int_of_nat_eq (k+m) n
  exact h0
