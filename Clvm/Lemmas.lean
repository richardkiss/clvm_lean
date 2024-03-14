--import Init.Data.Nat.Bitwise
--import Init.Data.Nat.Lemmas
--import Init.Data.Nat.Init.Lemmas

-- import Mathlib.Tactic.LibrarySearch


-- theorem shift_as_division { k: Nat }: n >>> k = n / (2 ^ k) := by
--  exact Nat.shiftRight_eq_div_pow n k


theorem shift_decreasing : n>0 → n >>> 8 < n := by
  intro h
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_self h (by decide)
