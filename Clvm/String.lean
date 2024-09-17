import Mathlib


theorem string_take_drop (s: String) (n: Nat): s = s.take n ++ s.drop n := by
  ext k a
  rw [String.data_append]
  rw [String.data_drop]
  rw [String.data_take]
  rw [List.take_append_drop]
