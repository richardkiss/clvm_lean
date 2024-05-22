import Mathlib


def nonempty (as : List α) := as.length > 0


def is_empty (as : List Nat) : Bool :=
  match as with
  | [] => True
  | _ => False


def is_msb_clear (as : List Nat) :=
  match as with
  | [] => false
  | v :: _ => v &&& 128 ≠ 128


def is_msb_set (as : List Nat) :=
  match as with
  | [] => false
  | v :: _ => v &&& 128 = 128


theorem is_msb_clear_nonempty {as: List Nat}: is_msb_clear as → nonempty as := by
  intro h
  cases as with
  | nil => contradiction
  | cons head tail =>
    unfold nonempty
    unfold List.length
    simp


theorem is_msb_set_nonempty {as: List Nat}: is_msb_set as → nonempty as := by
  intro h
  cases as with
  | nil => contradiction
  | cons head tail =>
    unfold nonempty
    unfold List.length
    simp
