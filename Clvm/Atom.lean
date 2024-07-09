import Mathlib
import Mathlib.Init.Set

import Clvm.Ints.Basic


/-! ## Atom has a list of `Nat` values and a proof that they are all under 255 -/
/-! We might consider using UInt8 at some point -/

structure Atom :=
  data: List Nat
  lt: ∀ n ∈ data, n ≤ 255
  deriving Repr


def Atom.nil : Atom := ⟨[], (by decide)⟩


def Atom.length (a: Atom) : Nat := a.data.length


instance : Inhabited Atom where
  default := Atom.nil


/-! Some coercion conveniences -/

instance : CoeOut Atom (List Nat) := ⟨fun a => a.data⟩

instance : CoeOut Atom (Array Nat) := ⟨fun a => a.data.toArray⟩


def max_255 (n: Nat) : Nat := if n ≤ 255 then n else 255


theorem map_prop_dist_for_all {P: β → Prop } { as: List α } { f: α → β } :  (∀ a, P (f a)) → ∀ b ∈ as.map f, (P b) := by
  intro h0
  intro b0
  simp
  intro a0
  intro _
  intro h2
  rewrite [← h2]
  exact h0 a0


theorem max_yields_limited_list (bs: List Nat): ∀ b ∈ bs.map max_255, b ≤ 255 := by
  apply map_prop_dist_for_all
  simp [max_255]
  intro b0
  by_cases h: b0 ≤ 255
  simp [h]
  simp [h]


/-! A simple cast that pins too-large values to 255 -/

def atom_cast (a: List Nat) : Atom :=
  let new_a : List Nat := a.map max_255
  have h_new_a: new_a = a.map max_255 := by simp
  let proof : ∀ n ∈ new_a, n ≤ 255 := by
    rw [h_new_a]
    exact max_yields_limited_list a
  ⟨new_a, proof⟩


instance : Coe (List Nat) Atom where
  coe := atom_cast


def atom_to_nat (atom: Atom) : Nat :=
  base_b_be_to_nat_inner 0 atom.data 256


def atom_to_int (atom: Atom) : Int :=
  twos_comp_to_int atom.data


instance CoeAtomInt : Coe Atom Int := ⟨atom_to_int⟩


def Atom.to := atom_cast


def byte_count_for_nat (n: Nat) : Nat :=
  let rec inner_func (depth: Nat) (n: Nat) : Nat :=
    if depth = 0 then 1 else
      if n < 256 then 1 else 1 + inner_func (depth - 1) (n >>> 8)
  inner_func n n


example {a b: Nat} {hb: b ≥ 1} : a - ((a/b) * b) < b := by
  rw [mod_formula]
  exact Nat.mod_lt a hb


example {a b : Nat} {ha: a ≥ 1} {hb: b > 0 }: a - b < a := by
  exact Nat.sub_lt ha hb


theorem atom_bounded: ∀ n ∈ int_to_twos_comp z, n ≤ 255 := by
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


def int_to_atom (z: Int) : Atom :=
  Atom.mk (int_to_twos_comp z) int_to_twos_comp_bounded


@[simp]
theorem round_trip_int (z: Int) : atom_to_int (int_to_atom z) = z := by
  simp [atom_to_int, int_to_atom, round_trip_twos_comp]
