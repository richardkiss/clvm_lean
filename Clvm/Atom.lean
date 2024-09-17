import Mathlib

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


def clip_255 (n: Nat) : Nat := if n ≤ 255 then n else 255


/--!
If we have a list `as` and P f(a) is true for all a, then P b is true for all b in as.map f.
This is pretty obvious.
-/
theorem map_prop_dist_for_all {P: β → Prop } { as: List α } { f: α → β } :  (∀ a, P (f a)) → ∀ b ∈ as.map f, (P b) := by
  simp_all only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, implies_true]


theorem clip_yields_limited_list (bs: List Nat): ∀ b ∈ bs.map clip_255, b ≤ 255 := by
  apply map_prop_dist_for_all
  simp only [clip_255]
  intro h
  split_ifs <;> simp_all


/-! A simple cast that pins too-large values to 255 -/

def atom_cast (a: List Nat) : Atom :=
  let new_a : List Nat := a.map clip_255
  have h_new_a: new_a = a.map clip_255 := by simp
  let proof : ∀ n ∈ new_a, n ≤ 255 := by
    rw [h_new_a]
    exact clip_yields_limited_list a
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


def int_to_atom (z: Int) : Atom :=
  Atom.mk (int_to_twos_comp z) int_to_twos_comp_bounded


@[simp]
theorem round_trip_int (z: Int) : atom_to_int (int_to_atom z) = z := by
  simp [atom_to_int, int_to_atom, round_trip_twos_comp]
