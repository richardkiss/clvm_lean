import Mathlib
import Mathlib.Init.Set

import Clvm.Bases
import Clvm.Lemmas
import Clvm.TwosComplement

structure Atom :=
  data: List Nat
  lt: ∀ n ∈ data, n ≤ 255
  deriving Repr

instance : CoeOut Atom (List Nat) := ⟨fun a => a.data⟩

instance : CoeOut Atom (Array Nat) := ⟨fun a => a.data.toArray⟩

instance : CoeOut Atom (Array UInt8) := ⟨fun a => a.data.toArray.map UInt8.ofNat⟩


def Atom.nil : Atom := ⟨[], (by decide)⟩

def Atom.length (a: Atom) : Nat := a.data.length


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


def Atom.to (a: List Nat) : Atom :=
  let n_a := a.map max_255
  let proof : ∀ n ∈ n_a, n ≤ 255 := max_yields_limited_list a
  ⟨n_a, proof⟩



def atom_cast (a: List Nat) : Atom :=
  let new_a : List Nat := a.map max_255
  have h_new_a: new_a = a.map max_255 := by simp
  let proof : ∀ n ∈ new_a, n ≤ 255 := by
    rw [h_new_a]
    exact max_yields_limited_list a
  ⟨new_a, proof⟩


instance : Coe (List Nat) Atom where
  coe := atom_cast


instance : CoeOut (Array Nat) Atom where
  coe := (fun a => atom_cast a.toList)


instance : CoeOut (Array UInt8) Atom where
  coe := fun a => atom_cast (a.map (fun x => x.val)).toList



instance : Inhabited Atom where
  default := Atom.nil


def list_nat_to_nat (atom: List Nat) (acc: Nat) : Nat :=
  match atom with
  | [] => acc
  | a::b => list_nat_to_nat b ((acc <<< 8) + a)


def atom_to_nat (atom: Atom) : Nat :=
  list_nat_to_nat atom.data 0


def atom_to_int (atom: Atom) : Int :=
  twos_comp_to_int atom.data


def nat_to_atom (n: Nat) : Atom :=
  let rec inner_func (n: Nat) : Array Nat :=
    if h256: n >= 256 then
      have h0: n > 0 := Nat.zero_lt_of_lt h256
      have : n >>> 8 < n := shift_decreasing h0
      (inner_func (n >>> 8)) ++  #[n % 256]
    else
      #[n % 256]
  if n = 0 then
    Atom.nil
  else
    let as_uint8_array := inner_func n
    let as_list := as_uint8_array.toList
    let as_nat_list : List Nat := as_list.map max_255
    let proof : ∀ n ∈ as_list.map max_255, n ≤ 255 := max_yields_limited_list as_list
    Atom.mk as_nat_list proof



--theorem nat_to_atom_matches_nat_to_base_b_be_256 (n: Nat) {b256: 256 > 1} { hn0: n > 0 } : nat_to_atom n = nat_to_base_b_be n b256 := by
--  sorry
  /-
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [nat_to_atom, nat_to_base_b_be]
    have h: n % 256 = n := by
      cases n % 256 with
      | zero => rfl
      | succ m => exfalso; apply Nat.succ_ne_zero m; assumption
    rw [h]
    rw [ih]
    rfl
-/


--theorem round_trip_nat (n: Nat) : atom_to_nat (nat_to_atom n) = n := by
--  sorry




instance CoeAtomInt : Coe Atom Int := ⟨atom_to_int⟩

def byte_count_for_nat (n: Nat) : Nat :=
  let rec inner_func (depth: Nat) (n: Nat) : Nat :=
    if depth = 0 then 1 else
      if n < 256 then 1 else 1 + inner_func (depth - 1) (n >>> 8)
  inner_func n n

-- set_option maxHeartbeats 1000000

example {b d: Nat}: v < b ^ d.succ → v / b < b ^ d := by sorry

example {a b: Nat}: a < b → a ≤ b - 1 := Nat.le_sub_one_of_lt

#eval 5 % 3

lemma mod_formula (a b: Nat) {hb: b ≥ 1} : a - ((a/b) * b) = a % b := by
  refine Nat.sub_eq_of_eq_add' ?h
  exact (Nat.div_add_mod' a b).symm


example {a b: Nat} {hb: b ≥ 1} : a - ((a/b) * b) < b := by
  rw [mod_formula]
  exact Nat.mod_lt a hb
  exact hb



lemma nat_to_base_b_be_partial_suitable_helper {b: Nat} {hb: b > 1}: ∀ d0, ∀ d, ∀ v, d < d0 → v < b ^ (d + 1) → ∀ n ∈ nat_to_base_b_be_partial v d hb, n ≤ b - 1  := by
  -- as long as d is large enough for a given v value, all digits that come out of
  -- nat_to_base_b_be_partial are "suitable", ie. less than b
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
        assumption
      exact ih (d-1) (v - v / b ^ d * b ^ d) h3 h4


lemma nat_to_base_b_be_partial_suitable {b v: Nat} {hb: b > 1} {d: Nat} (h: v < b ^ (d + 1)) :
    ∀ n ∈ nat_to_base_b_be_partial v d hb, n ≤ b - 1 := by
  have hdd: d < d + 1 := by linarith
  exact (nat_to_base_b_be_partial_suitable_helper (d+1) d v hdd h)

example {a b : Nat} {ha: a ≥ 1} {hb: b > 0 }: a - b < a := by
  exact Nat.sub_lt ha hb

lemma nat_to_base_b_be_partial_form_suitable: z ≠ 0 → ∀ n ∈ nat_to_base_b_be_partial ((neg_to_base_b_be.power_exp z neg_to_twos_comp.as_nat.proof_1).pow - Int.natAbs z)
      ((neg_to_base_b_be.power_exp z neg_to_twos_comp.as_nat.proof_1).k - 1) neg_to_twos_comp.as_nat.proof_1,
      n ≤ 255 := by
        intro h_z_ne_0
        apply nat_to_base_b_be_partial_suitable
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


lemma nat_to_base_b_be_form_suitable {hb: 256 > 1} {n : Nat }: n ≠ 0 → ∀ a ∈ nat_to_base_b_be n hb, a ≤ 255 := by
  intro h_n_ne_0
  unfold nat_to_base_b_be
  unfold digit_count
  simp [h_n_ne_0]
  apply nat_to_base_b_be_partial_suitable
  exact Nat.lt_pow_succ_log_self hb n


theorem atom_suitable: ∀ n ∈ int_to_twos_comp z, n ≤ 255 := by
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
        exact nat_to_base_b_be_partial_form_suitable h_z_0
      else
        simp [h_msb]
        unfold neg_to_twos_comp.as_nat neg_to_base_b_be
        exact nat_to_base_b_be_partial_form_suitable h_z_0
    else
      simp [h_z_lt_0]
      rw [pos_to_twos_comp]
      have h_abs_ne_0: Int.natAbs z ≠ 0 := by exact Int.natAbs_ne_zero.mpr h_z_0
      if h_msb: is_msb_set (pos_to_twos_comp.as_nat (Int.natAbs z)) = true then
        simp [h_msb]
        unfold pos_to_twos_comp.as_nat
        exact nat_to_base_b_be_form_suitable h_abs_ne_0
      else
        simp [h_msb]
        unfold pos_to_twos_comp.as_nat
        exact nat_to_base_b_be_form_suitable h_abs_ne_0


def int_to_atom (z: Int) : Atom :=
  Atom.mk (int_to_twos_comp z) atom_suitable


/-

structure Bytes (n : Nat) :=
  data: List Nat
  lengthIs: data.length = n
  lt: ∀ n ∈ data, n ≤ 255
  deriving Repr

-- instance CoeBytesNAtom { n: Nat } : Coe (Bytes n) (Array UInt8) := ⟨fun b => b.data⟩

abbrev Bytes32 := Bytes 32

instance : Inhabited Bytes32 where
  default := ⟨ [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], by decide, by decide ⟩



instance CoeBytes32Atom : Coe Bytes32 Atom := ⟨fun b => Atom.mk b.data b.lt⟩
-/


theorem round_trip_int (z: Int) : atom_to_int (int_to_atom z) = z := by
  simp [atom_to_int, int_to_atom, round_trip_twos_comp]
