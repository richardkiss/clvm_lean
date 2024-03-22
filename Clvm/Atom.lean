import Mathlib
import Mathlib.Init.Set

import Clvm.Bases
import Clvm.Lemmas

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
  let as_nat := atom_to_nat atom
  match (atom: List Nat) with
  | [] => as_nat
  | a :: _ => if a < 0x80 then as_nat else as_nat - (1 <<< (8 * atom.length))


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


def int_to_atom (z: Int) : Atom :=
  let as_nat : Nat := match z with
    | Int.ofNat n => n
    | Int.negSucc n =>
        let add_amount : Nat := (1 <<< (8 * (byte_count_for_nat (n + 1))))
        add_amount - n - 1

  let as_nat_atom := nat_to_atom as_nat

  match z with
  | Int.ofNat _ =>
      match as_nat_atom.data with
      | v :: _ => if v &&& 0x80 = 0 then as_nat_atom else Atom.to (0 :: as_nat_atom.data)
      | [] => as_nat_atom
  | Int.negSucc _ =>
      match as_nat_atom.data with
      | v :: _ => if v &&& 0x80 = 0x80 then as_nat_atom else Atom.to (255 :: as_nat_atom.data)
      | [] => as_nat_atom



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
