-- import Mathlib

import Clvm.Lemmas

structure Atom :=
  data: List Nat
  lt: Prop -- ∀ n ∈ data, n < 256
  deriving Repr

instance : CoeOut Atom (List Nat) := ⟨fun a => a.data⟩

instance : CoeOut Atom (Array Nat) := ⟨fun a => a.data.toArray⟩

instance : CoeOut Atom (Array UInt8) := ⟨fun a => a.data.toArray.map UInt8.ofNat⟩


def Atom.length (a: Atom) : Nat := a.data.length

def atom_cast (a: List Nat) : Atom :=
  let new_a : List Nat := a.filter (fun n => n < 256)
  /-let proof : ∀ n ∈ a, n < 256 := by
    intro n
    intro h
    sorry
    -/
  ⟨new_a, true⟩


instance : Coe (List Nat) Atom where
  coe := atom_cast


instance : CoeOut (Array Nat) Atom where
  coe := (fun a => atom_cast a.toList)


instance : CoeOut (Array UInt8) Atom where
  coe := fun a => atom_cast (a.map (fun x => x.val)).toList


instance : Inhabited Atom where
  default := ⟨ [], true ⟩



def atom_to_nat (atom: Atom) : Nat :=
  let rec inner_func (atom: List Nat) (acc: Nat) : Nat :=
    match atom with
    | [] => acc
    | a::b => inner_func b ((acc <<< 8) + a)
  inner_func atom 0



def atom_to_int (atom: Atom) : Int :=
  let as_nat := atom_to_nat atom
  match (atom: List Nat) with
  | [] => as_nat
  | a :: _ => if a < 0x80 then as_nat else as_nat - (1 <<< (8 * atom.length))


def nat_to_atom (n: Nat) : Atom :=
  let rec inner_func (n: Nat) : Array UInt8 :=
    if h256: n >= 256 then
      have h0: n > 0 := Nat.zero_lt_of_lt h256
      have : n >>> 8 < n := shift_decreasing h0
      (inner_func (n >>> 8)) ++  #[n.toUInt8]
    else
      #[n.toUInt8]
  if n = 0 then
    Atom.mk [] true
  else
    let as_uint8_array := inner_func n
    let as_list := as_uint8_array.toList
    /-
    let proof : ∀ n ∈ as_list, n < 256 := by
      intro n
      intro h
      have h2: n.val < 256 := by sorry
      exact h2
      -/
    let as_nat_list : List Nat := as_list.map (fun x => x.val)
    Atom.mk as_nat_list true



instance CoeAtomInt : Coe Atom Int := ⟨atom_to_int⟩

def byte_count_for_nat (n: Nat) : Nat :=
  let rec inner_func (depth: Nat) (n: Nat) : Nat :=
    if depth = 0 then 1 else
      if n < 256 then 1 else 1 + inner_func (depth - 1) (n >>> 8)
  inner_func n n


def int_to_atom (n: Int) : Atom :=
  let abs_n : Nat := n.natAbs
  let is_negative := n < 0
  let as_nat : Nat := if is_negative then
      let add_amount : Nat := (1 <<< (8 * (byte_count_for_nat abs_n)))
      add_amount - abs_n
    else
      abs_n
  let as_nat_atom := nat_to_atom as_nat
  match as_nat_atom.data with
  | v :: _ =>
      if is_negative then
        if v &&& 0x80 = 0x80 then as_nat_atom else Atom.mk (255 :: as_nat_atom.data) true
      else
        if v &&& 0x80 = 0 then as_nat_atom else Atom.mk (0 :: as_nat_atom.data) true
  | [] => as_nat_atom



structure Bytes (n : Nat) :=
  data: List Nat
  lengthIs: data.length = n
  deriving Repr

-- instance CoeBytesNAtom { n: Nat } : Coe (Bytes n) (Array UInt8) := ⟨fun b => b.data⟩


abbrev Bytes32 := Bytes 32

instance : Inhabited Bytes32 where
  default := ⟨ [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], by decide ⟩

-- TODO: make this less lame
def Bytes32.mk (data: List Nat) : Bytes32 :=
  if h: data.length = 32 then
    ⟨data, h⟩
  else
    default


instance CoeBytes32Atom : Coe Bytes32 Atom := ⟨fun b => Atom.mk b.data true⟩
