import Clvm.Lemmas

abbrev Atom := Array UInt8


instance : Inhabited Atom where
  default := #[]


def atom_to_nat (atom: Atom) : Nat :=
  let rec inner_func (atom: List UInt8) (acc: Nat) : Nat :=
    match atom with
    | [] => acc
    | a::b => inner_func b ((acc <<< 8) + a.toNat)
  inner_func atom.toList 0



def atom_to_int (atom: Atom) : Int :=
  let as_nat := atom_to_nat atom
  match atom[0]? with
  | some v => if v < 0x80 then as_nat else as_nat - (1 <<< (8 * atom.size))
  | none => as_nat


@[simp]
def nat_to_atom (n: Nat) : Atom :=
  let rec inner_func (n: Nat) : Atom :=
    if h256: n >= 256 then
      have h0: n > 0 := Nat.zero_lt_of_lt h256
      have : n >>> 8 < n := shift_decreasing h0
      (inner_func (n >>> 8)) ++  #[n.toUInt8]
    else
      #[n.toUInt8]
  if n = 0 then
    #[]
  else
    inner_func n


instance CoeAtomInt : Coe Atom Int := ⟨atom_to_int⟩

def byte_count_for_nat (n: Nat) : Nat :=
  let rec inner_func (depth: Nat) (n: Nat) : Nat :=
    if depth = 0 then 1 else
      if n < 256 then 1 else 1 + inner_func (depth - 1) (n >>> 8)
  inner_func n n


@[simp]
def int_to_atom (n: Int) : Atom :=
  let abs_n : Nat := n.natAbs
  let is_negative := n < 0
  let as_nat : Nat := if is_negative then
      let add_amount : Nat := (1 <<< (8 * (byte_count_for_nat abs_n)))
      add_amount - abs_n
    else
      abs_n
  let as_nat_atom := nat_to_atom as_nat
  match as_nat_atom[0]? with
  | some v =>
      if is_negative then
        if v &&& 0x80 = 0x80 then as_nat_atom else #[255] ++ as_nat_atom
      else
        if v &&& 0x80 = 0 then as_nat_atom else #[0] ++ as_nat_atom
  | none => as_nat_atom



structure Bytes (n : Nat) :=
  data: Array UInt8
  sizeIs: data.size = n
  deriving Repr

-- instance CoeBytesNAtom { n: Nat } : Coe (Bytes n) (Array UInt8) := ⟨fun b => b.data⟩


abbrev Bytes32 := Bytes 32

-- TODO: make this less lame
def Bytes32.mk (data: Array UInt8) : Bytes32 :=
  if h: data.size = 32 then
    ⟨data, h⟩
  else
    let s := Array.mkArray 32 0
    ⟨s, by decide⟩


instance CoeBytes32Atom : Coe Bytes32 Atom := ⟨fun b => b.data⟩
