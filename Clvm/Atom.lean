def atom_to_nat (atom: Array UInt8) : Nat :=
  let rec inner_func (atom: List UInt8) (acc: Nat) : Nat :=
    match atom with
    | [] => acc
    | a::b => inner_func b ((acc <<< 8) + a.toNat)
  inner_func atom.toList 0


def atom_to_int (atom: Array UInt8) : Int :=
  let as_nat := atom_to_nat atom
  match atom[0]? with
  | some v => if v < 0x80 then as_nat else as_nat - (1 <<< (8 * atom.size))
  | none => as_nat


def nat_to_atom (n: Nat) : Array UInt8 :=
  let rec inner_func (depth: Nat) (n: Nat) : Array UInt8 :=
    if depth = 0 then
      #[]
    else
      if n < 256 then
        #[UInt8.ofNat n]
      else
        (inner_func (depth - 1) (n >>> 8)) ++  #[UInt8.ofNat (n % 256)]
  inner_func n n


def byte_size (n: Nat) : Nat :=
  let rec inner_func (depth: Nat) (n: Nat) : Nat :=
    if depth = 0 then 1 else
      if n < 256 then 1 else 1 + inner_func (depth - 1) (n >>> 8)
  inner_func n n


def int_to_atom (n: Int) : Array UInt8 :=
  let abs_n : Nat := n.natAbs
  let is_negative := n < 0
  let as_nat : Nat := if is_negative then
      let add_amount : Nat := (1 <<< (8 * (byte_size abs_n)))
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



#eval int_to_atom (-129)

#eval byte_size (129)
#eval (1 <<< (8 * (byte_size 129)))
#eval 256-129


#eval nat_to_atom (0x12345678)

def bigneg := (-0x12345678 : Int)

#eval (1 <<< (8 * (byte_size bigneg.natAbs)))

#eval int_to_atom (-(Int.ofNat 0x12345678))
#eval (-(Int.ofNat 12345678))


#eval int_to_atom 0xff0000
