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
  let rec inner_func (depth: Nat) (n: Nat) (acc: Array UInt8) : Array UInt8 :=
    if depth = 0 then
      acc
    else
      if n < 256 then
        #[UInt8.ofNat n]
      else
        inner_func (depth - 1) (n >>> 8) (#[UInt8.ofNat (n % 256)] ++ acc)
  inner_func n n #[]


def int_to_atom (n: Int) : Array UInt8 :=
  if n < 0 then
    let as_nat : Nat := (n + (1 <<< (8 * 8))).toNat
    nat_to_atom as_nat
  else
    nat_to_atom n.toNat
