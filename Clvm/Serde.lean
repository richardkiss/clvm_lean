import Clvm.Node


def MAX_SINGLE_BYTE: Nat := 0x7f

/-
def my_panic :=
  let t := [1]
  t[1]!
-/

structure ParsedNode where
  node: Node
  bytes: List Nat


def atom_to_serialized_bytes (atom : List Nat) : List Nat :=
  let size: Nat := atom.length
  if size == 0 then
    [0x80]
  else if (size == 1) ∧ (atom[0]! <= MAX_SINGLE_BYTE) then
    atom
  else if size <= 0x40 then
    [(0x80.lor size)] ++ atom
  else if size <= 0x2000 then
    [(0xC0.lor (size.shiftRight 8)), ((size.shiftRight 0).land 0xFF)] ++ atom
  else if size <= 0x100000 then
    [(0xE0.lor (size.shiftRight 16)), ((size.shiftRight 8).land 0xFF), ((size.shiftRight 0).land 0xFF)] ++ atom
  else if size <= 0x8000000 then
    [(0xF0.lor (size.shiftRight 24)), ((size.shiftRight 16).land 0xFF), ((size.shiftRight 8).land 0xFF), ((size.shiftRight 0).land 0xFF)] ++ atom
  else if size <= 0x400000000 then
    [(0xF8.lor (size.shiftRight 32)), ((size.shiftRight 24).land 0xFF), ((size.shiftRight 16).land 0xFF), ((size.shiftRight 8).land 0xFF), ((size.shiftRight 0).land 0xFF)] ++ atom
  else
    -- let _o := my_panic
    []


def node_to_bytes (node : Node) : List Nat :=
  match node with
  | Node.atom bytes => atom_to_serialized_bytes bytes
  | Node.pair left right => [0xff] ++ node_to_bytes left ++ node_to_bytes right


def node_to_string (n : Node) : String :=
  match n with
  | Node.atom bytes => b2h bytes
  | Node.pair left right => "(" ++ (node_to_string left) ++ ", " ++ (node_to_string right) ++ ")"


def n2h (n : Node) : String :=
  b2h (node_to_bytes n)


def List.extract (as: List α) (start finish: Nat) : List α :=
  as.drop start |>.take (finish - start)


def bytes_to_atom (bytes: List Nat) : Option ParsedNode :=
  match bytes with
  | [] => none
  | o :: rest =>
      if o = 0x80 then
        some (ParsedNode.mk (Node.nil) rest)
      else
      if o <= MAX_SINGLE_BYTE then
        let new_bytes := rest
        let node := Node.atom [o]
        let _proof := rest.length < bytes.length
        some (ParsedNode.mk node new_bytes)
      else
        if o.land 0xc0 = 0x80 then
          let atom_size := (o.land 0x3f)
          let atom_start_offset := 1
          let new_bytes_offset := atom_start_offset + atom_size
          if bytes.length + 1 < new_bytes_offset then
            none
          else
            -- generate sublist
            let atom := bytes.extract atom_start_offset new_bytes_offset
            let new_bytes := bytes.extract new_bytes_offset bytes.length
            some (ParsedNode.mk (Node.atom atom) new_bytes)
        else
          if o.land 0xe0 = 0xc0 then
            let atom_start_offset := 2
            if bytes.length < atom_start_offset then
              none
            else
              let atom_size := (o.land 0x1f).shiftLeft 8 + (bytes[1]!)
              let new_bytes_offset := atom_start_offset + atom_size
              if bytes.length + 1 < new_bytes_offset then
                none
              else
                let atom := bytes.extract atom_start_offset new_bytes_offset
                let new_bytes := bytes.extract new_bytes_offset bytes.length
                some (ParsedNode.mk (Node.atom atom) new_bytes)
          else
            if o.land 0xf0 = 0xe0 then
              let atom_start_offset := 3
              if bytes.length < atom_start_offset then
                none
              else
                let atom_size := (o.land 0xf).shiftLeft 16 + (bytes[1]!).shiftLeft 24 + (bytes[2]!)
                let new_bytes_offset := atom_start_offset + atom_size
                if bytes.length + 1 < new_bytes_offset then
                  none
                else
                  let atom := bytes.extract atom_start_offset new_bytes_offset
                  let new_bytes := bytes.extract new_bytes_offset bytes.length
                  some (ParsedNode.mk (Node.atom atom) new_bytes)
            else
              none


def bytes_to_parsed_node (bytes: List Nat) : Except ((List Nat) × String) ParsedNode :=
  match bytes with
  | [] => Except.err bytes "end of stream"
  | o :: rest=>
    if o = 255 then
      do
      let left ← bytes_to_parsed_node rest
      have: List.length left.bytes < Nat.succ (List.length rest) := by
        sorry
      let right ← bytes_to_parsed_node left.bytes
      return ParsedNode.mk (Node.pair left.node right.node) right.bytes
    else
      match bytes_to_atom bytes with
      | none => Except.err bytes "end of stream"
      | some result => Except.ok result
  termination_by bytes.length


def bytes_to_node (bytes: List Nat) : Except ((List Nat) × String) Node := do
  let result ← bytes_to_parsed_node bytes
  return result.node


def skip_node (bytes: List Nat) : Except ((List Nat) × String) (List Nat) := do
  let result ← bytes_to_parsed_node bytes
  return result.bytes


def skip_node! (bytes: List Nat) : List Nat :=
  match bytes_to_parsed_node bytes with
  | Except.ok result => result.bytes
  | Except.error _ => []
