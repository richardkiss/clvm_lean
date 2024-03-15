import Clvm.Hex
import Clvm.Node


def MAX_SINGLE_BYTE: Nat := 0x7f

/-
def my_panic :=
  let t := [1]
  t[1]!
-/

def atom_to_serialized_bytes (atom : Array Nat) : Array Nat :=
  let size: Nat := atom.size
  if size == 0 then
    #[0x80]
  else if (size == 1) ∧ (atom[0]! <= MAX_SINGLE_BYTE) then
    atom
  else if size <= 0x40 then
    #[(0x80.lor size)] ++ atom
  else if size <= 0x2000 then
    #[(0xC0.lor (size.shiftRight 8)), ((size.shiftRight 0).land 0xFF)] ++ atom
  else if size <= 0x100000 then
    #[(0xE0.lor (size.shiftRight 16)), ((size.shiftRight 8).land 0xFF), ((size.shiftRight 0).land 0xFF)] ++ atom
  else if size <= 0x8000000 then
    #[(0xF0.lor (size.shiftRight 24)), ((size.shiftRight 16).land 0xFF), ((size.shiftRight 8).land 0xFF), ((size.shiftRight 0).land 0xFF)] ++ atom
  else if size <= 0x400000000 then
    #[(0xF8.lor (size.shiftRight 32)), ((size.shiftRight 24).land 0xFF), ((size.shiftRight 16).land 0xFF), ((size.shiftRight 8).land 0xFF), ((size.shiftRight 0).land 0xFF)] ++ atom
  else
    -- let _o := my_panic
    #[]


def node_to_bytes (node : Node) : Array Nat :=
  match node with
  | Node.atom bytes => atom_to_serialized_bytes bytes
  | Node.pair left right => #[0xff] ++ node_to_bytes left ++ node_to_bytes right


def node_to_string (n : Node) : String :=
  match n with
  | Node.atom bytes => b2h bytes
  | Node.pair left right => "(" ++ (node_to_string left) ++ ", " ++ (node_to_string right) ++ ")"


def n2h (n : Node) : String :=
  b2h (node_to_bytes n)


structure DResult where
  bytes: Array Nat
  node: Node


def bytes_to_atom (bytes: Array Nat) : Option DResult :=
  match bytes[0]? with
  | none => none
  | some o =>
      if o = 0x80 then
        let new_bytes := bytes.extract 1 bytes.size
        some (DResult.mk new_bytes (Node.nil))
      else
      if o <= MAX_SINGLE_BYTE then
        let new_bytes := bytes.extract 1 bytes.size
        let node := Node.atom (bytes.extract 0 1)
        let _proof := new_bytes.size < bytes.size
        some (DResult.mk new_bytes node)
      else
        if o.land 0xc0 = 0x80 then
          let atom_size := (o.land 0x3f)
          let atom_start_offset := 1
          let new_bytes_offset := atom_start_offset + atom_size
          if bytes.size + 1 < new_bytes_offset then
            none
          else
            let atom := bytes.extract atom_start_offset new_bytes_offset
            let new_bytes := bytes.extract new_bytes_offset bytes.size
            some (DResult.mk new_bytes (Node.atom atom))
        else
          if o.land 0xe0 = 0xc0 then
            let atom_start_offset := 2
            if bytes.size < atom_start_offset then
              none
            else
              let atom_size := (o.land 0x1f).shiftLeft 8 + (bytes[1]!)
              let new_bytes_offset := atom_start_offset + atom_size
              if bytes.size + 1 < new_bytes_offset then
                none
              else
                let atom := bytes.extract atom_start_offset new_bytes_offset
                let new_bytes := bytes.extract new_bytes_offset bytes.size
                some (DResult.mk new_bytes (Node.atom atom))
          else
            if o.land 0xf0 = 0xe0 then
              let atom_start_offset := 3
              if bytes.size < atom_start_offset then
                none
              else
                let atom_size := (o.land 0xf).shiftLeft 16 + (bytes[1]!).shiftLeft 24 + (bytes[2]!)
                let new_bytes_offset := atom_start_offset + atom_size
                if bytes.size + 1 < new_bytes_offset then
                  none
                else
                  let atom := bytes.extract atom_start_offset new_bytes_offset
                  let new_bytes := bytes.extract new_bytes_offset bytes.size
                  some (DResult.mk new_bytes (Node.atom atom))
            else
              none



def bytes_to_node_inner (heartbeat_count: Nat) (bytes: Array Nat) : Result DResult DResult :=
  if heartbeat_count = 0 then
    Result.err (DResult.mk bytes Node.nil) "heartbeat_count is 0"
  else
    let new_count := heartbeat_count - 1
    match bytes[0]? with
    | none => Result.err (DResult.mk bytes Node.nil) "end of stream"
    | some o =>
      if o = 255 then
        match bytes_to_node_inner new_count (bytes.extract 1 bytes.size)  with
        | Result.ok left =>
          match bytes_to_node_inner new_count left.bytes with
          | Result.ok right =>
              let node := Node.pair left.node right.node
              Result.ok (DResult.mk right.bytes node)
          | _other => _other
        | _other => _other
      else
        match bytes_to_atom bytes with
        | none => Result.err (DResult.mk bytes Node.nil) "end of stream"
        | some result => Result.ok result


def bytes_to_node (bytes: Array Nat) : Node :=
  match bytes_to_node_inner (bytes.size*2) bytes with
  | Result.err _ _ => Node.atom ([0x46, 0x41, 0x49, 0x4c])
  | Result.ok result => result.node
