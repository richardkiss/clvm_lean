import Init.Data.ByteArray


#eval ByteArray.empty
#eval (ByteArray.empty.push 15).push 17


inductive Node : Type
| atom : ByteArray -> Node
| pair : (Node × Node) -> Node


def uint8_to_hex (n : Nat) : String :=
  let hex_chars := "0123456789abcdef".toList
  let hex_digit (n : Nat) : Char :=
    if n < 16 then hex_chars.get! n else 'X'

  String.mk ([hex_digit (n / 16), hex_digit (n % 16)])

#eval uint8_to_hex 8
#eval uint8_to_hex 0xf8
#eval uint8_to_hex 255


def b2h (bytes : ByteArray) : String :=
  String.join (bytes.toList.map (λ b => uint8_to_hex b.toNat))

#eval b2h (ByteArray.mk #[100, 200])
#eval b2h (ByteArray.mk #[72, 101, 108, 108, 111])


#eval (ByteArray.empty.push 15).push 17

#check UInt8.mk 72
#check (UInt8)
#eval (UInt8.mk 100)


#eval [72, 100]
#eval [72, 100].map UInt8.mk
#eval Array.mk ([72, 100].map UInt8.mk)
#eval ByteArray.mk (Array.mk ([72, 100].map UInt8.mk))
#eval ByteArray.mk (Array.mk ([72, 100]))
#eval ByteArray.mk #[100, 200]
#eval #[200, 300, 500]

def foo: ByteArray := ByteArray.mk #[100, 200]
#eval foo
#eval foo[0]

def MAX_SINGLE_BYTE: UInt8 := 0x7f

#eval MAX_SINGLE_BYTE.shiftRight 1

def atom_to_bytes (atom : ByteArray) : ByteArray :=
  let size: Nat := atom.size
  if size == 0 then
    ByteArray.mk #[0x80]
  else if (size == 1) ∧ (atom[0]! <= MAX_SINGLE_BYTE) then
    atom
  else if size <= 0x40 then
    ByteArray.mk #[(0x80.lor size).toUInt8] ++ atom
  else if size <= 0x2000 then
    ByteArray.mk #[(0xC0.lor (size.shiftRight 8)).toUInt8, ((size.shiftRight 0).land 0xFF).toUInt8] ++ atom
  else if size <= 0x100000 then
    ByteArray.mk #[(0xE0.lor (size.shiftRight 16)).toUInt8, ((size.shiftRight 8).land 0xFF).toUInt8, ((size.shiftRight 0).land 0xFF).toUInt8] ++ atom
  else
    ByteArray.mk #[]
--   throw (IO.userError "Input must be greater than 10")
/-      elif size < 0x8000000:
        size_blob = bytes(
            [
                0xF0 | (size.shiftRight 24),
                (size.shiftRight 16) & 0xFF,
                (size.shiftRight 8) & 0xFF,
                (size.shiftRight 0) & 0xFF,
            ]
        )
    elif size < 0x400000000:
            size_blob = bytes(
            [
                0xF8 | (size.shiftRight 32),
                (size.shiftRight 24) & 0xFF,
                (size.shiftRight 16) & 0xFF,
                (size.shiftRight 8) & 0xFF,
                (size.shiftRight 0) & 0xFF,
            ]
        )
-/

#eval atom_to_bytes ByteArray.empty
#eval atom_to_bytes (ByteArray.mk #[100])
#eval atom_to_bytes (ByteArray.mk #[100, 200])
#eval atom_to_bytes (ByteArray.mk #[100, 200, 211])

def node_to_bytes (node : Node) : ByteArray :=
  match node with
  | Node.atom bytes => atom_to_bytes bytes
  | Node.pair (n1, n2) => ByteArray.mk #[0xff] ++ node_to_bytes n1 ++ node_to_bytes n2


#eval node_to_bytes (Node.atom ByteArray.empty)
















def Pair : Type := (Node × Node)

def n1: Node := Node.atom ByteArray.empty

def pair: Pair := ⟨n1, n1⟩

def n2: Node := Node.pair pair
