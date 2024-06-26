def hex_nibble_to_byte (c: Char) : UInt8 :=
  let c := c.toLower
  if c.toNat >= 48 && c.toNat <= 57 then
    (c.toNat - 48).toUInt8
  else if c.toNat >= 97 && c.toNat <= 102 then
    (c.toNat - 87).toUInt8
  else
    0


def h2b (s: String) : Array UInt8 :=
  let vals: List UInt8 := s.data.map hex_nibble_to_byte
  let filtered: List UInt8 := vals.enum.filterMap (λ (i, v) => if i % 2 == 0 then none else some ((vals[i-1]!.shiftLeft) 4 + v))
  filtered.toArray


def nat_to_hex (n : Nat) : String :=
  let hex_chars := "0123456789abcdef".toList
  let hex_digit (n : Nat) : Char :=
    if n < 16 then hex_chars.get! n else 'X'

  String.mk ([hex_digit (n / 16), hex_digit (n % 16)])


def b2h (bytes : Array UInt8) : String :=
  String.join (bytes.toList.map (λ b => nat_to_hex b.toNat))
