import Clvm.Result


def hex_nibble_to_byte (c: Char) : Result Nat Char :=
  let c := c.toLower
  if c.toNat >= 48 && c.toNat <= 57 then
    Result.ok (c.toNat - 48)
  else if c.toNat >= 97 && c.toNat <= 102 then
    Result.ok (c.toNat - 87)
  else
    Result.err c "invalid hex digit"


def list_char_2b (s: List Char) : Result (List Nat) (List Char) :=
  match s with
  | c1 :: c2 :: rest =>
    match hex_nibble_to_byte c1, hex_nibble_to_byte c2, list_char_2b rest with
    | Result.ok c1, Result.ok c2, Result.ok r => Result.ok ((c1 * 16 + c2) :: r)
    | Result.err c e, _, _ => Result.err [c] e
    | _, Result.err c e, _ => Result.err [c] e
    | _, _, Result.err c e => Result.err c e
  | [c] => Result.err [c] "odd number of hex digits"
  | [] => Result.ok []


def h2b_list (s: String) : Result (List Nat) String :=
  match list_char_2b s.data with
  | Result.ok r => Result.ok r
  | Result.err c e => Result.err (String.mk c) e


@[simp]
def h2b (s: String) : Result (Array Nat) String :=
  match (h2b_list s) with
  | Result.ok r => Result.ok r.toArray
  | Result.err _ e => Result.err s e



def nat_to_hex (n : Nat) : String :=
  let hex_chars := "0123456789abcdef".toList
  let hex_digit (n : Nat) : Char :=
    if n < 16 then hex_chars.get! n else 'X'
  String.mk ([hex_digit (n / 16), hex_digit (n % 16)])


def b2h (bytes : List Nat) : String :=
  String.join (bytes.map (λ b => nat_to_hex b))


def b2h_uint8 (bytes : List UInt8) : String :=
  b2h (bytes.map (λ b => b.toNat))


def List.hex (bytes: List Nat) : String :=
  b2h bytes
