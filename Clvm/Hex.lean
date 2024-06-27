import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Use


def hex_nibble_to_byte (c: Char) : Result Nat Char :=
  let c := c.toLower
  if c.toNat >= 48 && c.toNat <= 57 then
    Result.ok (c.toNat - 48)
  else if c.toNat >= 97 && c.toNat <= 102 then
    Result.ok (c.toNat - 87)
  else
    Result.err c "invalid hex digit"


def hex_pair_to_byte (c1 c2: Char) : Result Nat Char :=
  match hex_nibble_to_byte c1, hex_nibble_to_byte c2 with
  | Result.ok c1, Result.ok c2 => Result.ok (c1 * 16 + c2)
  | Result.err c1 m1, _ => Result.err c1 m1
  | _, Result.err c2 m2 => Result.err c2 m2


def h2b_lc (s: List Char) : Result (List Nat) (List Char) :=
  match s with
  | c1 :: c2 :: rest =>
    match hex_pair_to_byte c1 c2, h2b_lc rest with
    | Result.ok b, Result.ok r => Result.ok (b :: r)
    | Result.err c e, _ => Result.err [c] e
    | _, Result.err cs e => Result.err cs e
  | [c] => Result.err [c] "odd number of hex digits"
  | [] => Result.ok []


def h2b_lc! (s: List Char) : List Nat :=
  match h2b_lc s with
  | Result.ok r => r
  | Result.err _ _ => []


@[simp]
def h2b (s: String) : Result (List Nat) String :=
  match h2b_lc s.data with
  | Result.ok r => Result.ok r
  | Result.err c e => Result.err (String.mk c) e


def h2b! (s: String) : List Nat :=
  match h2b s with
  | Result.ok r => r
  | Result.err _ _ => []



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


theorem h2b_lc_remove_two_chars_helper: is_ok (h2b_lc ([c0, c1] ++ s)) →
    is_ok (hex_pair_to_byte c0 c1) ∧ is_ok (h2b_lc s) := by
  intro h
  obtain ⟨ns, h0⟩ := h
  unfold h2b_lc at h0
  simp at h0
  have p0: is_ok (hex_pair_to_byte c0 c1) := by
    by_contra h1
    obtain ⟨c, s0, h2⟩ := not_ok h1
    simp [h2] at h0
  simp [p0]
  obtain ⟨n0, hn0⟩ := p0
  rw [hn0] at h0
  have p1: is_ok (h2b_lc s) := by
    by_contra h1
    obtain ⟨c, s0, h2⟩ := not_ok h1
    simp [h2] at h0
  exact p1


theorem h2b_lc_remove_two_chars: is_ok (h2b_lc ([c0, c1] ++ s)) → h2b_lc ([c0, c1] ++ s) = Result.ok (h2b_lc! ([c0, c1]) ++ h2b_lc! s) := by
  intro h0
  obtain ⟨ p0, p1 ⟩ := h2b_lc_remove_two_chars_helper h0
  obtain ⟨ns0, hn0⟩ := p0
  obtain ⟨ns1, hn1⟩ := p1
  simp [h2b_lc, h2b_lc!, hn0, hn1, h2b_lc]


theorem take_drop (s : List α) (n: Nat): s = (s.take n) ++ (s.drop n) := by simp [List.take, List.drop]


theorem prefix_len_2 (s: List α) : s.length ≥ 2 → ∃ c0 c1 r, s = [c0, c1] ++ r := by
  intro h_len
  cases s with
  | nil => simp at h_len
  | cons c0 s0 =>
    cases s0 with
    | nil => simp at h_len
    | cons c1 s1 => simp [List.length] at h_len ; simp


theorem h2b_lc_take_drop: is_ok (h2b_lc s) → s.length ≥ 2 → h2b_lc s = Result.ok (h2b_lc! (s.take 2) ++ h2b_lc! (s.drop 2)) := by
  intro h0
  intro h_len

  obtain ⟨c0, c1, r, h2⟩ := prefix_len_2 s h_len
  rw [h2] at h0
  rw [h2]
  rw [(h2b_lc_remove_two_chars h0)]
  simp


theorem h2b_lc_ok : is_ok (h2b s) → is_ok (h2b_lc s.data) := by
  intro h
  by_contra h1
  obtain ⟨c, s0, h2⟩ := not_ok h1
  simp [h2, is_ok] at h


theorem h2b_eq_lc : is_ok (h2b s) → h2b! s = h2b_lc! s.data := by
  intro h
  obtain ⟨ns, h1⟩ := h2b_lc_ok h
  simp [h2b_lc!, h2b!, h2b, h1]


theorem h2b_eq_! : is_ok (h2b s) → h2b s = Result.ok (h2b! s) := by
  intro h
  obtain ⟨ns, h1⟩ := h2b_lc_ok h
  simp [h2b_lc!, h2b!, h2b, h1]


theorem h2b_lc_eq_! : is_ok (h2b s) → h2b_lc s.data = Result.ok (h2b_lc! s.data) := by
  intro h
  obtain ⟨ns, h1⟩ := h2b_lc_ok h
  simp [h2b_lc!, h2b!, h2b, h1]


theorem h2b_ok_iff_h2b_lc_ok : is_ok (h2b s) ↔ is_ok (h2b_lc s.data) := by
  constructor
  intro h
  simp [(h2b_lc_eq_! h), is_ok]
  intro h
  simp [h2b]
  obtain ⟨ns, h1⟩ := h
  rw [h1]
  simp [is_ok]
