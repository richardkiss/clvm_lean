import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Use


def Except.err {α β : Type} (e: β) (s: String) : Except (β × String) α := Except.error ⟨ e, s ⟩


def is_ok {α β : Type} (e: Except α β) := ∃ a, e = Except.ok a


theorem not_ok {α β : Type} {e: Except α β} (h: ¬ is_ok e) : ∃ a, e = Except.error a := by
  induction e with
  | ok a => simp only [is_ok, Except.ok.injEq, exists_eq', not_true_eq_false] at h
  | error a => use a


def hex_nibble_to_byte (c: Char) : Except (String × String) Nat :=
  let c := c.toLower
  if c.toNat >= 48 && c.toNat <= 57 then
    Except.ok (c.toNat - 48)
  else if c.toNat >= 97 && c.toNat <= 102 then
    Except.ok (c.toNat - 87)
  else
    Except.err (String.mk [c]) "invalid hex digit"


def hex_pair_to_byte (c1 c2: Char) : Except (String × String) Nat := do
  let n1 ← hex_nibble_to_byte c1
  let n2 ← hex_nibble_to_byte c2
  Except.ok (n1 * 16 + n2)


def hex_pair_to_byte! (c1 c2: Char) : Nat :=
  match hex_pair_to_byte c1 c2 with
  | Except.ok n => n
  | Except.error _ => 0


def h2b_lc (s: List Char) : Except (String × String) (List Nat) :=
  match s with
  | c1 :: c2 :: rest => do
    let b ← hex_pair_to_byte c1 c2
    let r ← h2b_lc rest
    Except.ok (b :: r)
  | [c] => Except.err (String.mk [c]) "odd number of hex digits"
  | [] => Except.ok []


def h2b_lc! (s: List Char) : List Nat :=
  match h2b_lc s with
  | Except.ok r => r
  | Except.error _ => []


@[simp]
def h2b (s: String) := h2b_lc s.data


def h2b! (s: String) : List Nat :=
  match h2b s with
  | Except.ok r => r
  | Except.error _ => []


def nat_to_hex (n : Nat) : String :=
  let hex_chars := "0123456789abcdef".toList
  let hex_digit (n : Nat) : Char :=
    if n < 16 then hex_chars.get! n else 'X'
  String.mk ([hex_digit (n / 16), hex_digit (n % 16)])


def b2h (bytes : List Nat) : String :=
  String.join (bytes.map (λ b => nat_to_hex b))


def List.hex (bytes: List Nat) : String :=
  b2h bytes


theorem h2b_lc_remove_two_chars_helper: is_ok (h2b_lc ([c0, c1] ++ s)) →
    is_ok (hex_pair_to_byte c0 c1) ∧ is_ok (h2b_lc s) := by
  intro h
  obtain ⟨ns, h0⟩ := h
  dsimp [h2b_lc] at h0
  have p0: is_ok (hex_pair_to_byte c0 c1) := by
    by_contra h1
    obtain ⟨c, h2⟩ := not_ok h1
    simp only [bind, Except.bind, h2] at h0

  simp only [p0, true_and]
  obtain ⟨n0, hn0⟩ := p0
  rw [hn0] at h0
  have p1: is_ok (h2b_lc s) := by
    by_contra h1
    obtain ⟨c, h2⟩ := not_ok h1
    simp only [bind, Except.bind, h2] at h0
  exact p1



theorem h2b_lc_remove_two_chars: is_ok (h2b_lc ([c0, c1] ++ s)) → h2b_lc ([c0, c1] ++ s) = Except.ok (h2b_lc! ([c0, c1]) ++ h2b_lc! s) := by
  intro h0
  obtain ⟨ p0, p1 ⟩ := h2b_lc_remove_two_chars_helper h0
  obtain ⟨ns0, hn0⟩ := p0
  obtain ⟨ns1, hn1⟩ := p1
  simp [h2b_lc, h2b_lc!, hn0, hn1, h2b_lc, bind, Except.bind]


theorem take_drop (s : List α) (n: Nat): s = (s.take n) ++ (s.drop n) := by simp [List.take, List.drop]


theorem prefix_len_2 (s: List α) : s.length ≥ 2 → ∃ c0 c1 r, s = [c0, c1] ++ r := by
  intro h_len
  cases s with
  | nil => simp [List.length_nil, ge_iff_le, Nat.le_zero_eq, Nat.add_one_ne_zero] at h_len
  | cons c0 s0 =>
    cases s0 with
    | nil => simp [List.length_singleton, ge_iff_le, Nat.reduceLeDiff] at h_len
    | cons c1 s1 => simp [List.length, ge_iff_le, Nat.le_add_left] at *


theorem h2b_lc_take_drop: is_ok (h2b_lc s) → s.length ≥ 2 → h2b_lc s = Except.ok (h2b_lc! (s.take 2) ++ h2b_lc! (s.drop 2)) := by
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
  obtain ⟨c, h2⟩ := not_ok h1
  simp [h2, is_ok] at h


theorem h2b_eq_lc : is_ok (h2b s) → h2b! s = h2b_lc! s.data := by
  intro h
  obtain ⟨ns, h1⟩ := h2b_lc_ok h
  simp [h2b_lc!, h2b!, h2b, h1]


theorem h2b_eq_! : is_ok (h2b s) → h2b s = Except.ok (h2b! s) := by
  intro h
  obtain ⟨ns, h1⟩ := h2b_lc_ok h
  simp [h2b_lc!, h2b!, h2b, h1]


theorem h2b_lc_eq_! : is_ok (h2b s) → h2b_lc s.data = Except.ok (h2b_lc! s.data) := by
  intro h
  obtain ⟨ns, h1⟩ := h2b_lc_ok h
  simp [h2b_lc!, h2b!, h2b, h1]


theorem h2b_ok_iff_h2b_lc_ok : is_ok (h2b s) ↔ is_ok (h2b_lc s.data) := by
  constructor
  · intro h
    simp [is_ok, (h2b_lc_eq_! h), Except.ok.injEq, exists_eq']
  · intro h
    simp [h2b]
    obtain ⟨ns, h1⟩ := h
    rw [h1]
    simp [is_ok]
