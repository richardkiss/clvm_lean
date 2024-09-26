import Clvm.Serde
import Clvm.String


def h2n_parsed_node (hex: String) : Except (String × String) ParsedNode :=
  do
    let bytes ← h2b_lc hex.data
    match bytes_to_parsed_node bytes with
    | Except.ok pn => return pn
    | Except.error ⟨ s, msg ⟩ => Except.err (toString s) msg


def h2n (hex: String) : Except (String × String) Node := do
  return (← (h2n_parsed_node hex)).node



def h2n_valid (hex: String) := ∃ (n: Node), h2n hex = Except.ok n -- ∧ n2h n = hex


def h2n_parsed_node! (hex: String) : ParsedNode :=
  match h2n_parsed_node hex with
  | Except.ok pn => pn
  | Except.error _ => ParsedNode.mk Node.nil [0x80]


def h2n! (hex: String) : Node := (h2n_parsed_node! hex).node


def h2n_first! (hex: String) : Node := (h2n_parsed_node! hex).node


def h2n_second (hex: String) : Except (String × String) Node :=
  do
    let pn ← h2n_parsed_node hex
    match bytes_to_parsed_node pn.bytes with
    | Except.ok pn2 => return pn2.node
    | Except.error ⟨ s, msg ⟩ => Except.err (toString s) msg


def h2n_second! (hex: String) : Node :=
  match h2n_second hex with
  | Except.ok node => node
  | Except.error _ => Node.nil


def h_first! (hex: String) : String := n2h (h2n! hex)

def h_rest! (hex: String) : String := n2h (h2n_second! hex)


lemma h2n_ok_parsed_node_ok (s: String): is_ok (h2n s) → is_ok (h2n_parsed_node s) := by
  intro h
  by_contra h_c
  obtain ⟨c, h1⟩ := not_ok h_c
  simp [h2n, h1, bind, Except.bind, is_ok] at h

/-!
a hex string that deserializes into a clvm object that starts with `ff` is a pair. This theorem
shows how to get the left and right side of the pair.
-/
theorem h2n_ff (s: String): is_ok (h2n s) → s = "ff" ++ s0 → h2n s = Except.ok (Node.pair (h2n_first! s0) (h2n_second! s0)) := by
  intro h0 h1

  obtain ⟨pn, h4⟩ := h2n_ok_parsed_node_ok s h0

  suffices : pn.node = (h2n_first! s0).pair (h2n_second! s0)
  · rw [← this]
    simp only [h2n, h4]
    rfl

  unfold h2n_parsed_node at h4
  unfold h2b_lc at h4
  simp only [h1, String.data_append, ↓Char.isValue, List.cons_append, List.singleton_append,
    bind_assoc] at h4
  simp only [hex_pair_to_byte, hex_nibble_to_byte, ↓Char.isValue, Char.reduceToLower,
    Char.reduceToNat, ge_iff_le, Nat.reduceLeDiff, decide_True, decide_False, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, le_refl, Bool.and_self, Nat.reduceSub, List.nil_append,
    bind_assoc] at h4
  simp only [bind, Except.bind, Nat.reduceMul, Nat.reduceAdd, pure, Except.pure] at h4
  unfold bytes_to_parsed_node at h4
  simp only [↓reduceIte] at h4

  have h_ok_1: is_ok (h2b_lc s0.data) := by
    by_contra h_c
    obtain ⟨c, h5⟩ := not_ok h_c
    simp only [h5] at h4

  obtain ⟨bytes, h5⟩ := h_ok_1
  rw [h5] at h4
  simp only [bind, Except.bind, pure, Except.pure] at h4

  have h_ok_2: is_ok (bytes_to_parsed_node bytes) := by
    by_contra h_c
    obtain ⟨c, h5⟩ := not_ok h_c
    simp only [h5, Except.err] at h4

  obtain ⟨pn1, h6⟩ := h_ok_2
  simp only [h6] at h4

  have h_ok_3: is_ok (bytes_to_parsed_node pn1.bytes) := by
    by_contra h_c
    obtain ⟨c, h5⟩ := not_ok h_c
    simp only [h5, Except.err] at h4

  obtain ⟨pn2, h7⟩ := h_ok_3
  simp only [h7, Except.ok.injEq] at h4

  rw [← h4]

  simp only [h2n_first!, h2n_parsed_node!, h2n_parsed_node, bind, Except.bind, h5, h6, pure,
    Except.pure, Node.pair.injEq, true_and]

  simp only [h2n_second!, h2n_second, h2n_parsed_node, bind_assoc, Node.nil]
  simp only [bind, Except.bind, h5, h6, pure, Except.pure, h7]


lemma h2n_first!_eq_h2n!: h2n_first! s = h2n! s := by rw [h2n_first!, h2n!]


/-!
A nicer version of `h2n_ff` that uses `h2n!`. This will go into a tactic that will strip off
a `ff` prefix from a hex string and yank out the parts of the string that matter.
-/
theorem h2n!_split (s: String): is_ok (h2n s) → s.take 2 = "ff" → h2n! s = Node.pair (h2n_first! (s.drop 2)) (h2n_second! (s.drop 2)) := by
  intro h0 h1
  have h: s = "ff" ++ s.drop 2 := by
    rw [← h1]
    apply string_take_drop s 2

  have h_q := h2n_ff s h0 h
  unfold h2n at h_q

  obtain ⟨pn, h2⟩ := h2n_ok_parsed_node_ok s h0
  unfold h2n! h2n_parsed_node!
  simp only [h2]
  simp only [bind, Except.bind, h2, pure, Except.pure, Except.ok.injEq] at h_q
  rw [h_q]


--#print h2n!_split


example: h2n! "ff01ff05ff09ff0a80" = Node.pair (Node.atom [1]) (Node.pair (Node.atom [5]) (Node.pair (Node.atom [9]) (Node.pair (Node.atom [10]) Node.nil))) := by
  have h_ok: is_ok (h2n "ff01ff05ff09ff0a80") := by
    simp [is_ok, h2n, Except.bind, bind, Except.pure, pure, h2n_parsed_node, h2b_lc, hex_pair_to_byte, hex_nibble_to_byte, bytes_to_parsed_node, bytes_to_atom, MAX_SINGLE_BYTE]

  have h_starts: "ff01ff05ff09ff0a80".take 2 = "ff" := by
    rfl

  simp only [h2n!_split "ff01ff05ff09ff0a80" h_ok h_starts, Node.nil, Node.pair.injEq]
  simp only [h2n_first!, h2n_parsed_node!, h2n_parsed_node, bind, Except.bind, h2b_lc,
    hex_pair_to_byte, hex_nibble_to_byte, ↓Char.isValue, Char.reduceToLower, Char.reduceToNat,
    ge_iff_le, le_refl, decide_True, Nat.reduceLeDiff, Bool.and_self, ↓reduceIte,
    tsub_eq_zero_of_le, Nat.reduceSub, zero_mul, zero_add, decide_False, Bool.and_false,
    Bool.false_eq_true, Nat.reduceMul, Nat.reduceAdd, add_zero, bytes_to_parsed_node,
    OfNat.one_ne_ofNat, bytes_to_atom, MAX_SINGLE_BYTE, Nat.one_le_ofNat, pure, Except.pure,
    true_and]

  simp only [h2n_second!, h2n_second, bind, Except.bind, h2n_parsed_node, h2b_lc, hex_pair_to_byte,
    hex_nibble_to_byte, ↓Char.isValue, Char.reduceToLower, Char.reduceToNat, ge_iff_le, le_refl,
    decide_True, Nat.reduceLeDiff, Bool.and_self, ↓reduceIte, tsub_eq_zero_of_le, Nat.reduceSub,
    zero_mul, zero_add, decide_False, Bool.and_false, Bool.false_eq_true, Nat.reduceMul,
    Nat.reduceAdd, add_zero, bytes_to_parsed_node, OfNat.one_ne_ofNat, bytes_to_atom,
    MAX_SINGLE_BYTE, Nat.one_le_ofNat, pure, Except.pure, Nat.reduceEqDiff, Node.nil]
