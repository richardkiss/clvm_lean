import Clvm.Serde


def h2n_parsed_node (hex: String) : Except (String × String) ParsedNode :=
  do
    let bytes ← h2b_lc hex.data
    match bytes_to_parsed_node bytes with
    | Except.ok pn => return pn
    | Except.error ⟨ s, msg ⟩ => Except.err (toString s) msg


def h2n (hex: String) : Except (String × String) Node := do
  return (← (h2n_parsed_node hex)).node


def h2n! (hex: String) : Node :=
  match h2n hex with
  | Except.ok node => node
  | Except.error _ => Node.nil


def h2n_valid (hex: String) := ∃ (n: Node), h2n hex = Except.ok n -- ∧ n2h n = hex


def h2n_parsed_node! (hex: String) : ParsedNode :=
  match h2n_parsed_node hex with
  | Except.ok pn => pn
  | Except.error _ => ParsedNode.mk Node.nil [0x80]


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



theorem h2n_ff : hex = "ff" ++ s → is_ok (h2n hex) → h2n hex = Except.ok (Node.pair (h2n_first! s) (h2n_second! s)) := by
  intro h0 h1
  obtain ⟨n, h2⟩ := h1

  unfold h2n

  have h2n_ok: is_ok (h2n_parsed_node hex) := by
    by_contra h_c
    obtain ⟨c, h5⟩ := not_ok h_c
    unfold h2n at h2
    simp [bind, Except.bind, h5] at h2

  obtain ⟨pn, h4⟩ := h2n_ok

  simp [bind, Except.bind, h4, pure, Except.pure]

  unfold h2n_parsed_node at h4
  unfold h2b_lc at h4
  simp [h0] at h4
  simp [hex_pair_to_byte, hex_nibble_to_byte] at h4
  simp [bind, Except.bind, pure, Except.pure] at h4
  unfold bytes_to_parsed_node at h4
  simp at h4

  have h_ok_1: is_ok (h2b_lc s.data) := by
    by_contra h_c
    obtain ⟨c, h5⟩ := not_ok h_c
    simp [bind, Except.bind, h5] at h4

  obtain ⟨bytes, h5⟩ := h_ok_1
  rw [h5] at h4
  simp at h4
  simp [bind, Except.bind, pure, Except.pure] at h4

  have h_ok_2: is_ok (bytes_to_parsed_node bytes) := by
    by_contra h_c
    obtain ⟨c, h5⟩ := not_ok h_c
    simp [bind, Except.bind, h5, Except.err] at h4

  obtain ⟨pn1, h6⟩ := h_ok_2
  simp [h6] at h4

  have h_ok_3: is_ok (bytes_to_parsed_node pn1.bytes) := by
    by_contra h_c
    obtain ⟨c, h5⟩ := not_ok h_c
    simp [bind, Except.bind, h5, Except.err] at h4

  obtain ⟨pn2, h7⟩ := h_ok_3
  simp [h7] at h4

  rw [← h4]

  simp [h2n_first!, h2n_parsed_node!, h2n_parsed_node, h5, bind, Except.bind, h6, pure, Except.pure]

  simp [h2n_second!, h2n_second, h2n_parsed_node, h0, h2b_lc, hex_pair_to_byte, hex_nibble_to_byte]
  simp [bind, Except.bind, bytes_to_parsed_node, h5, h6, h7, pure, Except.pure]
