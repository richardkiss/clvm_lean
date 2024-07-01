import Clvm.Serde


def show_except (except: Except (String × Node) Node) : String :=
  match except with
  | Except.ok node => "ok: " ++ n2h node
  | Except.error ⟨ msg, node ⟩ => "err: " ++ msg ++ " " ++ n2h node


def h2n_partial (hex: String) : Except (String × String) ParsedNode :=
  match h2b_lc hex.data with
  | Except.ok bytes =>
    match bytes_to_parsed_node bytes with
    | Except.ok d => Except.ok d
    | Except.error msg => Except.err msg.2 hex
  | Except.error ⟨ s, msg ⟩  => Except.err (String.mk [s]) msg


def h2n (hex: String) : Except (String × String) Node :=
  match h2n_partial hex with
  | Except.ok p => Except.ok p.node
  | Except.error ⟨ s, msg ⟩ => Except.err s msg


def h2n! (hex: String) : Node :=
  match h2n hex with
  | Except.ok node => node
  | Except.error _ => Node.nil


def h2n_valid (hex: String) := ∃ (n: Node), h2n hex = Except.ok n ∧ n2h n = hex


def h2n_partial! (hex: String) : Node :=
  match h2n hex with
  | Except.ok node => node
  | Except.error _ => Node.nil


def h2n_skip! (hex: String) : String :=
  match h2n_partial hex with
  | Except.ok p => b2h p.bytes
  | Except.error _ => ""
