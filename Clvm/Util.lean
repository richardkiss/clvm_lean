import Clvm.Result
import Clvm.Serde


def show_result (result: Result Node Node) : String :=
  match result with
  | Result.ok node => "ok: " ++ n2h node
  | Result.err node msg => "err: " ++ msg ++ " " ++ n2h node


@[simp]
def h2n (hex: String) : Result Node String :=
  match h2b_list hex with
  | Result.ok bytes =>
    match bytes_to_node bytes with
    | Result.ok node => Result.ok node
    | Result.err _ msg => Result.err hex msg
  | Result.err s msg => Result.err s msg


@[simp]
def h2n! (hex: String) : Node :=
  match h2n hex with
  | Result.ok node => node
  | Result.err _ _ => Node.nil


@[simp]
def h2n_partial (hex: String) : Result DResult String :=
  match h2b_list hex with
  | Result.ok bytes =>
    match bytes_to_node_inner hex.length bytes with
    | Result.ok d => Result.ok d
    | Result.err _ msg => Result.err hex msg
  | Result.err s msg => Result.err s msg


def h2n_valid (hex: String) := ∃ (n: Node), h2n hex = Result.ok n ∧ n2h n = hex



instance : ToString Node where toString :=
  fun n => "Node<" ++ (n2h n) ++ ">"

instance : Repr Node where reprPrec n _ := "Node<" ++ (n2h n) ++ ">"
