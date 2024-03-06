import Clvm.Result
import Clvm.Serde


def show_result (result: Result Node) : String :=
  match result with
  | Result.ok node => "ok: " ++ n2h node
  | Result.err node msg => "err: " ++ msg ++ " " ++ n2h node



def h2n (hex: String) : Node :=
  bytes_to_node (h2b hex)


def rt (hex: String) : Bool :=
  n2h (h2n hex) = hex

instance : ToString Node where toString :=
  fun n => "Node<" ++ (n2h n) ++ ">"

instance : Repr Node where reprPrec n _ := "Node<" ++ (n2h n) ++ ">"
