import Clvm.Coe
import Clvm.Node
import Clvm.Hex
import Clvm.Result
import Clvm.Run
import Clvm.Serde
import Clvm.Util


def do_run (node : Node) : String :=
  match node with
  | Node.atom a => s!"that's an atom: {a.data}"
  | Node.pair a b => match apply_node 100000 a b with
    | Result.ok n => n2h n
    | Result.err n e => s!"FAIL: {e} {n2h n}"


def handle_hex (hex : String) : String :=
  do_run (h2n hex)


def main (args: List String) : IO UInt32 :=
  let r := match args[0]? with
  | some hex => handle_hex hex
  | none => "no hex"
  do
    let stdout ← IO.getStdout
    stdout.putStrLn s!"{r}"
    pure 0
