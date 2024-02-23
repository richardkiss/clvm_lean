import LeanClvm.Atom
import LeanClvm.Result


inductive Node
  | atom : Array UInt8 → Node
  | pair : Node → Node → Node
  deriving Repr

def Node.nil := Node.atom #[]
def Node.one := Node.atom #[1]

def node_at_wdepth (depth: Nat) (p: Nat) (node: Node): Result Node :=
  if depth = 0 then
    Result.err node "depth is 0"
  else if p < 2 then
    if p = 0 then
      Result.ok (Node.atom #[])
    else
      Result.ok node
  else
    match node with
    | Node.atom _ => Result.err node "path into atom"
    | Node.pair a b => node_at_wdepth (depth-1) (p / 2) (if p % 2 = 0 then a else b)


def node_at (p: Nat) (node: Node): Result Node := node_at_wdepth (p+1) p node


def sha256 (data: Array UInt8): Array UInt8 := data


def tree_hash (hash: Array UInt8 -> Array UInt8) (node: Node): Array UInt8 :=
  let rec tree_aux (node: Node): Array UInt8 :=
    match node with
    | Node.atom a => hash #[1] ++ a
    | Node.pair a b => hash #[2] ++ (tree_aux a) ++ (tree_aux b)
  tree_aux node


def sha256_tree := tree_hash sha256

#check sha256_tree
