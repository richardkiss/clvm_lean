import Clvm.Atom
import Clvm.Result
-- import Clvm.Sha256

import Init.Data.Nat.Div


inductive Node
  | atom : Atom → Node
  | pair : Node → Node → Node
  deriving Repr


def Node.nil := Node.atom (Atom.mk [] (by decide))
def Node.one := Node.atom [1]

def node_at_wdepth (depth: Nat) (p: Nat) (node: Node): Result Node Node :=
  if depth = 0 then
    Result.err node "depth is 0"
  else if p < 2 then
    if p = 0 then
      Result.ok (Node.nil)
    else
      Result.ok node
  else
    match node with
    | Node.atom _ => Result.err node "path into atom"
    | Node.pair a b => node_at_wdepth (depth-1) (p / 2) (if p % 2 = 0 then a else b)



def node_at (p: Nat) (node: Node): Result Node Node := node_at_wdepth (p+1) p node


/-
def tree_hash_node (hash: Atom -> Bytes32) (node: Node): Bytes32 :=
  let atom_prefix : Nat := 1
  let node_prefix : Nat := 2
  let rec tree_aux (node: Node): Bytes32 :=
    match node with
    | Node.atom a => hash (atom_prefix :: a)
    | Node.pair a b => hash (node_prefix :: (tree_aux a.data ++ tree_aux b.data))
  tree_aux node
-/

-- def tree_hash (node: Node) := tree_hash_node sha256 node

-- #check tree_hash

structure NodePath :=
  n : Nat
deriving Repr

def ZERO_PATH : NodePath := { n := 0 }
def TOP : NodePath := { n := 1 }

def first (path: NodePath) : NodePath :=
  { n := path.n * 2 }

def rest (path: NodePath) : NodePath :=
  { n := path.n * 2 + 1 }

instance : Coe Nat NodePath := ⟨λ n => { n := n }⟩

def highest_bit (n: Nat) : Nat :=
  let rec count_bits (n: Nat) (acc: Nat) : Nat :=
    if h: 0 < n then
      have _: n / 2 < n := by
        exact Nat.div_lt_self h (by decide)
      count_bits (n / 2) (acc + 1)
    else
      acc
  (1 <<< (count_bits n 0)) / 2

#eval highest_bit 16

def compose_paths (a: NodePath) (b: NodePath) : NodePath :=
if a.n = 0 ∨ b.n = 0 then
  { n := 0 }
else
  let hba := highest_bit a.n
  { n := b.n * hba + (a.n ^^^ hba)}


instance : OfNat NodePath n where
  ofNat := { n := n }


def path_from_string (s: String) : NodePath :=
  { n := s.toNat! }


structure Replacement :=
  path : NodePath
  replacement : Node
deriving Repr


def split_replacements (replacements: List Replacement) : (List Replacement) × (List Replacement) × Option Node :=
  let rec loop (r: List Replacement) (left: List Replacement) (right: List Replacement) : (List Replacement) × (List Replacement) × Option Node :=
    match r with
    | [] => (left, right, none)
    | r :: rs =>
      if r.path.n = 1 then
        ([], [], some r.replacement)
      else
        let new_path : NodePath := { n := r.path.n / 2 }
        let new_r : Replacement := { path := new_path, replacement := r.replacement }
        if r.path.n % 2 = 0 then
          loop rs (new_r :: left) right
        else
          loop rs left (new_r :: right)
  loop replacements [] []


def replace (node : Node) (replacements : List Replacement) : Node :=
  if replacements.isEmpty then
    node
  else
    let split : (List Replacement) × (List Replacement) × Option Node := split_replacements replacements
    match split.2.2 with
    | some n => n
    | none => match node with
      | Node.atom _ => node
      | Node.pair left right => Node.pair (replace left split.1) (replace right split.2.1)


def nodepath_for_char (c: Char) : NodePath :=
  if c = 'f' then
    { n := 2 }
  else if c = 'r' then
    { n := 3 }
  else
    { n := 0 }


def nodepath_for_string (s: String) : NodePath :=
  let np : List NodePath := s.data.map nodepath_for_char
  np.foldl compose_paths TOP


instance : CoeOut String NodePath where
  coe := nodepath_for_string

instance Node.instOfNat : OfNat Node n where
  ofNat := Node.atom (int_to_atom (Int.ofNat n))

instance : CoeOut Int Node where
  coe := Node.atom ∘ int_to_atom
