import Clvm.Hex
import Clvm.Node
import Clvm.Ecdsa.Basic
import Clvm.Ecdsa.Bls12381
import Clvm.Ecdsa.Opcode


def node_to_list_1 (args: Node) (cast: Node → Except (Node × String) α): Except (Node × String) (List α) :=
  match args with
  | Node.atom { data := [], lt := _ } => Except.ok []
  | Node.pair first rest => match cast first with
    | Except.error a => Except.error a
    | Except.ok v => match node_to_list_1 rest cast with
      | Except.error ⟨ a, b ⟩  => Except.error ⟨ a, b ⟩
      | Except.ok rest => Except.ok (v :: rest)
  | _ => Except.err args "unexpected terminator"


def node_to_list_int (args: Node) (cast: Node → Except (Node × String) Int): Except (Node × String) (List Int) := node_to_list_1 args cast


def list_except_to_except_list (args: List (Except (Node × String) α)): Except (Node × String) (List α) :=
  match args with
  | [] => Except.ok []
  | Except.error ⟨ obj, msg ⟩ :: _ => Except.err obj msg
  | (Except.ok v) :: rest => match list_except_to_except_list rest with
    | Except.error ⟨ obj, msg ⟩ => Except.err obj msg
    | Except.ok rest => Except.ok (v :: rest)


def node_to_list (args: Node) (cast: Node → Except (Node × String) α): Except (Node × String) (List α) :=
  match args with
  | Node.atom ⟨ [], _ ⟩  => Except.ok []
  | Node.atom _ => Except.err args "unexpected terminator"
  | Node.pair n1 n2 => do
      let tail ← node_to_list n2 cast
      let head ← cast n1
      return head :: tail


def only_atoms (node: Node) (cast : Atom → α) : Except (Node × String) α :=
  match node with
  | Node.atom atom => Except.ok (cast atom)
  | _ => Except.err node "expected atom"


def atom_to_int_cast (node: Node) : Except (Node × String) Int := only_atoms node atom_to_int


def node_to_bool (node: Node) : Except (Node × String) Bool :=
  match node with
  | Node.atom atom => Except.ok (atom.length != 0)
  | _ => Except.ok true


def args_to_int (args: Node) : Except (Node × String) (List Int) :=
  node_to_list args atom_to_int_cast


def args_to_bool (args: Node) : Except (Node × String) (List Bool) :=
  node_to_list args node_to_bool


def node_to_bls_point (node: Node) : Except (Node × String) (JacobianPoint CurveBLS12381) :=
  match node with
  | Node.atom a => match deserialize_point a with
    | none => Except.err node "point_add on list"
    | some p => Except.ok p
  | _ => Except.err node "point_add expects blob, got xx"


def args_to_bls_points (args: Node) : Except (Node × String) (List (JacobianPoint CurveBLS12381)) :=
  node_to_list args node_to_bls_point


def atom_only_cast (n: Node) : Except (Node × String) Atom :=
  match n with
  | Node.atom a => Except.ok a
  | _ => Except.err n "expected atom"


def nat_to_uint32 (n: Nat) : Except (Node × String) UInt32 :=
  if (UInt32.ofNat n).toNat = n then Except.ok (UInt32.ofNat n)
  else Except.err Node.nil "expected 4 bytes"


def node_to_u32 (n: Node) : Except (Node × String) UInt32 :=
  match atom_only_cast n with
  | Except.ok a => match nat_to_uint32 (atom_to_nat a) with
    | Except.ok v => Except.ok v
    | Except.error a => Except.error a
  | Except.error a => Except.error a


def atom_to_shift_int (op: String) (atom: Atom) : Except (Node × String) Int :=
  if atom.length > 4 then
    Except.err (Node.atom atom) (op ++ " requires int32 args (with no leading zeros)")
  else
    let as_int := atom_to_int atom
    if as_int.natAbs > 65535 then
      Except.err (Node.atom atom) "shift too large"
    else
      Except.ok as_int


def node_as_int32 (op_name: String) (node: Node) : Except (Node × String) Int :=
  match node with
  | Node.atom a =>
        if a.length > 4 then
          Except.err node (op_name ++ " requires int32 args (with no leading zeros)")
        else
          Except.ok (atom_to_int a)
  | _ => Except.err node (op_name ++ " requires int32 args")
