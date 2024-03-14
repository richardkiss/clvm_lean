import Clvm.Node
import Clvm.Ecdsa.Basic
import Clvm.Ecdsa.Bls12381
import Clvm.Ecdsa.Opcode

inductive NResult (α: Type) : Type
| ok : α → NResult α
| err : Node → String → NResult α
deriving Repr


def NResult.is_ok {α: Type} (r: NResult α) : Bool :=
  match r with
  | NResult.ok _ => True
  | NResult.err _ _ => False


def node_to_list_1 (args: Node) (cast: Node → NResult α): NResult (List α) :=
  match args with
  | Node.atom #[] => NResult.ok []
  | Node.pair first rest => match cast first with
    | NResult.err a b => NResult.err a b
    | NResult.ok v => match node_to_list_1 rest cast with
      | NResult.err a b => NResult.err a b
      | NResult.ok rest => NResult.ok (v :: rest)
  | _ => NResult.err args "unexpected terminator"



def node_to_list_int (args: Node) (cast: Node → NResult Int): NResult (List Int) :=
  match args with
  | Node.atom #[] => NResult.ok []
  | Node.pair first rest => match cast first with
    | NResult.err a b => NResult.err a b
    | NResult.ok v => match node_to_list_1 rest cast with
      | NResult.err a b => NResult.err a b
      | NResult.ok rest => NResult.ok (v :: rest)
  | _ => NResult.err args "unexpected terminator"


def node_to_node_list_terminator (args: Node) : (List Node) × Atom :=
  match args with
  | Node.atom a => ⟨[], a⟩
  | Node.pair first rest =>
    let ⟨ rest, terminator⟩ := node_to_node_list_terminator rest
    ⟨first :: rest, terminator⟩


def node_to_node_list (args: Node) : NResult (List Node) :=
  let r := node_to_node_list_terminator args
  match r with
  | (l, #[]) => NResult.ok l
  | _ => NResult.err args "unexpected terminator"


def list_nresult_to_nresult_list (args: List (NResult α)): NResult (List α) :=
  match args with
  | [] => NResult.ok []
  | (NResult.err obj msg) :: _ => NResult.err obj msg
  | (NResult.ok v) :: rest => match list_nresult_to_nresult_list rest with
    | NResult.err obj msg => NResult.err obj msg
    | NResult.ok rest => NResult.ok (v :: rest)


def node_to_list (args: Node) (cast: Node → NResult α): NResult (List α) :=
  let step1 : List Node × Atom := node_to_node_list_terminator args
  -- need to prove that right node is nil
  if step1.2.size > 0 then
    NResult.err args "unexpected terminator"
  else
    let step2 : List (NResult α) := step1.1.map cast
    -- need to prove that all casts "succeed"
    let step3 : NResult (List α) := list_nresult_to_nresult_list step2
    match step3 with
    | NResult.err a b => NResult.err a b
    | NResult.ok l => NResult.ok l



def only_atoms (node: Node) (cast : (Array UInt8) → α) : NResult α :=
  match node with
  | Node.atom atom => NResult.ok (cast atom)
  | _ => NResult.err node "expected atom"


def atom_to_int_cast (node: Node) : NResult Int := only_atoms node atom_to_int


def atom_to_nat_cast (node: Node) : NResult Nat := only_atoms node atom_to_nat


def node_to_bool (node: Node) : NResult Bool :=
  match node with
  | Node.atom atom => NResult.ok (atom.size != 0)
  | _ => NResult.ok true


def args_to_int (args: Node) : NResult (List Int) :=
  node_to_list args atom_to_int_cast


def args_to_nat (args: Node) : NResult (List Nat) :=
  node_to_list args atom_to_nat_cast


def args_to_bool (args: Node) : NResult (List Bool) :=
  node_to_list args node_to_bool


def node_to_bls_point (node: Node) : NResult (JacobianPoint CurveBLS12381) :=
  match node with
  | Node.atom a => match deserialize_point a with
    | none => NResult.err node "point_add on list"
    | some p => NResult.ok p
  | _ => NResult.err node "point_add expects blob, got xx"


def args_to_bls_points (args: Node) : NResult (List (JacobianPoint CurveBLS12381)) :=
  node_to_list args node_to_bls_point


def atom_only_cast (n: Node) : NResult (Array UInt8) :=
  match n with
  | Node.atom a => NResult.ok a
  | _ => NResult.err n "expected atom"


def nat_to_uint32 (n: Nat) : NResult UInt32 :=
  if (UInt32.ofNat n).toNat = n then NResult.ok (UInt32.ofNat n)
  else NResult.err (Node.atom #[]) "expected 4 bytes"



def node_to_u32 (n: Node) : NResult UInt32 :=
  match atom_only_cast n with
  | NResult.ok a => match nat_to_uint32 (atom_to_nat a) with
    | NResult.ok v => NResult.ok v
    | NResult.err a b => NResult.err a b
  | NResult.err a b => NResult.err a b


def atom_to_u32 (atom: Array UInt8) : NResult UInt32 :=
  match nat_to_uint32 (atom_to_nat atom) with
  | NResult.ok v => NResult.ok v
  | NResult.err a b => NResult.err a b


def atom_to_shift_int (op: String) (atom: Array UInt8) : NResult Int :=
  if atom.size > 4 then
    NResult.err (Node.atom atom) (op ++ " requires int32 args (with no leading zeros)")
  else
    let as_int := atom_to_int atom
    if as_int.natAbs > 65535 then
      NResult.err (Node.atom atom) "shift too large"
    else
      NResult.ok as_int


def node_as_int32 (op_name: String) (node: Node) : NResult Int :=
  match node with
  | Node.atom a =>
        if a.size > 4 then
          NResult.err node (op_name ++ " requires int32 args (with no leading zeros)")
        else
          NResult.ok (atom_to_int a)
  | _ => NResult.err node (op_name ++ " requires int32 args")
