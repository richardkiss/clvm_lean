import Clvm.Node
import Clvm.Ecdsa.Basic
import Clvm.Ecdsa.Bls12381
import Clvm.Ecdsa.Opcode



def node_to_list_1 (args: Node) (cast: Node → Result α Node): Result (List α) Node :=
  match args with
  | Node.atom #[] => Result.ok []
  | Node.pair first rest => match cast first with
    | Result.err a b => Result.err a b
    | Result.ok v => match node_to_list_1 rest cast with
      | Result.err a b => Result.err a b
      | Result.ok rest => Result.ok (v :: rest)
  | _ => Result.err args "unexpected terminator"



def node_to_list_int (args: Node) (cast: Node → Result Int Node): Result (List Int) Node :=
  match args with
  | Node.atom #[] => Result.ok []
  | Node.pair first rest => match cast first with
    | Result.err a b => Result.err a b
    | Result.ok v => match node_to_list_1 rest cast with
      | Result.err a b => Result.err a b
      | Result.ok rest => Result.ok (v :: rest)
  | _ => Result.err args "unexpected terminator"


def node_to_node_list_terminator (args: Node) : (List Node) × Atom :=
  match args with
  | Node.atom a => ⟨[], a⟩
  | Node.pair first rest =>
    let ⟨ rest, terminator⟩ := node_to_node_list_terminator rest
    ⟨first :: rest, terminator⟩


def node_to_node_list (args: Node) : Result (List Node) Node :=
  let r := node_to_node_list_terminator args
  match r with
  | (l, #[]) => Result.ok l
  | _ => Result.err args "unexpected terminator"


def list_result_to_result_list (args: List (Result α Node)): Result (List α) Node :=
  match args with
  | [] => Result.ok []
  | (Result.err obj msg) :: _ => Result.err obj msg
  | (Result.ok v) :: rest => match list_result_to_result_list rest with
    | Result.err obj msg => Result.err obj msg
    | Result.ok rest => Result.ok (v :: rest)


def node_to_list (args: Node) (cast: Node → Result α Node): Result (List α) Node:=
  let step1 : List Node × Atom := node_to_node_list_terminator args
  -- need to prove that right node is nil
  if step1.2.size > 0 then
    Result.err args "unexpected terminator"
  else
    let step2 : List (Result α Node) := step1.1.map cast
    -- need to prove that all casts "succeed"
    let step3 : Result (List α) Node := list_result_to_result_list step2
    match step3 with
    | Result.err a b => Result.err a b
    | Result.ok l => Result.ok l



def only_atoms (node: Node) (cast : Atom → α) : Result α Node :=
  match node with
  | Node.atom atom => Result.ok (cast atom)
  | _ => Result.err node "expected atom"


def atom_to_int_cast (node: Node) : Result Int Node := only_atoms node atom_to_int


def atom_to_nat_cast (node: Node) : Result Nat Node := only_atoms node atom_to_nat


def node_to_bool (node: Node) : Result Bool Node :=
  match node with
  | Node.atom atom => Result.ok (atom.size != 0)
  | _ => Result.ok true


def args_to_int (args: Node) : Result (List Int) Node :=
  node_to_list args atom_to_int_cast


def args_to_nat (args: Node) : Result (List Nat) Node :=
  node_to_list args atom_to_nat_cast


def args_to_bool (args: Node) : Result (List Bool) Node :=
  node_to_list args node_to_bool


def node_to_bls_point (node: Node) : Result (JacobianPoint CurveBLS12381) Node :=
  match node with
  | Node.atom a => match deserialize_point a with
    | none => Result.err node "point_add on list"
    | some p => Result.ok p
  | _ => Result.err node "point_add expects blob, got xx"


def args_to_bls_points (args: Node) : Result (List (JacobianPoint CurveBLS12381)) Node :=
  node_to_list args node_to_bls_point


def atom_only_cast (n: Node) : Result (Array UInt8) Node :=
  match n with
  | Node.atom a => Result.ok a
  | _ => Result.err n "expected atom"


def nat_to_uint32 (n: Nat) : Result UInt32 Node :=
  if (UInt32.ofNat n).toNat = n then Result.ok (UInt32.ofNat n)
  else Result.err Node.nil "expected 4 bytes"



def node_to_u32 (n: Node) : Result UInt32 Node :=
  match atom_only_cast n with
  | Result.ok a => match nat_to_uint32 (atom_to_nat a) with
    | Result.ok v => Result.ok v
    | Result.err a b => Result.err a b
  | Result.err a b => Result.err a b


def atom_to_u32 (atom: Array UInt8) : Result UInt32 Node :=
  match nat_to_uint32 (atom_to_nat atom) with
  | Result.ok v => Result.ok v
  | Result.err a b => Result.err a b


def atom_to_shift_int (op: String) (atom: Array UInt8) : Result Int Node :=
  if atom.size > 4 then
    Result.err (Node.atom atom) (op ++ " requires int32 args (with no leading zeros)")
  else
    let as_int := atom_to_int atom
    if as_int.natAbs > 65535 then
      Result.err (Node.atom atom) "shift too large"
    else
      Result.ok as_int


def node_as_int32 (op_name: String) (node: Node) : Result Int Node :=
  match node with
  | Node.atom a =>
        if a.size > 4 then
          Result.err node (op_name ++ " requires int32 args (with no leading zeros)")
        else
          Result.ok (atom_to_int a)
  | _ => Result.err node (op_name ++ " requires int32 args")
