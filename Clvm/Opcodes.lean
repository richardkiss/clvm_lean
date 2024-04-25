import Clvm.Atom
import Clvm.Casts
--import Clvm.Ecdsa.Basic
--import Clvm.Ecdsa.Bls12381
--import Clvm.Ecdsa.Jacobian
import Clvm.Serde
import Clvm.Sha256
import Clvm.Result
import Clvm.Util

def extend (a : Array UInt8) (size : Nat) : Array UInt8 :=
  let v : UInt8 := match a[0]? with
    | none => 0
    | some x => if x >= 128 then 255 else 0
  (Array.mkArray (size - a.size) v) ++ a


def equalize (a0 b0 : Array UInt8) : (Array UInt8 × Array UInt8) :=
  if a0.size < b0.size then
    (extend a0 b0.size, b0)
  else if a0.size > b0.size then
    (a0, extend b0 a0.size)
  else
    (a0, b0)


def minimize (depth : Nat) (a : Array UInt8) : Array UInt8 :=
  if depth = 0 then
    a
  else
    let first : Option UInt8 := a[0]?
    match first with
    | none => a
    | some 0 => match a[1]? with
      | none => a
      | some x => if x &&& 0x80 = 0 then
        minimize (depth - 1) (a.extract 1 a.size)
      else
        a
    | some 0xff => match a[1]? with
      | none => a
      | some x => if x &&& 0x80 = 0x80 then
        minimize (depth - 1) (a.extract 1 a.size)
      else
        a
    | _ => a


def logical_op (a : Array UInt8) (b : Int) (f : Nat → Nat → Nat) : Array UInt8 :=
  let b0 := int_to_atom b
  let (a, b) := equalize a b0
  let r := a.zip b
  let r := r.map (fun (a, b) => (f a.toNat b.toNat).toUInt8)
  minimize r.size r


def land (a : Array UInt8) (b : Int): Array UInt8 := logical_op a b (fun a b => a.land b)
def lor (a : Array UInt8) (b : Int): Array UInt8 := logical_op a b (fun a b => a.lor b)
def lxor (a : Array UInt8) (b : Int): Array UInt8 := logical_op a b (fun a b => a.xor b)



def handle_op_c (args: Node) : Result Node Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom ⟨[], _⟩)) => Result.ok (Node.pair a0 a1)
  | _ => Result.err args "c takes exactly 2 arguments"


def handle_op_f (args: Node) : Result Node Node :=
  match args with
  | Node.pair a0 (Node.atom ⟨[], _⟩) =>
      match a0 with
      | Node.pair a0 _ => Result.ok a0
      | _ => Result.err a0 "first of non-cons"
  | _ => Result.err args "f takes exactly 1 argument"


def handle_op_r (args: Node) : Result Node Node :=
  match args with
  | Node.pair a0 (Node.atom ⟨[], _⟩) =>
      match a0 with
      | Node.pair _ a0 => Result.ok a0
      | _ => Result.err a0 "rest of non-cons"
  | _ => Result.err args "r takes exactly 1 argument"



def handle_op_i (args: Node) : Result Node Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.pair a2 (Node.atom ⟨[], _⟩))) =>
      match a0 with
      | Node.atom ⟨[], _⟩  => Result.ok a2
      | _ => Result.ok a1
  | _ => Result.err args "i takes exactly 3 arguments"


def handle_op_l (args: Node) : Result Node Node :=
  match args with
  | Node.pair a0 (Node.atom ⟨[], _⟩) =>
      match a0 with
      | Node.atom _ => Result.ok Node.nil
      | Node.pair _ _ => Result.ok Node.one
  | _ => Result.err args "l takes exactly 1 argument"


def handle_op_x (args: Node) : Result Node Node :=
  Result.err (
    match args with
    | Node.pair (Node.atom msg) (Node.atom ⟨[], _⟩) => (Node.atom msg)
    | _ => args
  ) "clvm raise"


def handle_op_eq (args: Node) : Result Node Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom ⟨[], _⟩)) =>
    match a0, a1 with
    |  Node.atom v0, Node.atom v1 =>
        if v0.data = v1.data then
          Result.ok Node.one
        else
          Result.ok Node.nil
    | Node.pair _ _, _ => Result.err a0 "= on list"
    | Node.atom _, Node.pair _ _ => Result.err a1 "= on list"
  | _ => Result.err args "= takes exactly 2 arguments"


def compare_gr_s (depth: Nat) (v0: Array UInt8) (v1: Array UInt8) : Bool :=
  if depth = 0 then
    False
  else
    match v0[0]?, v1[0]? with
    | none, none => False
    | none, some _ => False
    | some _, none => True
    | some n0, some n1 =>
      if n0 > n1 then
        True
      else if n0 < n1 then
        False
      else compare_gr_s (depth - 1) (v0.extract 1 v0.size) (v1.extract 1 v1.size)


def handle_op_gt_s (args: Node) : Result Node Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom ⟨[], _⟩)) =>
    match a0, a1 with
    |  Node.atom v0, Node.atom v1 =>
        let depth: Nat := max v0.length v1.length
        Result.ok (if (compare_gr_s depth v0 v1) then Node.one else Node.nil)
    | Node.pair _ _, _ => Result.err a0 ">s on list"
    | _, _ => Result.err a1 ">s on list"
  | _ => Result.err args ">s takes exactly 2 arguments"


def handle_op_sha256 (args: Node) : Result Node Node :=
  match node_to_list args atom_only_cast with
  | Result.err a _ => Result.err a "sha256 on list"
  | Result.ok atoms =>
    let msg : List Nat := atoms.foldl (fun a b => a ++ b) []
    Result.ok (Node.atom (sha256 msg))


def handle_op_substr (args: Node) : Result Node Node :=
  let three_args : Result (Node × Node × Option Node) Node :=
  match args with
  | Node.pair a0 (Node.pair a1 a2) =>
    match a2 with
    | Node.atom ⟨ [], _⟩  => Result.ok (a0, a1, none)
    | Node.pair a2 (Node.atom ⟨ [], _⟩) => Result.ok (a0, a1, some a2)
    | _ => Result.err args "substr takes exactly 2 or 3 arguments"
  | _ => Result.err args "substr takes exactly 2 or 3 arguments"

  let three_args : Result ((Array UInt8) × Int × Int) Node :=
    match three_args with
    | Result.err a b => Result.err a b
    | Result.ok (string_node, start_node, maybe_end) =>
      match string_node with
      | Node.pair _ _ => Result.err string_node "substr on list"
      | Node.atom s0 =>
        match node_as_int32 "substr" start_node with
        | Result.err a b => Result.err a b
        | Result.ok i1 =>
          match maybe_end with
            | none => Result.ok (s0, i1, s0.length)
            | some x => match node_as_int32 "substr" x with
              | Result.err a b => Result.err a b
              | Result.ok i2 => Result.ok (s0, i1, i2)
  match three_args with
  | Result.err a b => Result.err a b
  | Result.ok (s0, i1, i2) =>
      if i2 > s0.size ∨ i2 < i1 ∨ i2 < 0 ∨ i1 < 0 then
        Result.err args "invalid indices for substr"
      else
        Result.ok (Node.atom (s0.extract i1.toNat i2.toNat))


def handle_op_strlen (args: Node) : Result Node Node :=
  match args with
  | Node.pair a0 (Node.atom ⟨ [], _⟩) =>
    match a0 with
    | Node.atom msg => Result.ok (Node.atom (int_to_atom msg.length))
    | _ => Result.err a0 "strlen on list"
  | _ => Result.err args "strlen takes exactly 1 argument"


def handle_op_concat (args: Node) : Result Node Node :=
  match node_to_list args atom_only_cast with
  | Result.err a _ => Result.err a "concat on list"
  | Result.ok args =>
      let total : Array UInt8 := args.foldl (fun a b => a ++ b) #[]
      Result.ok (Node.atom total)


def handle_op_add (args: Node) : Result Node Node :=
  match args_to_int args with
  | Result.err _ b => Result.err args b
  | Result.ok args =>
    let total : Int := args.foldl (fun a b => a + b) 0
    Result.ok (Node.atom (int_to_atom total))


def handle_op_sub (args: Node) : Result Node Node :=
  match args_to_int args with
  | Result.err _ b => Result.err args b
  | Result.ok args =>
    match args with
    | first :: rest =>
      let total : Int := rest.foldl (fun a b => a - b) first
      Result.ok (Node.atom (int_to_atom total))
    | _ => Result.ok Node.nil


def handle_op_mul (args: Node) : Result Node Node :=
  match args_to_int args with
  | Result.err _ b => Result.err args b
  | Result.ok args =>
    let total : Int := args.foldl (fun a b => a * b) 1
    Result.ok (Node.atom (int_to_atom total))


def handle_op_div (args: Node) : Result Node Node :=
  match args with
  | Node.pair n0 (Node.pair n1 (Node.atom ⟨ [], _⟩)) =>
    match n0, n1 with
    | Node.atom a0, Node.atom a1 =>
      let v0 := atom_to_int a0
      let v1 := atom_to_int a1
      if v1 < 0 ∨ v0 < 0 then
        Result.err args "div operator with negative operands is deprecated"
      else if v1 == 0 then
        Result.err n0 "div with 0"
      else
        Result.ok (Node.atom (int_to_atom (v0 / v1)))
    | _, _ => Result.err args "div requires int args"
  | _ => Result.err args "div takes exactly 2 arguments"


def divmod (a: Int) (b: Int) : (Int × Int) :=
  let a_neg := a < 0
  let b_neg := b < 0
  let a := a.natAbs
  let b := b.natAbs
  let q := a / b
  let r := a % b
  let (q, r) := (
    if a_neg ≠ b_neg ∧ r != 0 then
        (q + 1, b - r)
    else
      (q, r)
  )
  (if a_neg = b_neg then q else -q, if b_neg then -r else r)


def handle_op_divmod (args: Node) : Result Node Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom ⟨ [], _⟩)) =>
    match a0, a1 with
    | Node.atom v0, Node.atom v1 =>
      let v0 := atom_to_int v0
      let v1 := atom_to_int v1
      if v1 == 0 then
        Result.err a0 "divmod with 0"
      else
        let dm := divmod v0 v1
        Result.ok (Node.pair (Node.atom (int_to_atom dm.1)) (Node.atom (int_to_atom dm.2)))
    | Node.pair _ _, _ => Result.err a0 "divmod requires int args"
    | _, _ => Result.err a1 "divmod requires int args"
  | _ => Result.err args "divmod takes exactly 2 arguments"


def handle_op_gt (args: Node) : Result Node Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom ⟨ [], _⟩)) =>
    match a0, a1 with
    |  Node.atom v0, Node.atom v1 =>
        let v0 := atom_to_int v0
        let v1 := atom_to_int v1
        Result.ok (if v0 > v1 then Node.one else Node.nil)
    | Node.pair _ _, _ => Result.err a0 "> requires int args"
    | _, _ => Result.err a1 "> requires int args"
  | _ => Result.err args "> takes exactly 2 arguments"


def shiftNat (v0: Nat) (v1: Int) : Nat :=
  if v1 < 0 then
    let v1 : Nat := v1.natAbs
    v0 >>> v1
  else
    v0 <<< v1.toNat

def shiftInt (v0: Int) (v1: Int) : Int :=
  let is_negative : Bool := if v0 < 0 then true else false
  let shifted := shiftNat v0.natAbs v1
  if is_negative then
    -shifted
  else
    shifted

def handle_op_ash (args: Node) : Result Node Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom ⟨ [], _⟩)) =>
    match a0, a1 with
    | Node.atom v0, Node.atom v1 =>
      let v0 := atom_to_int v0
      let v1 := atom_to_shift_int "ash" v1
      match v1 with
      | Result.err a b => Result.err a b
      | Result.ok v1 => Result.ok (Node.atom (int_to_atom (shiftInt v0 v1)))
    | Node.pair _ _, Node.atom _ => Result.err a0 "ash requires int args"
    | _, Node.pair _ _ => Result.err a1 "ash requires int args"
  | _ => Result.err args "ash takes exactly 2 arguments"

def handle_op_lsh (args: Node) : Result Node Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom ⟨ [], _⟩)) =>
    match a0, a1 with
    | Node.atom v0, Node.atom v1 =>
      let v0 := atom_to_nat v0
      let v1 := atom_to_shift_int "lsh" v1
      match v1 with
      | Result.err a b => Result.err a b
      | Result.ok v1 => Result.ok (Node.atom (int_to_atom (shiftNat v0 v1)))
    | Node.pair _ _, _ => Result.err a0 "lsh requires int args"
    | _, _ => Result.err a1 "lsh requires int args"
  | _ => Result.err args "lsh takes exactly 2 arguments"

def handle_op_logand (args: Node) : Result Node Node :=
  match args_to_int args with
  | Result.err _ b => Result.err args b
  | Result.ok args =>
      Result.ok (Node.atom (args.foldl (fun a b => land a b) #[255]))


def handle_op_logior (args: Node) : Result Node Node :=
  match args_to_int args with
  | Result.err _ b => Result.err args b
  | Result.ok args =>
      Result.ok (Node.atom (args.foldl (fun a b => lor a b) ([]: List Nat)))


def handle_op_logxor (args: Node) : Result Node Node :=
  match args_to_int args with
  | Result.err _ b => Result.err args b
  | Result.ok args =>
      Result.ok (Node.atom (args.foldl (fun a b => lxor a b) ([]: List Nat)))


def handle_op_lognot (args: Node) : Result Node Node :=
  match args with
  | Node.pair a0 (Node.atom ⟨ [], _⟩) =>
    match a0 with
    | Node.atom v0 =>
      if v0.length = 0 then
        Result.ok (Node.atom #[255])
      else
        let v1 : Array UInt8 := lxor v0 (-1)
        Result.ok (Node.atom (int_to_atom (atom_to_int v1)))
      | _ => Result.err a0 "lognot requires int args"
  | _ => Result.err args "lognot takes exactly 1 argument"


def handle_op_point_add (args: Node) : Result Node Node :=
  match args_to_bls_points args with
  | Result.err _ b => Result.err args b
  | Result.ok points =>
    let initial : JacobianPoint CurveBLS12381 := zero
    let total : JacobianPoint CurveBLS12381 := points.foldl add_jacobian initial
    Result.ok (Node.atom (serialize_point total))


def handle_op_pubkey_for_exp (args: Node) : Result Node Node :=
  let order := 0x73EDA753299D7D483339D80809A1D80553BDA402FFFE5BFEFFFFFFFF00000001
  if let Node.pair arg (Node.atom ⟨ [], _⟩) := args then
    if let Node.atom a0 := arg then
      let i0 := atom_to_int a0
      let i1 : Int := i0 % order
      let i2 : Nat := (if i1 < 0 then i1 + order else i1).toNat
      let pt : JacobianPoint CurveBLS12381 := i2 * generator_bls12381_g1
      Result.ok (Node.atom (serialize_point pt))
    else
      Result.err args "pubkey_for_exp requires int args"
  else
    Result.err args "pubkey_for_exp takes exactly 1 argument"


def handle_op_not (args: Node) : Result Node Node :=
  match args with
  | Node.pair a0 (Node.atom ⟨ [], _⟩) =>
    match a0 with
    | Node.atom ⟨ [], _⟩ => Result.ok Node.one
    | _ => Result.ok Node.nil
  | _ => Result.err args "not takes exactly 1 argument"

-- this take vararg arguments and returns true iff any argument is true
def handle_op_any (args: Node) : Result Node Node :=
  let v := args_to_bool args
  match v with
  | Result.err _ b => Result.err args b
  | Result.ok v =>
    let r := v.foldl (fun a b => a || b) false
    Result.ok (if r then Node.one else Node.nil)


-- this take vararg arguments and returns true iff all arguments are true
def handle_op_all (args: Node) : Result Node Node :=
  let v := args_to_bool args
  match v with
  | Result.err _ b => Result.err args b
  | Result.ok v =>
    let r := v.foldl (fun a b => a && b) true
    Result.ok (if r then Node.one else Node.nil)
