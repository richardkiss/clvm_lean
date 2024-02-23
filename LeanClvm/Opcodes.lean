import LeanClvm.Atom
import LeanClvm.Serde
import LeanClvm.Result
import LeanClvm.Util


def handle_op_c (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom #[])) => Result.ok (Node.pair a0 a1)
  | _ => Result.err args "c takes exactly 2 arguments"


def handle_op_f (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.atom #[]) =>
      node_at 2 a0
  | _ => Result.err args "f takes exactly 1 argument"


def handle_op_r (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.atom #[]) =>
      node_at 3 a0
  | _ => Result.err args "r takes exactly 1 argument"


def handle_op_i (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.pair a2 (Node.atom #[]))) =>
      match a0 with
      | Node.atom #[] => Result.ok a2
      | _ => Result.ok a1
  | _ => Result.err args "i takes exactly 3 arguments"


def handle_op_l (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.atom #[]) =>
      match a0 with
      | Node.atom _ => Result.ok (Node.atom #[])
      | Node.pair _ _ => Result.ok (Node.atom #[1])
  | _ => Result.err args "l takes exactly 1 argument"


def handle_op_x (args: Node) : Result Node :=
  Result.err (
    match args with
    | Node.pair (Node.atom msg) (Node.atom #[]) => (Node.atom msg)
    | _ => args
  ) "clvm raise"


def handle_op_eq (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom #[])) =>
    match a0, a1 with
    |  Node.atom v0, Node.atom v1 =>
        if v0 == v1 then
          Result.ok (Node.atom #[1])
        else
          Result.ok (Node.atom #[])
    | _, _ => Result.err args "Arguments to = must be atoms"
  | _ => Result.err args "eq takes exactly 2 arguments"


def handle_op_gt_s (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom #[])) =>
    match a0, a1 with
    |  Node.atom v0, Node.atom v1 =>
        if atom_to_int v0 > atom_to_int v1 then
          Result.ok (Node.atom #[1])
        else
          Result.ok (Node.atom #[])
    | _, _ => Result.err args "Arguments to > must be atoms"
  | _ => Result.err args "gt_s takes exactly 2 arguments"


def handle_op_sha256 (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.atom #[]) =>
    match a0 with
    | Node.atom msg => Result.ok (Node.atom (sha256 msg))
    | _ => Result.err args "sha256 takes exactly 1 argument"
  | _ => Result.err args "sha256 takes exactly 1 argument"

def handle_op_substr (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.pair a2 (Node.atom #[]))) =>
    match a0, a1, a2 with
    | Node.atom msg, Node.atom start, Node.atom length =>
      let start := atom_to_nat start
      let length := atom_to_nat length
      if start + length > msg.size then
        Result.err args "substring out of bounds"
      else
        Result.ok (Node.atom (msg.extract start (start + length)))
    | _, _, _ => Result.err args "Arguments to substr must be atoms"
  | _ => Result.err args "substr takes exactly 3 arguments"

def handle_op_strlen (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.atom #[]) =>
    match a0 with
    | Node.atom msg => Result.ok (Node.atom (nat_to_atom msg.size))
    | _ => Result.err args "strlen takes exactly 1 argument"
  | _ => Result.err args "strlen takes exactly 1 argument"

def handle_op_concat (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom #[])) =>
    match a0, a1 with
    | Node.atom msg0, Node.atom msg1 => Result.ok (Node.atom (msg0 ++ msg1))
    | _, _ => Result.err args "Arguments to concat must be atoms"
  | _ => Result.err args "concat takes exactly 2 arguments"

def handle_op_add (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom #[])) =>
    match a0, a1 with
    | Node.atom v0, Node.atom v1 =>
      let v0 := atom_to_int v0
      let v1 := atom_to_int v1
      Result.ok (Node.atom (int_to_atom (v0 + v1)))
    | _, _ => Result.err args "Arguments to add must be atoms"
  | _ => Result.err args "add takes exactly 2 arguments"

def handle_op_sub (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom #[])) =>
    match a0, a1 with
    | Node.atom v0, Node.atom v1 =>
      let v0 := atom_to_int v0
      let v1 := atom_to_int v1
      Result.ok (Node.atom (int_to_atom (v0 - v1)))
    | _, _ => Result.err args "Arguments to sub must be atoms"
  | _ => Result.err args "sub takes exactly 2 arguments"

def handle_op_mul (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom #[])) =>
    match a0, a1 with
    | Node.atom v0, Node.atom v1 =>
      let v0 := atom_to_int v0
      let v1 := atom_to_int v1
      Result.ok (Node.atom (int_to_atom (v0 * v1)))
    | _, _ => Result.err args "Arguments to mul must be atoms"
  | _ => Result.err args "mul takes exactly 2 arguments"

def handle_op_div (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom #[])) =>
    match a0, a1 with
    | Node.atom v0, Node.atom v1 =>
      let v0 := atom_to_int v0
      let v1 := atom_to_int v1
      if v1 == 0 then
        Result.err args "division by zero"
      else
        Result.ok (Node.atom (int_to_atom (v0 / v1)))
    | _, _ => Result.err args "Arguments to div must be atoms"
  | _ => Result.err args "div takes exactly 2 arguments"

def handle_op_divmod (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom #[])) =>
    match a0, a1 with
    | Node.atom v0, Node.atom v1 =>
      let v0 := atom_to_int v0
      let v1 := atom_to_int v1
      if v1 == 0 then
        Result.err args "division by zero"
      else
        Result.ok (Node.pair (Node.atom (int_to_atom (v0 / v1)))  (Node.atom (int_to_atom (v0 % v1))))
    | _, _ => Result.err args "Arguments to divmod must be atoms"
  | _ => Result.err args "divmod takes exactly 2 arguments"

def handle_op_gt (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom #[])) =>
    match a0, a1 with
    | Node.atom v0, Node.atom v1 =>
      let v0 := atom_to_int v0
      let v1 := atom_to_int v1
      if v0 > v1 then
        Result.ok (Node.atom #[1])
      else
        Result.ok (Node.atom #[])
    | _, _ => Result.err args "Arguments to gt must be atoms"
  | _ => Result.err args "gt takes exactly 2 arguments"

def handle_op_ash (args: Node) : Result Node :=
  Result.err args "ash not implemented"

/-
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom #[])) =>
    match a0, a1 with
    | Node.atom v0, Node.atom v1 =>
      let v0 := atom_to_int v0
      let v1 := atom_to_int v1
      Result.ok (Node.atom (int_to_atom (v0.shiftLeft_left v1)))
    | _, _ => Result.err args "Arguments to ash must be atoms"
  | _ => Result.err args "ash takes exactly 2 arguments"
 -/

def handle_op_lsh (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom #[])) =>
    match a0, a1 with
    | Node.atom v0, Node.atom v1 =>
      let v0 := atom_to_nat v0
      let v1 := atom_to_int v1
      Result.ok (Node.atom (nat_to_atom (if v1 > 0 then (v0.shiftLeft v1.toNat) else v0.shiftRight (-v1).toNat)))
    | _, _ => Result.err args "Arguments to lsh must be atoms"
  | _ => Result.err args "ash takes exactly 2 arguments"

def handle_op_logand (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom #[])) =>
    match a0, a1 with
    | Node.atom v0, Node.atom v1 =>
      let v0 := atom_to_nat v0
      let v1 := atom_to_nat v1
      Result.ok (Node.atom (nat_to_atom (v0.land v1)))
    | _, _ => Result.err args "Arguments to logand must be atoms"
  | _ => Result.err args "logand takes exactly 2 arguments"

-- this does bitwise or just like how op_logand does bitwise and
def handle_op_logior (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom #[])) =>
    match a0, a1 with
    | Node.atom v0, Node.atom v1 =>
      let v0 := atom_to_nat v0
      let v1 := atom_to_nat v1
      Result.ok (Node.atom (nat_to_atom (v0.lor v1)))
    | _, _ => Result.err args "Arguments to logior must be atoms"
  | _ => Result.err args "logior takes exactly 2 arguments"

-- this does xor
def handle_op_logxor (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.pair a1 (Node.atom #[])) =>
    match a0, a1 with
    | Node.atom v0, Node.atom v1 =>
      let v0 := atom_to_nat v0
      let v1 := atom_to_nat v1
      Result.ok (Node.atom (nat_to_atom (v0.xor v1)))
    | _, _ => Result.err args "Arguments to logxor must be atoms"
  | _ => Result.err args "logxor takes exactly 2 arguments"

def handle_op_lognot (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.atom #[]) =>
    match a0 with
    | Node.atom v0 =>
      let v0 := atom_to_nat v0
      Result.ok (if v0 = 0 then Node.one else Node.nil)
    | _ => Result.err args "Arguments to lognot must be atoms"
  | _ => Result.err args "lognot takes exactly 1 argument"

def handle_op_point_add (args: Node) : Result Node :=
  Result.err args "point_add not implemented"

def handle_op_pubkey_for_exp (args: Node) : Result Node :=
  Result.err args "pubkey_for_exp not implemented"

def handle_op_not (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.atom #[]) =>
    match a0 with
    | Node.atom v0 =>
      if v0 == #[0] then
        Result.ok (Node.atom #[1])
      else
        Result.ok (Node.atom #[])
    | _ => Result.err args "Arguments to not must be atoms"
  | _ => Result.err args "not takes exactly 1 argument"

-- this take vararg arguments and returns true iff any argument is true
def handle_op_any (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.atom #[]) =>
    match a0 with
    | Node.atom v0 =>
      if v0 == #[1] then
        Result.ok (Node.atom #[1])
      else
        Result.ok (Node.atom #[])
    | Node.pair a0 a1 =>
      match a0, a1 with
      | Node.atom v0, Node.atom v1 =>
        if v0 == #[1] || v1 == #[1] then
          Result.ok (Node.atom #[1])
        else
          Result.ok (Node.atom #[])
      | _, _ => Result.err args "Arguments to any must be atoms"
  | _ => Result.err args "any takes at least 1 argument"

-- this take vararg arguments and returns true iff all arguments are true
def handle_op_all (args: Node) : Result Node :=
  match args with
  | Node.pair a0 (Node.atom #[]) =>
    match a0 with
    | Node.atom v0 =>
      if v0 == #[1] then
        Result.ok (Node.atom #[1])
      else
        Result.ok (Node.atom #[])
    | Node.pair a0 a1 =>
      match a0, a1 with
      | Node.atom v0, Node.atom v1 =>
        if v0 == #[1] && v1 == #[1] then
          Result.ok (Node.atom #[1])
        else
          Result.ok (Node.atom #[])
      | _, _ => Result.err args "Arguments to all must be atoms"
  | _ => Result.err args "all takes at least 1 argument"
