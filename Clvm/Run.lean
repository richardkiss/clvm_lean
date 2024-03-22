import Clvm.Node
import Clvm.Opcodes
import Clvm.Result
import Clvm.Serde
import Clvm.Util


def OP_Q := 0x01
def OP_A := 0x02

def OP_I: UInt8 := 0x03
def OP_C: UInt8 := 0x04
def OP_F: UInt8 := 0x05
def OP_R: UInt8 := 0x06
def OP_L: UInt8 := 0x07
def OP_X: UInt8 := 0x08

def OP_EQ: UInt8 := 0x09
def OP_GT_S: UInt8 := 0x0a
def OP_SHA256: UInt8 := 0x0b
def OP_SUBSTR: UInt8 := 0x0c
def OP_STRLEN: UInt8 := 0x0d
def OP_CONCAT: UInt8 := 0x0e

def OP_ADD: UInt8 := 0x10
def OP_SUB: UInt8 := 0x11
def OP_MUL: UInt8 := 0x12
def OP_DIV: UInt8 := 0x13
def OP_DIVMOD: UInt8 := 0x14
def OP_GT: UInt8 := 0x15
def OP_ASH: UInt8 := 0x16
def OP_LSH: UInt8 := 0x17

def OP_LOGAND: UInt8 := 0x18
def OP_LOGIOR: UInt8 := 0x19
def OP_LOGXOR: UInt8 := 0x1a
def OP_LOGNOT: UInt8 := 0x1b

def OP_POINT_ADD: UInt8 := 0x1d
def OP_PUBKEY_FOR_EXP: UInt8 := 0x1e

def OP_NOT: UInt8 := 0x20
def OP_ANY: UInt8 := 0x21
def OP_ALL: UInt8 := 0x22

def OP_SOFTFORK: UInt8 := 0x24


def handle_unused (_args: Node) : Result Node Node :=
  Result.ok Node.nil



def OP_ARRAY: Array (Node → Result Node Node) := #[
  handle_unused, handle_unused, handle_unused, handle_op_i, -- 0 to 3
  handle_op_c, handle_op_f, handle_op_r, handle_op_l, -- 4 to 7
  handle_op_x, handle_op_eq, handle_op_gt_s, handle_op_sha256, -- 8 to 0x0b
  handle_op_substr, handle_op_strlen, handle_op_concat, handle_unused, -- 0x0c to 0x0f
  handle_op_add, handle_op_sub, handle_op_mul, handle_op_div,  -- 0x10 to 0x13
  handle_op_divmod, handle_op_gt, handle_op_ash, handle_op_lsh, -- 0x14 to 0x17
  handle_op_logand, handle_op_logior, handle_op_logxor, handle_op_lognot, -- 0x18 to 0x1b
  handle_unused, handle_op_point_add, handle_op_pubkey_for_exp, handle_unused, -- 0x1c to 0x1f
  handle_op_not, handle_op_any, handle_op_all, handle_unused -- 0x20 to 0x23
]



def as_node (nodes: List Node) : Node :=
  let rec inner_func (nodes: List Node) : Node :=
    match nodes with
    | [] => Node.nil
    | a::b => Node.pair a (inner_func b)
  inner_func nodes


def node_map (f: Node -> Node): Node -> Node :=
  let rec inner_func (node: Node) : Node :=
    match node with
    | Node.atom _ => node
    | Node.pair a b => Node.pair (f a) (inner_func b)
  inner_func


def handle_opcode (byte: Nat) (args: Node) : Result Node Node :=
  let f:= match byte with
  | 0x03 => handle_op_i
  | 0x04 => handle_op_c
  | 0x05 => handle_op_f
  | 0x06 => handle_op_r
  | 0x07 => handle_op_l
  | 0x08 => handle_op_x
  | 0x09 => handle_op_eq
  | 0x0a => handle_op_gt_s
  | 0x0b => handle_op_sha256
  | 0x0c => handle_op_substr
  | 0x0d => handle_op_strlen
  | 0x0e => handle_op_concat
  | 0x10 => handle_op_add
  | 0x11 => handle_op_sub
  | 0x12 => handle_op_mul
  | 0x13 => handle_op_div
  | 0x14 => handle_op_divmod
  | 0x15 => handle_op_gt
  | 0x16 => handle_op_ash
  | 0x17 => handle_op_lsh
  | 0x18 => handle_op_logand
  | 0x19 => handle_op_logior
  | 0x1a => handle_op_logxor
  | 0x1b => handle_op_lognot
  | 0x1d => handle_op_point_add
  | 0x1e => handle_op_pubkey_for_exp
  | 0x20 => handle_op_not
  | 0x21 => handle_op_any
  | 0x22 => handle_op_all
  | _ => handle_unused
  f args


def apply_cons_mode_syntax (opcode: Node) (should_be_nil: Node) (operand_list: Node) (program : Node): Result Node Node :=
  match opcode, should_be_nil with
  | Node.atom opcode_atom, Node.atom ⟨ [], _ ⟩  =>
    match opcode_atom.data with
    | [byte] => handle_opcode byte operand_list
    | _ => Result.err program "invalid operator"
  | _, _ => Result.err program "in ((X)...) syntax X must be lone atom"


def map_or_err (f: Node -> Result Node Node) (args: Node) : (Result Node Node) :=
  match args with
  | Node.atom ⟨ _, _ ⟩  => Result.ok Node.nil
  | Node.pair n1 n2 => match map_or_err f n2 with
    | Result.ok r2 =>
      match f n1 with
      | Result.ok r1 => Result.ok (Node.pair r1 r2)
      | _other => _other
    | Result.err a msg => Result.err a msg


#eval node_at (atom_to_nat #[0x00, 0x02]) (h2n "ff7701")


def apply_node (depth: Nat) (program: Node) (args: Node) : Result Node Node :=
  if depth = 0 then
    Result.err program "depth 0"
  else
    match program with
    | Node.atom atom => node_at (atom_to_nat atom) args
    | Node.pair opcode arguments => match opcode with
      | Node.pair inner_opcode should_be_nil => apply_cons_mode_syntax inner_opcode should_be_nil arguments program
      | Node.atom atom =>
          if atom.length = 1 then
            let byte := atom.data[0]!
            if byte = OP_Q then
              Result.ok arguments
            else
             let eval_args : Result Node Node := map_or_err (fun node => apply_node (depth-1) node args) arguments
             match eval_args with
            | Result.ok eval_args =>
                if byte = OP_A then
                    match eval_args with
                    | Node.pair program (Node.pair args (Node.atom ⟨ [], _ ⟩ )) => apply_node (depth-1) program args
                    | _ => Result.err eval_args "apply requires exactly 2 parameters"
                else
                  handle_opcode byte eval_args
            | Result.err arg msg => Result.err arg msg
          else
            Result.err (Node.atom atom) "invalid operator"


def my_quote: Node := Node.pair (Node.atom #[0x01]) (Node.atom #[2, 3, 4])


#check my_quote
#eval n2h my_quote

def apply (program: Node) (args: Node) : Result Node Node :=
  apply_node 100 program args

#check apply my_quote my_quote
-- #eval show_result (apply my_quote my_quote)

#eval atom_to_int ([]: List Nat)
#eval atom_to_int [0]
#eval atom_to_int [127]
#eval atom_to_nat [128]
#eval atom_to_int [128]
#eval atom_to_int [255]
#eval atom_to_int [128, 0]
#eval atom_to_int [127, 255]


def rh (hex: String) : String := show_result (apply (h2n hex) (h2n "00"))

def my_tree: Node := h2n "ff8474686973ff826973ffff02847465737480"

#eval (n2h my_tree)
#eval show_result (apply (Node.atom #[11]) my_tree)

#eval rh "ff14ffff010affff010380"
