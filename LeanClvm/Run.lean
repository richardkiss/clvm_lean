import LeanClvm.Node
import LeanClvm.Opcodes
import LeanClvm.Result
import LeanClvm.Serde
import LeanClvm.Util


def OP_Q: UInt8 := 0x01
def OP_A: UInt8 := 0x02
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


def handle_unused (_args: Node) : Result Node :=
  Result.ok Node.nil



def OP_ARRAY: Array (Node → Result Node) := #[
  handle_unused, handle_unused, handle_unused, handle_op_i, handle_op_c,
  handle_op_f, handle_op_r, handle_op_l, handle_op_x, handle_op_eq, handle_op_gt_s, handle_op_sha256,
  handle_op_substr, handle_op_strlen, handle_op_concat, handle_unused, handle_op_add, handle_op_sub,
  handle_op_mul, handle_op_div, handle_op_divmod, handle_op_gt, handle_op_ash, handle_op_lsh,
  handle_op_logand, handle_op_logior, handle_op_logxor, handle_op_lognot, handle_unused, handle_unused,
  handle_op_point_add, handle_op_pubkey_for_exp, handle_unused, handle_op_not, handle_op_any, handle_op_all
]



def as_list (node: Node) : List Node :=
  match node with
  | Node.atom _ => []
  | Node.pair a b => a::(as_list b)


def as_node (nodes: List Node) : Node :=
  let rec inner_func (nodes: List Node) : Node :=
    match nodes with
    | [] => Node.atom #[]
    | a::b => Node.pair a (inner_func b)
  inner_func nodes


def node_map (f: Node -> Node): Node -> Node :=
  let rec inner_func (node: Node) : Node :=
    match node with
    | Node.atom _ => node
    | Node.pair a b => Node.pair (f a) (inner_func b)
  inner_func


def handle_opcode (byte: UInt8) (args: Node) : Result Node :=
  let f:= match OP_ARRAY[byte.toNat]? with
  | some f => f
  | none => handle_unused
  f args


def apply_weird_mode_opcode (_opcode: Node) (_should_be_nil: Node) (args: Node) : Result Node :=
  Result.err args "Not implemented"


def map_or_err (f: α -> Result α) (arr: List α) : (Result (List α)) :=
  match arr with
  | [] => Result.ok []
  | a::b => match f a with
    | Result.ok node =>
      match map_or_err f b with
      | Result.ok nodes => Result.ok (node::nodes)
      | _other => _other
    | Result.err _ msg => Result.err arr msg


def apply_atom (atom: Array UInt8) (args: Node) : Result Node :=
  node_at (atom_to_nat atom) args


def apply_node (depth: Nat) (program: Node) (args: Node) : Result Node :=
  if depth = 0 then
    Result.err program "depth 0"
  else
    match program with
    | Node.atom atom => apply_atom atom args
    | Node.pair opcode arguments => match opcode with
      | Node.pair inner_opcode should_be_nil => apply_weird_mode_opcode inner_opcode should_be_nil args
      | Node.atom atom =>
          if atom.size == 1 then
            let byte := atom[0]!
            if byte == OP_Q then
              Result.ok arguments
            else
             let eval_args : Result (List Node) := map_or_err (fun node => apply_node (depth-1) node args) (as_list arguments)
             match eval_args with
            | Result.ok eval_args =>
                let new_args := as_node eval_args
                if byte == OP_A then
                    match new_args with
                    | Node.pair program (Node.pair args (Node.atom #[])) => apply_node (depth-1) program args
                    | _ => Result.err new_args "apply takes exactly 2 arguments"
                else
                  handle_opcode byte new_args
            | Result.err _ msg => Result.err arguments msg
          else
            Result.err (Node.atom atom) "Not implemented"


def my_quote: Node := Node.pair (Node.atom #[0x01]) (Node.atom #[2, 3, 4])


#check my_quote
#eval n2h my_quote

def apply (program: Node) (args: Node) : Result Node :=
  apply_node 100 program args

#check apply my_quote my_quote
#eval show_result (apply my_quote my_quote)

#eval atom_to_int #[]
#eval atom_to_int #[0]
#eval atom_to_int #[127]
#eval atom_to_nat #[128]
#eval atom_to_int #[128]
#eval atom_to_int #[255]
#eval atom_to_int #[128, 0]
#eval atom_to_int #[127, 255]


def rh (hex: String) : String := show_result (apply (h2n hex) (h2n "00"))

def my_tree: Node := h2n "ff8474686973ff826973ffff02847465737480"

#eval (n2h my_tree)
#eval show_result (apply (Node.atom #[11]) my_tree)

#eval rh "ff03ffff0180ffff018200c8ffff0182012c80"
