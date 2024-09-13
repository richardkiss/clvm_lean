import Clvm.H2n
import Clvm.Node
import Clvm.Opcodes
import Clvm.Serde
import Clvm.Sha256


def OP_Q := 0x01
def OP_A := 0x02

def OP_I := 0x03
def OP_C := 0x04
def OP_F := 0x05
def OP_R := 0x06
def OP_L := 0x07
def OP_X := 0x08

def OP_EQ := 0x09
def OP_GT_S := 0x0a
def OP_SHA256 := 0x0b
def OP_SUBSTR := 0x0c
def OP_STRLEN := 0x0d
def OP_CONCAT := 0x0e

def OP_ADD := 0x10
def OP_SUB := 0x11
def OP_MUL := 0x12
def OP_DIV := 0x13
def OP_DIVMOD := 0x14
def OP_GT := 0x15
def OP_ASH := 0x16
def OP_LSH := 0x17

def OP_LOGAND := 0x18
def OP_LOGIOR := 0x19
def OP_LOGXOR := 0x1a
def OP_LOGNOT := 0x1b

def OP_POINT_ADD := 0x1d
def OP_PUBKEY_FOR_EXP := 0x1e

def OP_NOT := 0x20
def OP_ANY := 0x21
def OP_ALL := 0x22

def OP_SOFTFORK := 0x24



def handle_unused (_args: Node) : Except (Node × String) Node :=
  Except.ok Node.nil


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


def handle_opcode (byte: Nat) (args: Node) : Except (Node × String) Node :=
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


def handle_opcode_for_atom (a: Atom) (args: Node) : Except (Node × String) Node :=
  match a.data with
  | [byte] => handle_opcode byte args
  | _ => handle_unused args


def apply_cons_mode_syntax (opcode: Node) (should_be_nil: Node) (operand_list: Node) (program : Node): Except (Node × String) Node :=
  match opcode, should_be_nil with
  | Node.atom opcode_atom, Node.atom ⟨ [], _ ⟩  =>
    match opcode_atom.data with
    | [byte] => handle_opcode byte operand_list
    | _ => Except.err program "invalid operator"
  | _, _ => Except.err program "in ((X)...) syntax X must be lone atom"


def map_or_err (f: Node -> Except (Node × String) Node) (args: Node) : (Except (Node × String) Node) :=
  match args with
  | Node.atom ⟨ _, _ ⟩  => Except.ok Node.nil
  | Node.pair n1 n2 => do
      let r2 ← map_or_err f n2
      let r1 ← f n1
      return Node.pair r1 r2


#eval! node_at (atom_to_nat [0x00, 0x02]) (h2n! "ff7701")


def exactly_two_args (args: Node) : Except (Node × String) (Node × Node) :=
  match args with
  | Node.pair a (Node.pair b (Node.atom ⟨ [], _ ⟩ )) => Except.ok ⟨ a, b ⟩
  | _ => Except.err args "apply requires exactly 2 parameters"


def apply_node (depth: Nat) (program: Node) (args: Node) : Except (Node × String) Node :=
  if depth = 0 then
    Except.err program "depth 0"
  else
    match program with
    | Node.atom atom => node_at (atom_to_nat atom) args
    | Node.pair opcode arguments => match opcode with
      | Node.pair inner_opcode should_be_nil => apply_cons_mode_syntax inner_opcode should_be_nil arguments program
      | Node.atom atom =>
          if atom.data = [OP_Q] then
            Except.ok arguments
          else do
            let args ← map_or_err (apply_node (depth-1) · args) arguments
            if atom.data = [OP_A] then
              let ⟨ p, e ⟩ ← exactly_two_args args
              apply_node (depth-1) p e
            else
              handle_opcode_for_atom atom args


def my_quote: Node := Node.pair (Node.atom [0x01]) (Node.atom [2, 3, 4])


#check my_quote
#eval n2h my_quote

def apply (program: Node) (args: Node) : Except (Node × String) Node :=
  apply_node 100 program args


def bruns_to (program: Node) (args: Node) (r: Node) := ∃ depth, apply_node depth program args = Except.ok r


-- "node_applies" means "program does not fail when run for some deep enough depth"
def node_applies (n args: Node) := ∃ k, is_ok (apply_node k n args)



#check apply my_quote my_quote
-- #eval show_Except (apply my_quote my_quote)


def rh (hex: String) : String := toString (apply (h2n! hex) (h2n! "00"))

def my_tree: Node := h2n! "ff8474686973ff826973ffff02847465737480"

#eval! (n2h my_tree)
#eval! toString (apply (Node.atom [11]) my_tree)

#eval! rh "ff14ffff010affff010380"


---

@[simp]
def operator_program (depth opcode: Nat) (args env: Node) : Except (Node × String) Node := apply_node depth (Node.pair (Node.atom [opcode]) args) env


theorem not_quote_or_atom {depth opcode: Nat} {args env: Node}
  {h_depth: depth ≠ 0 }
  {h_opcode: opcode ≤ 255}
  {h_not_q: opcode ≠ OP_Q}
  {h_not_a: opcode ≠ OP_A}
  (h_map_or_err: (map_or_err (fun node => apply_node (depth-1) node env) args = Except.ok new_args)) :
    operator_program depth opcode args env = handle_opcode opcode new_args := by
  simp [apply_node]
  simp [h_depth]
  simp [atom_cast, max_255]
  simp [h_opcode]
  simp [h_not_q]
  simp [h_not_a]
  simp [handle_opcode_for_atom, bind, Except.bind]
  rw [h_map_or_err]


#eval! map_or_err (fun node => apply_node 99 node 10) (Node.atom (Atom.to [1]))


lemma int_to_atom_nil: (int_to_atom 0).data = [] := by rfl
