import Mathlib


import Clvm.Atom
import Clvm.Coe
import Clvm.Ints.Basic
import Clvm.Run

--import Std.Classes.Cast
--import Std.Data.Int.Init.Lemmas
--import Std.Data.UInt


--import Mathlib.Algebra.EuclideanDomain.Defs
--import Mathlib.Tactic.LibrarySearch
--import Mathlib.Data.Fin.Basic


-- we have here several theorems about running programs

def Q1 : Node := Node.pair 1 1


-- n is a node. We have (a (q . n) 0) => n
example { n: Node } : apply (Node.pair 1 n) Node.nil = Except.ok n := by rfl


-- (q . 1).replace("r", n) => (1 . n)

example { x: Node } : replace Q1 [Replacement.mk "r" x] = Node.pair 1 x := by rfl


-- try following paths

-- brun '2 (x . y)' => x
example { x y: Node } : bruns_to 2 (Node.pair x y) x := by use 1; rfl

-- brun '3 (x . y)' => y
example { x y: Node } : bruns_to 3 (Node.pair x y) y := by use 1; rfl

-- (i (q . 1) 2 3)
def if_example_true : Node := [3, Q1, 2, 3]

-- brun (i (q . 1) 2 3) (x . y) => x
example { x y: Node } : bruns_to if_example_true (Node.pair x y) x := by use 2; rfl


def if_example_false : Node := [3, 0, 2, 3]

-- brun (i 0 2 3) (x . y) => y
example { x y: Node } : bruns_to if_example_false (Node.pair x y) y := by use 2; rfl

-- brun (+) n => 0
example { n: Node } : bruns_to (Node.pair OP_ADD Node.nil) n 0 := by use 1; rfl


def cons_example : Node := [OP_C, 2, 3]

-- brun (c 2 3) (x . y) => (x . y)
example { x y: Node } : bruns_to cons_example (Node.pair x y) (Node.pair x y) := by use 2; rfl

-- brun (f 1) (x . y) => x
example { x y: Node } : bruns_to [OP_F, 1] (Node.pair x y) x := by use 2; rfl

-- brun (r 1) (x . y) => y
example { x y: Node } : bruns_to [OP_R, 1] (Node.pair x y) y := by use 2; rfl


-- (l n) => 0 or 1 depending on whether n is an atom
example { x: Node } : handle_op_l [x] = Except.ok (if is_atom x then Node.nil else Node.one) := by
  cases x <;> rfl

-- brun (l 1) x => 0 or 1
example { x: Node } : bruns_to [OP_L, 1] x (if is_atom x then Node.nil else Node.one) := by
  cases x <;> use 2 <;> rfl


-- brun (strlen 1) x => a.size (where a is the atom for x)
example { a: Atom } : bruns_to [OP_STRLEN, 1] (Node.atom a) (Node.atom a.length) := by use 2; rfl


-- many theorems will use `int_list_to_node_list` so we make sure they work right



theorem try_int_list_to_node_list_general {zs : List Int} : (int_list_to_node_list zs) = zs.map int_to_atom := by
  induction zs with
  | nil => simp [int_list_to_node_list]
  | cons z0 z_tail ih =>
    unfold int_list_to_node_list List.map
    simp
    rw [ih]
    rfl

example { z0 z1 : Int } : (int_list_to_node_list [z0, z1]) = [Node.atom (int_to_atom z0), Node.atom (int_to_atom z1)] := by
  simp [try_int_list_to_node_list_general]


-- we use `node_to_list` a lot in handle_op_xxx so let's prove it works right

def identity (n: Node) : Except (Node × String) Node := Except.ok n

example : node_to_list Node.nil identity = Except.ok [] := by
  rfl

-- node_to_list works on a single atom
example (n: Node) : node_to_list (Node.pair n Node.nil) identity = Except.ok [n] := by
  rfl

-- node_to_list works on two atoms
example (n1 n2 : Node) : node_to_list (Node.pair n1 (Node.pair n2 Node.nil)) identity = Except.ok [n1, n2] := by
  rfl


def atoms_only (n: Node) : Except (Node × String) Node :=
  match n with
  | Node.atom _ => Except.ok n
  | _ => Except.err n "not an atom"


-- define "rightmost_node" as the atom we hit when we repeatedly go to the right
def rightmost_node (n: Node): Atom :=
  match n with
  | Node.atom a => a
  | Node.pair _ rest => rightmost_node rest


-- adding something to the beginning of an existing list doesn't change the rightmost node
example { n1 n2 : Node } : rightmost_node (Node.pair n1 n2) = rightmost_node n2 := by
  rfl


-- define "right_depth" as the distance to the rightmost node
def right_depth (n: Node) : Nat := match n with
  | Node.atom _ => 0
  | Node.pair _ n2 => 1 + (right_depth n2)


-- the depth is at least one if a node is not an atom
example { n1 n2 : Node } : right_depth (Node.pair n1 n2) ≥ 1 := by
  unfold right_depth
  exact Nat.le_add_right 1 (right_depth n2)

-- the depth goes up one at a time
example { n1 n2 : Node } : right_depth (Node.pair n1 n2) = 1 + right_depth n2 := by
  unfold right_depth
  cases n2 <;> rfl

-- prove `node_to_list` works on nil
example : node_to_list Node.nil atoms_only = Except.ok [] := by
  rfl

-- define a new property : "is_nil_terminated_list" which is true if the rightmost node is nil



-----
-- some more handle_op_xxx opcodes


-- set_option maxHeartbeats 1000000

-- (l n) => 0 or 1 depending on whether n is an atom

theorem op_sha256 { a: Atom } : handle_op_sha256 [Node.atom a] = Except.ok (Node.atom (sha256 a.data)) := by
  rfl


example: Int.ofNat (11: UInt8).val.val = (11: Int) := by simp


example: int_to_atom (11: UInt8).toNat = (11: Int) := by simp



theorem cast_helper (u : Nat) : (instNatCastInt.1 u) = u := by simp


example : Int.ofNat (11: UInt8).toNat = (11: Int) := by
  simp

example: Int.ofNat (11: UInt8).val.val = (11: Int) := by simp





theorem round_trip_int_cast (zs: List Int) : args_to_int ((node_list_to_node ∘ int_list_to_node_list) zs) = Except.ok zs := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>

    simp

    unfold int_list_to_node_list
    unfold node_list_to_node
    unfold args_to_int
    unfold node_to_list
    simp only [gt_iff_lt]

    have zzz0: is_nil_terminated_list (node_list_to_node (int_list_to_node_list zs)) := by
      simp at ih
      exact args_to_int_okay_nil_terminated ⟨zs, ih⟩

    have zzz1: List.length (node_to_node_list_terminator (node_list_to_node (int_list_to_node_list zs))).2 = 0 := by
      rw [node_to_node_list_terminator_rewrite]
      congr

    have zzz: (node_to_node_list_terminator (Node.pair (Node.atom (int_to_atom z)) (node_list_to_node (int_list_to_node_list zs)))).2.length = 0 := by
      rw [node_to_node_list_terminator_rewrite]
      congr

    simp [zzz]
    unfold node_to_node_list_terminator
    unfold List.map
    unfold list_except_to_except_list
    simp [atom_to_int_cast]
    unfold only_atoms
    simp

    simp at ih
    unfold args_to_int at ih
    unfold node_to_list at ih
    simp at ih
    simp [zzz1] at ih
    simp [ih]
    --exact round_trip_int
    --sorry


-- set_option maxHeartbeats 2400000


--theorem run_sha256_atom { a: Atom } : bruns_to [OP_SHA256.toNat, 1] a (Node.atom (sha256 a)) := by
--  use 2
--  rfl


theorem run_sha256_two_atoms { a1 a2: Atom } : bruns_to [OP_SHA256, 2, 5] [a1, a2] (Node.atom (sha256 (a1 ++ a2))) := by
  use 2 ; rfl


theorem run_sha256_three_atoms { a1 a2 a3: Atom } : bruns_to [OP_SHA256, 2, 5, 11] [a1, a2, a3] (Node.atom (sha256 ((a1 ++ a2) ++ a3))) := by
  use 2 ; rfl


theorem op_add_nil : handle_op_add Node.nil = Except.ok 0 := by rfl


theorem op_add_n_numbers { zs : List Int } : handle_op_add zs = Except.ok (Node.atom (int_to_atom (zs.foldl (fun a b => (a + b)) 0))) := by
  unfold handle_op_add
  rw [round_trip_int_cast]


def quote_node (n: Node) : Node := Node.pair (Node.atom [1]) n


def quoted_nodes (ns : List Node) : Node :=
  match ns with
  | [] => Node.nil
  | n :: ns0 =>
      Node.pair (quote_node n) (quoted_nodes ns0)


#eval quoted_nodes [1, 2, 3]


-- we can `map_or_err` a list of subprograms that apply, we end up with a list of Excepts in the intuitive way. This provides a shortcut
lemma map_or_err_good_subprograms {Excepts subprograms: List Node}: map_or_err (fun n ↦ apply_node k n env) (node_list_to_node subprograms) = Except.ok (node_list_to_node Excepts) := by
  sorry





lemma map_or_err_to_quoted_nodes {hv: v > 0} { f: Node -> Except Node Node } { ns: List Node } : map_or_err (fun n => apply_node v n args) (quoted_nodes ns) = Except.ok (node_list_to_node ns) := by
  induction ns with
  | nil => rfl
  | cons head tail h_tail =>
    simp [map_or_err, apply_node, node_at, atom_to_nat, node_at_wdepth, list_nat_to_nat]
    unfold quote_node
    simp [atom_cast]
    simp [h_tail]
    unfold apply_node
    have hv0: ¬ v = 0 := by linarith
    simp [hv0]
    rfl


theorem run_add_nil: apply ([OP_ADD, 0]: Node) (0: Node) = Except.ok 0 := by
  rfl


theorem run_add_one_number_old {z: Int}: apply ([OP_ADD, 1]: Node) (z: Node) = Except.ok (z: Node) := by
  simp
  unfold OP_ADD
  simp [nat_list_to_int_list, int_list_to_node_list]
  have h16: int_to_atom 16 = [16] := by
    rfl
  have h1: int_to_atom 1 = [1] := by
    rfl
  rw [h16, h1]
  simp [atom_cast, max_255]
  simp [node_list_to_node]

  -- input arguments are simplified
  unfold apply apply_node
  simp
  unfold OP_Q OP_A
  simp

  simp [map_or_err, apply_node, node_at, atom_to_nat, node_at_wdepth, list_nat_to_nat]

  simp [handle_opcode]

  unfold handle_op_add
  simp [List.foldl, args_to_int, node_to_list, node_to_node_list_terminator, list_except_to_except_list]
  simp [int_to_atom, int_to_twos_comp]


theorem run_add_two_numbers {z1 z2: Int}: apply ([OP_ADD, 2, 5]: Node) ([z1, z2]: Node) = Except.ok ((z1 + z2): Node) := by
  simp
  unfold OP_ADD
  simp [nat_list_to_int_list, int_list_to_node_list]
  have h16: int_to_atom 16 = [16] := by
    rfl
  have h2: int_to_atom 2 = [2] := by
    rfl
  have h5: int_to_atom 5 = [5] := by
    rfl
  rw [h16, h2, h5]
  simp [atom_cast, max_255]
  simp [node_list_to_node]

  -- input arguments are simplified
  unfold apply apply_node
  simp
  unfold OP_Q OP_A
  simp

  simp [map_or_err, apply_node, node_at, atom_to_nat, node_at_wdepth, list_nat_to_nat]
  simp [handle_opcode]
  simp [handle_op_add]

  unfold List.foldl

  simp [args_to_int, node_to_list, node_to_node_list_terminator, list_except_to_except_list]
  simp [List.length, int_to_atom, int_to_twos_comp]


theorem run_add_two_quoted_numbers {z1 z2: Int}: apply ([((OP_ADD): Node), (Node.pair 1 z1), (Node.pair 1 z2)]: Node) Node.nil = Except.ok ((z1 + z2): Node) := by
  simp
  unfold OP_ADD
  simp [node_list_to_node]

  -- input arguments are simplified
  simp [apply, apply_node]
  have h16: int_to_atom 16 = [16] := by
    rfl
  rw [h16]
  simp [atom_cast, max_255, getElem!, OP_Q, OP_A, Atom.length]

  simp [map_or_err, apply_node, node_at, atom_to_nat, node_at_wdepth, list_nat_to_nat]
  unfold apply_node
  simp
  have h1: int_to_atom 1 = [1] := by
    rfl
  rw [h1]
  simp [atom_cast, Atom.length, max_255, getElem!, OP_Q, OP_A]

  simp [handle_opcode]
  simp [handle_op_add]
  simp [args_to_int, node_to_list, node_to_node_list_terminator, list_except_to_except_list, List.length]


#print axioms run_add_two_quoted_numbers


theorem run_mul_two_quoted_numbers {z1 z2: Int}: apply ([((OP_MUL): Node), (Node.pair 1 z1), (Node.pair 1 z2)]: Node) Node.nil = Except.ok ((z1 * z2): Node) := by
  simp
  unfold OP_MUL
  simp [node_list_to_node]

  -- input arguments are simplified
  simp [apply, apply_node]
  have h18: int_to_atom 18 = [18] := by
    rfl
  rw [h18]
  simp [atom_cast, max_255, getElem!, OP_Q, OP_A, Atom.length]

  simp [map_or_err, apply_node, node_at, atom_to_nat, node_at_wdepth, list_nat_to_nat]
  unfold apply_node
  simp
  have h1: int_to_atom 1 = [1] := by
    rfl
  rw [h1]
  simp [atom_cast, Atom.length, max_255, getElem!, OP_Q, OP_A]

  simp [handle_opcode]
  simp [handle_op_mul]
  simp [args_to_int, node_to_list, node_to_node_list_terminator, list_except_to_except_list, List.length]


-- "node_applies" means "program does not fail when run for some deep enough depth"
