-- import Mathlib
import Mathlib.Tactic.Linarith
import Mathlib.Data.UInt

import Init.Coe
import Init.Data
import Init.Data.ByteArray
import Init.Data.Fin
import Init.Data.Nat
import Init.Data.Nat.Bitwise

import Init.Data.UInt
import Init.Prelude
import Init.Tactics
--import Init.Data.Nat.Lemmas

import Clvm.Atom
import Clvm.Basic
import Clvm.Casts
import Clvm.Coe
import Clvm.Hex
import Clvm.Node
import Clvm.Opcodes
import Clvm.Result
import Clvm.Run
import Clvm.Serde
import Clvm.Util

import Std.Classes.Cast
--import Std.Data.Int.Init.Lemmas
import Std.Data.UInt


import Mathlib.Algebra.EuclideanDomain.Defs
--import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Fin.Basic


-- we have here several theorems about running programs

def quote_one : Node := "ff0101"


-- n is a node. We have (a (q . n) 0) => n

theorem run_quote_x_is_x { n: Node } : apply (Node.pair 1 n) Node.nil = Result.ok n := by
  rfl

-- (q . 1).replace("r", n) => (1 . n)

theorem replace_quote_one_r_with_x_is_quote_x { x: Node } : replace quote_one [Replacement.mk "r" x] = Node.pair 1 x := by
  have hq : quote_one = Node.pair 1 1 := by
    rfl
  rw [hq]
  simp [replace]
  have split: split_replacements [{ path := nodepath_for_string "r", replacement := x }] = ( [], [{ path := 1, replacement := x }], none ) := by
    rfl
  rw [split]
  simp


-- try following paths

-- brun '2 (x . y)' => x
theorem follow_path_2 { x y: Node } : apply 2 (Node.pair x y) = Result.ok x := by
  rfl

-- brun '3 (x . y)' => y
theorem follow_path_3 { x y: Node } : apply 3 (Node.pair x y) = Result.ok y := by
  rfl

-- (i (q . 1) 2 3)
def if_example_true : Node := [3, (Node.pair 1 1), 2, 3]

-- brun (i (q . 1) 2 3) (x . y) => x
theorem check_if_true { x y: Node } : apply if_example_true (Node.pair x y) = Result.ok x := by
  rfl


def if_example_false : Node := [3, (Node.pair 1 0), 2, 3]

-- brun (i (q . 0) 2 3) (x . y) => y
theorem check_if_false { x y: Node } : apply if_example_false (Node.pair x y) = Result.ok y := by
  rfl

-- brun (+) n => 0
theorem run_add_nil_is_0 { n: Node } : apply (Node.pair OP_ADD.toNat Node.nil) n = Result.ok 0 := by
  rfl


def cons_example : Node := [4, 2, 3]

-- brun (c 2 3) (x . y) => (x . y)
theorem run_cons { x y: Node } : apply cons_example (Node.pair x y) = Result.ok (Node.pair x y) := by
  rfl

-- brun (f 1) (x . y) => x
theorem run_first { x y: Node } : apply [OP_F.toNat, 1] (Node.pair x y) = Result.ok x := by
  rfl

-- brun (r 1) (x . y) => y
theorem run_rest { x y: Node } : apply [OP_R.toNat, 1] (Node.pair x y) = Result.ok y := by
  rfl


def is_atom (n: Node): Bool := match n with
  | Node.atom _ => true
  | _ => false

-- (l n) => 0 or 1 depending on whether n is an atom
theorem op_list { x: Node } : handle_op_l [x] = Result.ok (if is_atom x then Node.nil else Node.one) := by
  cases x <;> rfl

-- brun (l 1) x => 0 or 1
theorem run_list { x: Node } : apply [OP_L.toNat, 1] x = Result.ok (if is_atom x then Node.nil else Node.one) := by
  cases x <;> rfl


def strlen_example : Node := [OP_STRLEN.toNat, 1]

-- brun (strlen 1) x => a.size (where a is the atom for x)
theorem run_strlen { a: Atom } : apply strlen_example a = Result.ok (Node.atom a.size) :=
  rfl


-- many theorems will use `int_list_to_node_list` so we make sure they work right

theorem try_int_list_to_node_list { z0 z1 : Int } : (int_list_to_node_list [z0, z1]) = [Node.atom (int_to_atom z0), Node.atom (int_to_atom z1)] := by
  rfl


-- TODO: rewrite using induction on the list rather than the length

theorem try_int_list_to_node_list_general {k : Nat} : (∀ zl : List Int, zl.length ≤ k → (int_list_to_node_list zl) = zl.map int_to_atom) := by
  induction' k with k0 ih
  intro z_list
  intro h_length
  have h_nil: z_list = [] := by
    cases z_list with
    | nil => rfl
    | cons head tail =>
      simp
      unfold List.length at h_length
      linarith
  rw [h_nil]
  rfl
  intro z_list
  intro h_length
  cases z_list with
  | nil => rfl
  | cons z0 z_tail =>
    have h_tail: z_tail.length ≤ k0 := by
      simp [List.length] at h_length
      linarith
    unfold int_list_to_node_list
    unfold List.map
    have h_tail2: (int_list_to_node_list z_tail) = z_tail.map int_to_atom := by
      exact ih z_tail h_tail
    rw [h_tail2]
    rfl



-- we use `node_to_list` a lot in handle_op_xxx so let's prove it works right

def identity (n: Node) : NResult Node := NResult.ok n

theorem node_to_list_on_nil : node_to_list Node.nil identity = NResult.ok [] := by
  rfl

-- node_to_list works on a single atom
example (n: Node) : node_to_list (Node.pair n Node.nil) identity = NResult.ok [n] := by
  rfl

-- node_to_list works on two atoms
example (n1 n2 : Node) : node_to_list (Node.pair n1 (Node.pair n2 Node.nil)) identity = NResult.ok [n1, n2] := by
  rfl


def atoms_only (n: Node) : NResult Node :=
  match n with
  | Node.atom _ => NResult.ok n
  | _ => NResult.err n "not an atom"


-- define "rightmost_node" as the atom we hit when we repeatedly go to the right
def rightmost_node (n: Node): Atom :=
  match n with
  | Node.atom a => a
  | Node.pair _ rest => rightmost_node rest

-- adding something to the beginning of an existing list doesn't change the rightmost node
theorem rightmost_idempotent { n1 n2 : Node } : rightmost_node (Node.pair n1 n2) = rightmost_node n2 := by
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
example : node_to_list Node.nil atoms_only = NResult.ok [] := by
  rfl

-- define a new property : "is_nil_terminated_list" which is true if the rightmost node is nil

def is_nil_terminated_list (n: Node): Bool := (rightmost_node n).size = 0

-- adding something to the beginning of an existing list doesn't change the nil-terminated property
theorem nil_terminated_idempotent { n1 n2 : Node } : is_nil_terminated_list (Node.pair n1 n2) = is_nil_terminated_list n2 := by
  rfl


-- the first step for many handle_op_xxx functions is to convert a node to a list of nodes with node_to_node_list_terminator
-- let's prove it works right
lemma node_list_terminator_ind { n1 n2 : Node } : node_to_node_list_terminator (Node.pair n1 n2) = ⟨ n1 :: (node_to_node_list_terminator n2).1, (node_to_node_list_terminator n2).2⟩ := by
  rfl


-- for all nodes, the second element of the result of node_to_node_list_terminator is the rightmost node

theorem node_to_node_list_terminator_ok { n : Node } : (node_to_node_list_terminator n).2 = rightmost_node n := by
  induction' n with atom n1 n2 _ h2
  rfl
  unfold rightmost_node
  rw [← h2]
  rfl



-- now let's work on (node_to_node_list_terminator).1

def alt_node_to_node_list_terminator_without_terminator (n: Node) : (List Node) :=
  match n with
  | Node.atom _ => []
  | Node.pair n1 n2 => n1 :: alt_node_to_node_list_terminator_without_terminator n2


-- we will show that (node_to_node_list_terminator).1 is the same as alt_node_to_node_list_terminator_without_terminator
theorem node_to_node_list_terminator_1 { n : Node } : (node_to_node_list_terminator n).1 = alt_node_to_node_list_terminator_without_terminator n := by
  induction' n with atom n1 n2 _ h2
  rfl
  unfold node_to_node_list_terminator
  simp
  rw [h2]
  rfl


-- and here's the simpler version
theorem node_to_node_list_terminator_rewrite { n : Node } : node_to_node_list_terminator n = ⟨ alt_node_to_node_list_terminator_without_terminator n, rightmost_node n ⟩ := by
  rw [← node_to_node_list_terminator_1, ← node_to_node_list_terminator_ok]


-- now we can prove that node_to_list works on a list of atoms

-- theorem node_to_atoms_only_list_on_one_atom (a: Atom) : node_to_list (Node.pair (Node.atom a) Node.nil) atoms_only = NResult.ok [n] := by
--   have h_is_ok : atoms_only (Node.atom a) = NResult.ok (Node.atom a) := by rfl


-----
-- some more handle_op_xxx opcodes


-- set_option maxHeartbeats 1000000

-- (l n) => 0 or 1 depending on whether n is an atom
theorem op_sha256 { a: Atom } : handle_op_sha256 [Node.atom a] = Result.ok (Node.atom (sha256 a)) := by
  unfold handle_op_sha256
  simp [node_list_to_node]
  simp [atom_only_cast, node_to_list, node_to_node_list_terminator, list_nresult_to_nresult_list]



example: Int.ofNat (11: UInt8).val.val = (11: Int) := by simp


example: int_to_atom (11: UInt8).toNat = (11: Int) := by simp



example : (int_to_atom (UInt8.toNat OP_SHA256)) = #[11] := by
  unfold OP_SHA256
  unfold UInt8.toNat
  unfold UInt8.val
  unfold Fin.val
  unfold UInt8.instOfNat
  conv_lhs => simp


theorem cast_helper (u : Nat) : (instNatCastInt.1 u) = u := by simp


example : Int.ofNat (11: UInt8).toNat = (11: Int) := by
  simp

example: Int.ofNat (11: UInt8).val.val = (11: Int) := by simp

example: [OP_SHA256.toNat, 1] = Node.atom #[] := by
  simp
  unfold OP_SHA256
  unfold UInt8.toNat
  unfold UInt8.val
  simp
  simp [nat_list_to_int_list, int_list_to_node_list, int_to_atom, nat_to_atom, nat_to_atom.inner_func, Nat.toUInt8]
  unfold List.toArray List.toArrayAux Array.push Array.mkEmpty List.concat List.toArrayAux
  simp







theorem run_sha256 { a: Atom } : apply [OP_SHA256.toNat, 1] a = Result.ok (Node.atom (sha256 a)) := by
  simp [Function.comp, nat_list_to_int_list, int_list_to_node_list, node_list_to_node]
  unfold OP_SHA256

  simp

  unfold Nat.cast NatCast.natCast

  have h1: (instNatCastInt.1 (UInt8.toNat OP_SHA256)) = UInt8.toNat OP_SHA256 := by
    simp

  rw [h1]
  unfold OP_SHA256
  unfold UInt8.toNat
  unfold UInt8.val
  unfold Fin.val
  unfold UInt8.instOfNat


  simp [apply]
  unfold Nat.cast NatCast.natCast









  unfold Nat.cast
  unfold OP_SHA256 UInt8.toNat UInt8.val Nat.cast NatCast.natCast instNatCastInt
  simp






  sorry
