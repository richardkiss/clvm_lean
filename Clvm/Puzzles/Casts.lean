import Mathlib

import Clvm.Atom
import Clvm.Coe
import Clvm.Ints.Basic
import Clvm.Node
import Clvm.Run

def Q1 : Node := Node.pair 1 1

/-!
This file is currently unused.
-/

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

-- many theorems will use `int_list_to_node_list` so we make sure they work right


def is_nil_terminated_list (n: Node): Prop := (rightmost_node n).length = 0

-- adding something to the beginning of an existing list doesn't change the nil-terminated property
theorem nil_terminated_idempotent { n1 n2 : Node } : is_nil_terminated_list (Node.pair n1 n2) = is_nil_terminated_list n2 := by
  rfl



-- now we can prove that node_to_list works on a list of atoms

-- theorem node_to_atoms_only_list_on_one_atom (a: Atom) : node_to_list (Node.pair (Node.atom a) Node.nil) atoms_only = Except.ok [n] := by
--   have h_is_ok : atoms_only (Node.atom a) = Except.ok (Node.atom a) := by rfl


lemma args_to_int_okay_nil_terminated: is_ok (args_to_int n) → (is_nil_terminated_list n) := by
  intro h
  obtain ⟨r, h0⟩ := h
  by_contra h1
  unfold is_nil_terminated_list at h1
  unfold args_to_int at h0
  unfold node_to_list at h0
  match n with
  | Node.atom ⟨ [], _ ⟩ =>
    rw [Atom.length, List.length_eq_zero] at h1
    simp only [rightmost_node, not_true_eq_false] at h1
  | Node.atom ⟨ head :: tail, lt ⟩ =>
    simp at h0
    sorry
  | Node.pair n1 n2 => sorry



theorem try_int_list_to_node_list_general {zs : List Int} : (int_list_to_node_list zs) = zs.map int_to_atom := by
  induction zs with
  | nil => simp [int_list_to_node_list]
  | cons z0 z_tail ih =>
    unfold int_list_to_node_list List.map
    simp only [List.pure_def, List.bind_eq_bind, List.bind_cons, round_trip_int,
      List.singleton_append, List.cons.injEq, true_and]
    rw [ih]
    rfl

example { z0 z1 : Int } : (int_list_to_node_list [z0, z1]) = [Node.atom (int_to_atom z0), Node.atom (int_to_atom z1)] := by
  simp [try_int_list_to_node_list_general]


-- we use `node_to_list` a lot in handle_op_xxx so let's prove it works right


example : node_to_list Node.nil Except.ok = Except.ok [] := by
  rfl

-- node_to_list works on a single atom
example (n: Node) : node_to_list (Node.pair n Node.nil) Except.ok = Except.ok [n] := by
  rfl

-- node_to_list works on two atoms
example (n1 n2 : Node) : node_to_list (Node.pair n1 (Node.pair n2 Node.nil)) Except.ok = Except.ok [n1, n2] := by
  rfl


def atoms_only (n: Node) : Except (Node × String) Node :=
  match n with
  | Node.atom _ => Except.ok n
  | _ => Except.err n "not an atom"

-- prove `node_to_list` works on nil
example : node_to_list Node.nil atoms_only = Except.ok [] := by
  rfl




-----
-- some more handle_op_xxx opcodes


-- set_option maxHeartbeats 1000000

-- (l n) => 0 or 1 depending on whether n is an atom



-- set_option maxHeartbeats 2400000


--theorem run_sha256_atom { a: Atom } : bruns_to [OP_SHA256.toNat, 1] a (Node.atom (sha256 a)) := by
--  use 2
--  rfl
