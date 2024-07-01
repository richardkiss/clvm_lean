import Mathlib

import Clvm.Atom
import Clvm.Coe
import Clvm.Ints.Basic
import Clvm.Node
import Clvm.Run

import Clvm.Puzzles.Results


def Q1 : Node := Node.pair 1 1


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


-- the first step for many handle_op_xxx functions is to convert a node to a list of nodes with node_to_node_list_terminator
-- let's prove it works right
lemma node_list_terminator_ind { n1 n2 : Node } : node_to_node_list_terminator (Node.pair n1 n2) = ⟨ n1 :: (node_to_node_list_terminator n2).1, (node_to_node_list_terminator n2).2⟩ := by
  rfl


-- for all nodes, the second element of the Except of node_to_node_list_terminator is the rightmost node

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

-- theorem node_to_atoms_only_list_on_one_atom (a: Atom) : node_to_list (Node.pair (Node.atom a) Node.nil) atoms_only = Except.ok [n] := by
--   have h_is_ok : atoms_only (Node.atom a) = Except.ok (Node.atom a) := by rfl


lemma args_to_int_okay_nil_terminated: is_ok (args_to_int n) → (is_nil_terminated_list n) := by
  intro h
  obtain ⟨r, h0⟩ := h
  by_contra h1
  unfold is_nil_terminated_list at h1
  unfold args_to_int at h0
  unfold node_to_list at h0
  rw [node_to_node_list_terminator_rewrite] at h0
  simp at h0
  unfold Atom.length at h1
  have hgt: List.length (rightmost_node n).data > 0 := by
    by_contra hgtn
    have hgt0: List.length (rightmost_node n).data = 0 := by
      linarith
    exact h1 hgt0
  simp [hgt, Except.err] at h0



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
