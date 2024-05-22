import Mathlib

import Init.Coe
import Init.Data
import Init.Data.ByteArray
import Init.Data.Fin
import Init.Data.Nat
import Init.Data.Nat.Bitwise

import Init.Data.UInt
import Init.Prelude
import Init.Tactics

import Clvm.Atom
import Clvm.Ints.Basic
import Clvm.Puzzles.Apply
import Clvm.Puzzles.Casts
import Clvm.Puzzles.Results
import Clvm.Run

import Std.Classes.Cast
import Std.Data.UInt



-- we have here several theorems about running programs

def quote_one : Node := h2n "ff0101"


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
theorem run_add_nil_is_0 { n: Node } : apply (Node.pair OP_ADD Node.nil) n = Result.ok 0 := by
  rfl


def cons_example : Node := [4, 2, 3]

-- brun (c 2 3) (x . y) => (x . y)
theorem run_cons { x y: Node } : apply cons_example (Node.pair x y) = Result.ok (Node.pair x y) := by
  rfl

-- brun (f 1) (x . y) => x
theorem run_first { x y: Node } : apply [OP_F, 1] (Node.pair x y) = Result.ok x := by
  rfl

-- brun (r 1) (x . y) => y
theorem run_rest { x y: Node } : apply [OP_R, 1] (Node.pair x y) = Result.ok y := by
  rfl


-- (l n) => 0 or 1 depending on whether n is an atom
theorem op_list { x: Node } : handle_op_l [x] = Result.ok (if is_atom x then Node.nil else Node.one) := by
  cases x <;> rfl

-- brun (l 1) x => 0 or 1
theorem run_list { x: Node } : apply [OP_L, 1] x = Result.ok (if is_atom x then Node.nil else Node.one) := by
  cases x <;> rfl


def strlen_example : Node := [OP_STRLEN, 1]

#eval apply strlen_example (Atom.to [1, 2, 3])
#eval ((Result.ok (Node.atom [0])): Result Node Node)

-- brun (strlen 1) x => a.size (where a is the atom for x)
theorem run_strlen { a: Atom } : apply strlen_example (Node.atom a) = (Result.ok (Node.atom a.length) : Result Node Node) := by
  rfl


-----
-- some more handle_op_xxx opcodes


-- set_option maxHeartbeats 1000000

-- (l n) => 0 or 1 depending on whether n is an atom

theorem op_sha256 { a: Atom } : handle_op_sha256 [Node.atom a] = Result.ok (Node.atom (sha256 a.data)) := by
  rfl


example: Int.ofNat (11: UInt8).val.val = (11: Int) := by simp


example: int_to_atom (11: UInt8).toNat = (11: Int) := by simp



example : (int_to_atom (UInt8.toNat OP_SHA256)) = [11] := by
  unfold OP_SHA256
  unfold UInt8.toNat
  unfold UInt8.val
  unfold Fin.val
  conv_lhs => simp


example : Int.ofNat (11: UInt8).toNat = (11: Int) := by
  simp

example: Int.ofNat (11: UInt8).val.val = (11: Int) := by simp



-- set_option maxHeartbeats 2400000


/-
theorem run_sha256_atom { a: Atom } : apply [OP_SHA256, 1] a = Result.ok (Node.atom (sha256 a)) := by
  rfl
-/


theorem run_sha256_two_atoms { a1 a2: Atom } : apply [OP_SHA256, 2, 5] [a1, a2] = Result.ok (Node.atom (sha256 (a1 ++ a2))) := by
  rfl


theorem run_sha256_three_atoms { a1 a2 a3: Atom } : apply [OP_SHA256, 2, 5, 11] [a1, a2, a3] = Result.ok (Node.atom (sha256 ((a1 ++ a2) ++ a3))) := by
  rfl


theorem op_add_nil : handle_op_add Node.nil = Result.ok 0 := by rfl


theorem op_add_n_numbers { zs : List Int } : handle_op_add zs = Result.ok (Node.atom (int_to_atom (zs.foldl (fun a b => (a + b)) 0))) := by
  unfold handle_op_add
  rw [round_trip_int_cast]


def quote_node (n: Node) : Node := Node.pair Node.one n


def quoted_nodes (ns : List Node) : Node :=
  match ns with
  | [] => Node.nil
  | n :: ns0 =>
      Node.pair (quote_node n) (quoted_nodes ns0)


#eval quoted_nodes [1, 2, 3]



theorem run_add_nil: apply ([OP_ADD, 0]: Node) (0: Node) = Result.ok 0 := by
  rfl


theorem run_add_one_number_1 {z: Int}: apply ([OP_ADD, 1]: Node) (z: Node) = Result.ok (z: Node) := by
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

  simp [handle_opcode_for_atom, handle_opcode]

  unfold handle_op_add
  simp [List.foldl, args_to_int, node_to_list, node_to_node_list_terminator, list_result_to_result_list]


theorem run_add_two_numbers {z1 z2: Int}: apply ([OP_ADD, 2, 5]: Node) ([z1, z2]: Node) = Result.ok ((z1 + z2): Node) := by
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
  simp [handle_opcode_for_atom, handle_opcode]
  simp [handle_op_add]

  unfold List.foldl

  simp [args_to_int, node_to_list, node_to_node_list_terminator, list_result_to_result_list]


theorem run_add_two_quoted_numbers {z1 z2: Int}: apply ([(OP_ADD: Node), (Node.pair 1 z1), (Node.pair 1 z2)]: Node) Node.nil = Result.ok ((z1 + z2): Node) := by
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

  simp [handle_opcode_for_atom, handle_opcode]
  simp [handle_op_add]
  simp [args_to_int, node_to_list, node_to_node_list_terminator, list_result_to_result_list, List.length]


#print axioms run_add_two_quoted_numbers


theorem run_mul_two_quoted_numbers {z1 z2: Int}: apply ([((OP_MUL): Node), (Node.pair 1 z1), (Node.pair 1 z2)]: Node) Node.nil = Result.ok ((z1 * z2): Node) := by
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

  simp [handle_opcode_for_atom, handle_opcode]
  simp [handle_op_mul]
  simp [args_to_int, node_to_list, node_to_node_list_terminator, list_result_to_result_list, List.length]



lemma quoted_node_is_ok (args: Node): node_applies (Node.pair OP_Q n) args := by
  use 1
  simp [node_applies, is_ok]
  use n
  rfl



---- unfinished proofs go after this line


def quoted_atoms (as: List Atom) : Node :=
  quoted_nodes (as.map (fun a => Node.atom a))


/-
lemma concat_of_quoted_atoms_is_okay (as: List Atom): node_applies (Node.pair (Node.atom [OP_CONCAT]) (quoted_atoms as)) 0 := by
  use 2
  unfold OP_CONCAT
  simp [atom_cast, max_255]
  simp [node_applies, is_ok]
  -- obtain ⟨r, h0⟩ := map_or_err_is_ok ns 0
  simp [apply_node]
  simp [Atom.length, OP_Q, OP_A, getElem!]
  induction as with
  | nil =>
    unfold map_or_err
    unfold quoted_atoms quoted_nodes
    simp
    simp [handle_opcode, handle_op_concat]
    simp [node_to_list, List.length]
    rw [node_to_node_list_terminator_rewrite]
    simp [alt_node_to_node_list_terminator_without_terminator, rightmost_node]
    simp [list_result_to_result_list]
  | cons head tail ih =>
    obtain ⟨r, h0⟩ := ih
    --use (Node.atom (head.data ++ r))
    unfold quoted_atoms
    simp
    unfold quoted_nodes quote_node List.map -- atom_cast OP_Q max_255
    simp
    simp [int_to_atom, atom_to_int]
    simp [twos_comp_to_int, int_to_twos_comp, is_msb_set, base_b_be_to_nat, base_b_be_to_nat_inner]
    simp [pos_to_twos_comp, pos_to_twos_comp.as_nat, nat_to_base_b_be, nat_to_base_b_be_partial, digit_count]
    simp [is_msb_set]
    unfold map_or_err
    simp [apply_node]
    simp [Atom.length, OP_Q, OP_A, getElem!]
    unfold quoted_atoms at h0
    --rw [h0]
    sorry

theorem run_add_n_numbers { zs: List Int } : program = (Node.pair ([OP_ADD] : Atom) (quoted_nodes zs)) → apply program 0 =
    Result.ok (Node.atom (int_to_atom (zs.foldl (fun (a b: Int) => a + b) 0))) := by

  unfold OP_ADD
  simp [atom_cast, max_255]

  intro hp
  induction zs with
  | nil =>
    simp [hp]
    rfl

  | cons head tail ih =>
    simp [hp]
    unfold apply apply_node
    simp
    simp [Atom.length, OP_Q, OP_A, getElem!]
    simp [List.length, atom_to_int, twos_comp_to_int, is_msb_set]


    rw [map_or_err_to_quoted_nodes]
    unfold node_list_to_node
    simp
    simp [pure, List.ret]
    simp [handle_opcode]
    simp [handle_op_add]
    simp [args_to_int, node_to_list]
    rw [node_to_node_list_terminator_rewrite]
    simp [alt_node_to_node_list_terminator_without_terminator, rightmost_node]










    simp [map_or_err, apply_node, node_at, atom_to_nat, node_at_wdepth, list_nat_to_nat]
    simp [hp]
    simp [Atom.length, OP_Q, OP_A, getElem!]
    unfold map_or_err
    simp [handle_opcode]



    simp [handle_opcode]
    simp [handle_op_add]
    rfl






    simp [int_to_atom, nat_to_atom, List.map, max_255, List.foldr, List.foldl, List.length, nat_to_atom.inner_func]

    unfold getElem instGetElemArrayNatLtInstLTNatSize Array.size Array.get List.get
    simp

    simp







    simp [apply, apply_node, Node.nil]
    simp [atom_to_nat, node_at, node_at_wdepth, list_nat_to_nat]
    simp





  | cons head tail ih =>
    sorry
-/
