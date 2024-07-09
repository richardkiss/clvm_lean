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

import Clvm.HalfBaked



-- we have here several theorems about running programs

def quote_one : Node := h2n! "ff0101"


-- n is a node. We have (a (q . n) 0) => n

theorem run_quote_x_is_x { n: Node } : apply (Node.pair 1 n) Node.nil = Except.ok n := by
  simp [apply]
  unfold apply_node
  simp [small_int_to_atom 1, OP_Q]



-- (q . 1).replace("r", n) => (1 . n)

theorem replace_quote_one_r_with_x_is_quote_x { x: Node } : replace quote_one [Replacement.mk "r" x] = Node.pair 1 x := by
  have hq : quote_one = Node.pair 1 1 := by
    rfl
  rw [hq]
  simp [replace]
  simp [compose_paths, TOP, nodepath_for_char, split_replacements, split_replacements.loop]
  ring_nf
  simp [highest_bit, highest_bit.count_bits]
  ring_nf
  sorry

-- try following paths

-- brun '2 (x . y)' => x
theorem follow_path_2 { x y: Node } : apply 2 (Node.pair x y) = Except.ok x := by
  simp [apply]
  unfold apply_node atom_to_nat
  simp [(small_int_to_atom 2)]
  simp [base_b_be_to_nat_inner]
  simp [node_at]
  unfold node_at_wdepth node_at_wdepth
  rfl


-- brun '3 (x . y)' => y
theorem follow_path_3 { x y: Node } : apply 3 (Node.pair x y) = Except.ok y := by
  simp [apply]
  unfold apply_node atom_to_nat
  simp [(small_int_to_atom 3)]
  simp [base_b_be_to_nat_inner]
  simp [node_at]
  unfold node_at_wdepth node_at_wdepth
  rfl

-- (i (q . 1) 2 3)
def if_example_true : Node := [3, (Node.pair 1 1), 2, 3]

-- brun (i (q . 1) 2 3) (x . y) => x
theorem check_if_true { x y: Node } : apply if_example_true (Node.pair x y) = Except.ok x := by
  simp [apply]
  unfold apply_node
  simp
  simp [if_example_true, node_list_to_node]
  simp [handle_opcode_for_atom, (small_int_to_atom 3), OP_Q, OP_A]
  simp [handle_opcode, handle_op_i]
  simp [map_or_err, apply_node, node_at, atom_to_nat, node_at_wdepth, Except.bind, bind, Except.pure, pure]

  unfold apply_node
  simp [apply_node, node_at, atom_to_nat, node_at_wdepth, Except.bind, bind, Except.pure, pure]
  simp [(small_int_to_atom 3)]
  simp [base_b_be_to_nat_inner]
  unfold node_at_wdepth
  simp
  simp [base_b_be_to_nat_inner, (small_int_to_atom 2), OP_Q, (small_int_to_atom 1)]
  simp [OfNat.ofNat]
  simp [int_to_atom, int_to_twos_comp, twos_comp_to_int, is_msb_set, nat_to_base_b_be, base_b_be_to_nat, nat_to_base_b_be_partial, digit_count, One.one]
  simp [pos_to_twos_comp, pos_to_twos_comp.as_nat, nat_to_base_b_be, nat_to_base_b_be_partial, digit_count, is_msb_set]


def if_example_false : Node := [3, (Node.pair 1 0), 2, 3]

-- brun (i (q . 0) 2 3) (x . y) => y
theorem check_if_false { x y: Node } : apply if_example_false (Node.pair x y) = Except.ok y := by
  simp [apply]
  unfold apply_node
  simp
  simp [if_example_false, node_list_to_node]
  simp [handle_opcode_for_atom, (small_int_to_atom 3), OP_Q, OP_A]
  simp [handle_opcode, handle_op_i]
  simp [map_or_err, apply_node, node_at, atom_to_nat, node_at_wdepth, Except.bind, bind, Except.pure, pure]

  unfold apply_node
  simp [apply_node, node_at, atom_to_nat, node_at_wdepth, Except.bind, bind, Except.pure, pure]
  simp [(small_int_to_atom 3)]
  simp [base_b_be_to_nat_inner]
  unfold node_at_wdepth
  simp
  simp [base_b_be_to_nat_inner, (small_int_to_atom 2), OP_Q, (small_int_to_atom 1)]
  simp [OfNat.ofNat]
  simp [int_to_atom, int_to_twos_comp, twos_comp_to_int, is_msb_set, nat_to_base_b_be, base_b_be_to_nat, nat_to_base_b_be_partial, digit_count, Zero.zero]

-- brun (+) n => 0
theorem run_add_nil_is_0 { n: Node } : apply (Node.pair OP_ADD Node.nil) n = Except.ok 0 := by
  simp [apply]
  unfold apply_node
  simp [OP_ADD]
  simp [(small_int_to_atom 16), OP_Q]

  simp [map_or_err, apply_node, node_at, atom_to_nat, node_at_wdepth, Except.bind, bind, Except.pure, pure, OP_A]
  simp [handle_opcode_for_atom, (small_int_to_atom 3), OP_Q, OP_A]
  simp [handle_opcode, handle_op_add]
  simp [args_to_int, node_to_list, list_except_to_except_list]
  rfl


def cons_example : Node := [4, 2, 3]

-- brun (c 2 3) (x . y) => (x . y)
theorem run_cons { x y: Node } : apply cons_example (Node.pair x y) = Except.ok (Node.pair x y) := by
  simp [apply]
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  simp [cons_example]
  simp [node_list_to_node]
  simp [small_int_to_atom, OP_Q, OP_A]
  simp [node_at, atom_to_nat, node_at_wdepth, base_b_be_to_nat_inner]
  unfold node_at_wdepth
  simp [bind, Except.bind, Except.pure, pure]
  simp [handle_opcode_for_atom, handle_opcode, handle_op_c]



-- brun (f 1) (x . y) => x
theorem run_first { x y: Node } : apply [OP_F, 1] (Node.pair x y) = Except.ok x := by
  simp [apply]
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  simp [node_list_to_node, OP_Q, OP_A]
  simp [small_int_to_atom, OP_F]
  simp [node_at, atom_to_nat, node_at_wdepth, base_b_be_to_nat_inner]
  simp [bind, Except.bind, Except.pure, pure]
  simp [handle_opcode_for_atom, handle_opcode, handle_op_f]

-- brun (r 1) (x . y) => y
theorem run_rest { x y: Node } : apply [OP_R, 1] (Node.pair x y) = Except.ok y := by
  simp [apply]
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  simp [node_list_to_node, OP_Q, OP_A]
  simp [small_int_to_atom, OP_R]
  simp [node_at, atom_to_nat, node_at_wdepth, base_b_be_to_nat_inner]
  simp [bind, Except.bind, Except.pure, pure]
  simp [handle_opcode_for_atom, handle_opcode, handle_op_r]

-- (l n) => 0 or 1 depending on whether n is an atom
theorem op_list { x: Node } : handle_op_l [x] = Except.ok (if is_atom x then Node.nil else Node.one) := by
  cases x <;> rfl

-- brun (l 1) x => 0 or 1
theorem run_list { x: Node } : apply [OP_L, 1] x = Except.ok (if is_atom x then Node.nil else Node.one) := by
  simp [apply]
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  simp [node_list_to_node, OP_Q, OP_A]
  simp [small_int_to_atom, OP_L]
  simp [node_at, atom_to_nat, node_at_wdepth, base_b_be_to_nat_inner]
  unfold node_at_wdepth node_at_wdepth
  simp [bind, Except.bind, Except.pure, pure]
  cases x <;> rfl


def strlen_example : Node := [OP_STRLEN, 1]

#eval apply strlen_example (Atom.to [1, 2, 3])
#eval ((Except.ok (Node.atom [0])): Except (Node × String) Node)

-- brun (strlen 1) x => a.size (where a is the atom for x)
theorem run_strlen { a: Atom } : apply strlen_example (Node.atom a) = (Except.ok (Node.atom a.length) : Except (Node × String) Node) := by
  simp [apply]
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  simp [node_list_to_node, OP_Q, OP_A, strlen_example]
  simp [small_int_to_atom, OP_STRLEN]
  simp [node_at, atom_to_nat, node_at_wdepth, base_b_be_to_nat_inner]
  simp [bind, Except.bind, Except.pure, pure]
  simp [handle_opcode_for_atom, handle_opcode, handle_op_strlen]



-----
-- some more handle_op_xxx opcodes


-- set_option maxHeartbeats 1000000

-- (l n) => 0 or 1 depending on whether n is an atom

theorem op_sha256 { a: Atom } : handle_op_sha256 [Node.atom a] = Except.ok (Node.atom (sha256 a.data)) := by
  rfl



-- set_option maxHeartbeats 2400000



theorem run_sha256_atom { a: Atom } : apply [OP_SHA256, 1] (Node.atom a) = Except.ok (Node.atom (sha256 a)) := by
  simp [apply]
  unfold apply_node map_or_err
  simp
  unfold apply_node map_or_err
  simp [node_list_to_node, OP_Q, OP_A]
  simp [small_int_to_atom, OP_SHA256]
  simp [node_at, atom_to_nat, node_at_wdepth, base_b_be_to_nat_inner]
  simp [handle_opcode_for_atom, handle_opcode, handle_op_sha256]
  simp [bind, Except.bind, Except.pure, pure]
  simp [atom_to_int, int_to_atom, node_to_list, atom_only_cast, node_to_list]
  simp [bind, Except.bind, pure, Except.pure]


theorem run_sha256_two_atoms { a1 a2: Atom } : apply [OP_SHA256, 2, 5] [a1, a2] = Except.ok (Node.atom (sha256 (a1 ++ a2))) := by
  simp [apply]
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  simp [node_list_to_node, OP_Q, OP_A]
  simp [small_int_to_atom, OP_SHA256]
  simp [node_at, atom_to_nat, node_at_wdepth, base_b_be_to_nat_inner]
  simp [bind, Except.bind, Except.pure, pure]
  simp [handle_opcode_for_atom, handle_opcode, handle_op_sha256]
  rfl


theorem run_sha256_three_atoms { a1 a2 a3: Atom } : apply [OP_SHA256, 2, 5, 11] [a1, a2, a3] = Except.ok (Node.atom (sha256 ((a1 ++ a2) ++ a3))) := by
  simp [apply]
  unfold apply_node map_or_err
  simp [node_list_to_node, OP_Q, OP_A]
  simp [small_int_to_atom, OP_SHA256]
  simp [handle_opcode_for_atom, handle_opcode, handle_op_sha256]
  simp [bind, Except.bind, Except.pure, pure]

  unfold map_or_err
  unfold map_or_err
  unfold map_or_err
  simp [bind, Except.bind, Except.pure, pure]

  simp [apply_node]
  simp [node_at, atom_to_nat, node_at_wdepth, base_b_be_to_nat_inner]
  simp [node_to_list, list_except_to_except_list]
  simp [atom_only_cast]
  simp [bind, Except.bind, Except.pure, pure]


theorem op_add_nil : handle_op_add Node.nil = Except.ok 0 := by rfl


theorem op_add_n_numbers { zs : List Int } : handle_op_add zs = Except.ok (Node.atom (int_to_atom (zs.foldl (fun a b => (a + b)) 0))) := by
  unfold handle_op_add
  rw [round_trip_int_cast]


def quote_node (n: Node) : Node := Node.pair Node.one n


def quoted_nodes (ns : List Node) : Node :=
  match ns with
  | [] => Node.nil
  | n :: ns0 =>
      Node.pair (quote_node n) (quoted_nodes ns0)


#eval quoted_nodes [1, 2, 3]



theorem run_add_nil: apply ([OP_ADD, 0]: Node) (0: Node) = Except.ok 0 := by
  rfl


theorem run_add_one_number_1 {z: Int}: apply ([OP_ADD, 1]: Node) (z: Node) = Except.ok (z: Node) := by
  simp [apply]
  unfold apply_node map_or_err
  simp [node_list_to_node, OP_Q, OP_A]
  simp [small_int_to_atom, OP_ADD]
  simp [handle_opcode_for_atom, handle_opcode, handle_op_sha256]

  unfold map_or_err
  simp [bind, Except.bind, Except.pure, pure]

  simp [apply_node]
  simp [node_at, atom_to_nat, node_at_wdepth, base_b_be_to_nat_inner]
  simp [handle_op_add]
  unfold List.foldl
  simp [args_to_int, node_to_list, list_except_to_except_list, atom_to_int_cast, only_atoms]
  simp [bind, Except.bind, Except.pure, pure]


theorem run_add_two_numbers {z1 z2: Int}: apply ([OP_ADD, 2, 5]: Node) ([z1, z2]: Node) = Except.ok ((z1 + z2): Node) := by
  simp [apply]
  unfold apply_node map_or_err
  simp [node_list_to_node, OP_Q, OP_A]
  simp [small_int_to_atom, OP_ADD]
  simp [handle_opcode_for_atom, handle_opcode, handle_op_sha256]

  unfold map_or_err apply_node
  unfold map_or_err apply_node
  simp [bind, Except.bind, Except.pure, pure]

  simp [node_at, atom_to_nat, node_at_wdepth, base_b_be_to_nat_inner]
  simp [handle_op_add]
  unfold List.foldl
  simp [args_to_int, node_to_list, list_except_to_except_list]
  simp [atom_to_int_cast, only_atoms]
  simp [bind, Except.bind, Except.pure, pure]


theorem run_add_two_quoted_numbers {z1 z2: Int}: apply ([(OP_ADD: Node), (Node.pair 1 z1), (Node.pair 1 z2)]: Node) Node.nil = Except.ok ((z1 + z2): Node) := by
  simp [apply]
  unfold apply_node map_or_err
  simp [node_list_to_node, OP_Q, OP_A]
  simp [small_int_to_atom, OP_ADD]
  simp [handle_opcode_for_atom, handle_opcode, handle_op_add]

  unfold map_or_err apply_node
  unfold map_or_err apply_node
  simp [bind, Except.bind, Except.pure, pure]
  simp [small_int_to_atom, OP_Q, OP_A]

  unfold List.foldl
  simp [args_to_int, node_to_list, list_except_to_except_list]
  simp [atom_to_int_cast, only_atoms]
  simp [bind, Except.bind, Except.pure, pure]


#print axioms run_add_two_quoted_numbers


theorem run_mul_two_quoted_numbers {z1 z2: Int}: apply ([((OP_MUL): Node), (Node.pair 1 z1), (Node.pair 1 z2)]: Node) Node.nil = Except.ok ((z1 * z2): Node) := by
  simp [apply]
  unfold apply_node map_or_err
  simp [node_list_to_node, OP_Q, OP_A]
  simp [small_int_to_atom, OP_MUL]
  simp [handle_opcode_for_atom, handle_opcode, handle_op_mul]

  unfold map_or_err apply_node
  unfold map_or_err apply_node
  simp [bind, Except.bind, Except.pure, pure]
  simp [small_int_to_atom, OP_Q, OP_A]

  unfold List.foldl
  simp [args_to_int, node_to_list, list_except_to_except_list]
  simp [atom_to_int_cast, only_atoms]
  simp [bind, Except.bind, Except.pure, pure]


lemma quoted_node_is_ok (args: Node): node_applies (Node.pair OP_Q n) args := by
  use 1
  simp [node_applies, is_ok]
  use n

  unfold apply_node map_or_err
  simp [OP_Q, OP_A]
  simp [small_int_to_atom]




def quoted_atoms (as: List Atom) : Node :=
  quoted_nodes (as.map (fun a => Node.atom a))


lemma map_err_quoted_atoms_is_ok (as: List Atom) {h_d: d ≠ 0} {env: Node} : map_or_err (apply_node d · env) (quoted_atoms as) = Except.ok as := by
  induction as with
  | nil =>
    unfold map_or_err
    simp [quoted_atoms, quoted_nodes, Except.bind, bind, Except.pure, pure, node_list_to_node]

  | cons head tail ih =>
    unfold map_or_err
    unfold quoted_atoms quoted_nodes List.map
    simp
    unfold quoted_atoms at ih
    rw [ih]
    simp [Except.bind, bind]
    unfold apply_node
    simp [h_d, quote_node, OP_Q, pure, Except.pure, node_list_to_node]


lemma args_to_int_atoms_ok {zs: List Int} : args_to_int (node_list_to_node (List.map Node.atom (zs.bind fun a => [int_to_atom a]))) = Except.ok zs := by
  simp [args_to_int]
  induction zs with
  | nil => simp [List.map, node_list_to_node, node_to_list]
  | cons head tail ih =>
    simp [List.bind] at ih
    simp [List.map, node_list_to_node, node_to_list]
    rw [ih]
    simp [bind, Except.bind]
    simp [atom_to_int_cast, only_atoms]
    simp [pure, Except.pure]


theorem run_add_n_numbers { zs: List Int } : bruns_to (Node.pair OP_ADD (quoted_atoms zs)) 0 (int_to_atom (zs.foldl (fun (a b: Int) => a + b) 0)) := by
  use 2
  simp [OP_ADD]
  simp [small_int_to_atom]
  unfold apply_node
  simp [OP_Q, OP_A, handle_opcode_for_atom, handle_opcode]
  unfold handle_op_add

  simp [map_err_quoted_atoms_is_ok]
  simp [bind, Except.bind]
  simp [args_to_int_atoms_ok]




---- unfinished proofs go after this line


lemma concat_of_quoted_atoms_is_ok (as: List Atom): node_applies (Node.pair (Node.atom [OP_CONCAT]) (quoted_atoms as)) 0 := by
  use 2
  unfold apply_node
  simp [atom_cast, max_255, OP_CONCAT, OP_Q, OP_A]
  simp [handle_opcode_for_atom, handle_opcode]

  simp [map_err_quoted_atoms_is_ok]
  simp [Except.bind, bind, Except.pure, pure]

  induction as with
  | nil =>
    simp [handle_op_concat]
    simp [node_to_list, list_except_to_except_list]
    simp [is_ok]
  | cons head tail ih =>

    obtain ⟨n_ih, h_ih⟩ := ih

    have h_is_ok: is_ok (node_to_list (node_list_to_node (List.map Node.atom tail)) atom_only_cast) := by
      by_contra h
      obtain ⟨n, hn⟩ := not_ok h
      simp [handle_op_concat] at h_ih
      rw [hn] at h_ih
      simp at h_ih
      simp [Except.err] at h_ih

    simp [handle_op_concat, List.map, node_list_to_node, node_to_list]

    obtain ⟨ n0, hn0 ⟩ := h_is_ok
    simp [hn0, bind, Except.bind, atom_only_cast, pure, Except.pure, is_ok]



theorem run_concat_atoms { nat_lists: List (List Nat) } : bruns_to (Node.pair OP_CONCAT (quoted_atoms nat_lists)) env (Node.atom (Atom.to (nat_lists.foldl (fun (a b: List Nat) => a ++ b) []))) := by
  use 2
  simp [OP_CONCAT]
  simp [small_int_to_atom]
  unfold apply_node
  simp [OP_Q, OP_A, handle_opcode_for_atom, handle_opcode]
  unfold handle_op_concat

  simp [map_err_quoted_atoms_is_ok]
  simp [bind, Except.bind]
  induction nat_lists with
  | nil => simp [node_list_to_node, node_to_list, Atom.to, atom_cast]
  | cons head tail ih =>

    have h_is_ok: is_ok (node_to_list (node_list_to_node (List.map Node.atom (tail.bind fun a => [atom_cast a]))) atom_only_cast) := by
      by_contra h
      obtain ⟨n, hn⟩ := not_ok h
      simp [handle_op_concat] at ih
      rw [hn] at ih
      simp at ih
      simp [Except.err] at ih

    obtain ⟨ n0, hn0 ⟩ := h_is_ok
    simp [hn0, bind, Except.bind, atom_only_cast, pure, Except.pure, is_ok]
    rw [hn0] at ih
    simp at ih

    simp [node_list_to_node, node_to_list, Atom.to, atom_cast]

    sorry
