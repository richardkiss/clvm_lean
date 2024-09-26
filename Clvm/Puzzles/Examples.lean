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
import Clvm.Puzzles.Apply
import Clvm.Run
import Clvm.SmallIntToAtom




-- we have here several theorems about running programs

def quote_one : Node := h2n! "ff0101"




-- n is a node. We have (a (q . n) 0) => n

theorem run_quote_x_is_x { n: Node } : bruns_to (Node.pair 1 n) Node.nil n := by
  simp only [bruns_to, Node.nil]
  use 1
  unfold apply_node
  simp [small_int_to_atom 1, OP_Q]



-- (q . 1).replace("r", n) => (1 . n)

theorem replace_quote_one_r_with_x_is_quote_x { x: Node } : replace quote_one [Replacement.mk "r" x] = Node.pair 1 x := by
  have hq : quote_one = Node.pair 1 1 := by
    rfl
  rw [hq]
  simp only [nodepath_for_string, ↓Char.isValue, List.map_cons, List.map_nil, List.foldl_cons,
    List.foldl_nil, replace, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
    List.isEmpty_eq_true]
  simp only [split_replacements, split_replacements.loop, compose_paths, TOP, one_ne_zero,
    nodepath_for_char, ↓Char.isValue, Char.reduceEq, ↓reduceIte, OfNat.ofNat_ne_zero, or_self,
    List.isEmpty_eq_true, ↓dreduceIte]
  simp only [highest_bit, highest_bit.count_bits, zero_lt_one, ↓reduceDIte, Nat.reduceDiv, zero_add,
    lt_self_iff_false, Nat.reduceShiftLeft, Nat.ofNat_pos, Nat.div_self, mul_one, Nat.xor_self,
    add_zero, OfNat.ofNat_ne_one, ↓reduceIte, Nat.reduceMod, one_ne_zero, List.isEmpty_nil,
    List.isEmpty_cons, Bool.false_eq_true, Node.pair.injEq, true_and]
  simp [split_replacements.loop]


-- try following paths

-- brun '2 (x . y)' => x
theorem follow_path_2 { x y: Node } : bruns_to 2 (Node.pair x y) x := by
  rw [bruns_to]
  use 1
  unfold apply_node atom_to_nat
  simp only [one_ne_zero, ↓reduceIte, Int.ofNat_eq_coe, Nat.cast_ofNat]
  simp only [gt_iff_lt, Nat.ofNat_pos, Int.reduceLT, small_int_to_atom, Int.reduceAbs]
  simp only [base_b_be_to_nat_inner, List.length_nil, pow_zero, mul_one, zero_add]
  simp only [node_at, Nat.reduceAdd]
  unfold node_at_wdepth node_at_wdepth
  simp


-- brun '3 (x . y)' => y
theorem follow_path_3 { x y: Node } : bruns_to 3 (Node.pair x y) y := by
  rw [bruns_to]
  use 1
  unfold apply_node atom_to_nat
  simp only [one_ne_zero, ↓reduceIte, Int.ofNat_eq_coe, Nat.cast_ofNat]
  rw [(small_int_to_atom 3)]
  rw [base_b_be_to_nat_inner]
  rw [node_at]
  unfold node_at_wdepth node_at_wdepth
  rfl
  simp only [gt_iff_lt, Nat.ofNat_pos]
  simp only [Int.reduceLT]

-- (i (q . 1) 2 3)
def if_example_true : Node := [3, (Node.pair 1 1), 2, 3]

-- brun (i (q . 1) 2 3) (x . y) => x
theorem check_if_true { x y: Node } : bruns_to if_example_true (Node.pair x y) x := by
  rw [bruns_to]
  use 2
  unfold apply_node
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.add_one_sub_one]
  simp only [if_example_true, node_list_to_node, Node.nil, Int.ofNat_eq_coe, Nat.cast_ofNat]
  simp only [gt_iff_lt, Nat.ofNat_pos, Int.reduceLT, (small_int_to_atom 3), Int.reduceAbs, OP_Q,
    List.cons.injEq, OfNat.ofNat_ne_one, and_true, ↓reduceIte, OP_A, Nat.succ_ne_self,
    handle_opcode_for_atom]
  simp only [handle_opcode, handle_op_i]
  simp only [bind, Except.bind, map_or_err, Node.nil, pure, Except.pure]

  unfold apply_node
  simp only [one_ne_zero, ↓reduceIte, node_at, atom_to_nat, Int.ofNat_eq_coe, Nat.cast_ofNat,
    node_at_wdepth, AddLeftCancelMonoid.add_eq_zero, and_false, Node.nil, add_tsub_cancel_right,
    Nat.cast_one, bind, Except.bind, le_refl, tsub_eq_zero_of_le]
  simp only [gt_iff_lt, Nat.ofNat_pos, Int.reduceLT, (small_int_to_atom 3), Int.reduceAbs]
  simp only [base_b_be_to_nat_inner, List.length_nil, pow_zero, mul_one, zero_add, Nat.reduceLT,
    ↓reduceIte, Nat.reduceDiv, Nat.reduceMod, one_ne_zero]
  unfold node_at_wdepth
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.one_lt_ofNat, one_ne_zero, Node.nil]
  simp only [gt_iff_lt, Nat.ofNat_pos, Int.reduceLT, (small_int_to_atom 2), Int.reduceAbs,
    base_b_be_to_nat_inner, List.length_nil, pow_zero, mul_one, zero_add, lt_self_iff_false,
    ↓reduceIte, OfNat.ofNat_ne_zero, Nat.div_self, Nat.one_lt_ofNat, one_ne_zero, Nat.mod_self,
    zero_lt_one, (small_int_to_atom 1), isUnit_one, Int.natAbs_of_isUnit, OP_Q]
  simp only [OfNat.ofNat, Int.ofNat_eq_coe, Nat.cast_one]
  simp only [int_to_atom, int_to_twos_comp, One.one, one_ne_zero, ↓reduceIte, Int.reduceLT,
    isUnit_one, Int.natAbs_of_isUnit]
  simp only [pos_to_twos_comp, is_msb_set, pos_to_twos_comp.as_nat, nat_to_base_b_be, digit_count,
    one_ne_zero, ↓reduceIte, Nat.log_one_right, add_zero, le_refl, tsub_eq_zero_of_le,
    nat_to_base_b_be_partial, Nat.one_and_eq_mod_two, Nat.reduceMod, OfNat.zero_ne_ofNat,
    decide_False, Bool.false_eq_true]


def if_example_false : Node := [3, (Node.pair 1 0), 2, 3]

-- brun (i (q . 0) 2 3) (x . y) => y
theorem check_if_false { x y: Node } : bruns_to if_example_false (Node.pair x y) y := by
  rw [bruns_to]
  use 2
  unfold apply_node
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.add_one_sub_one]
  simp only [if_example_false, node_list_to_node, Node.nil, Int.ofNat_eq_coe, Nat.cast_ofNat]
  simp only [gt_iff_lt, Nat.ofNat_pos, Int.reduceLT, (small_int_to_atom 3), Int.reduceAbs, OP_Q,
    List.cons.injEq, OfNat.ofNat_ne_one, and_true, ↓reduceIte, OP_A, Nat.succ_ne_self,
    handle_opcode_for_atom]
  simp only [handle_opcode, handle_op_i]
  simp only [bind, Except.bind, map_or_err, Node.nil, pure, Except.pure]

  unfold apply_node
  simp only [one_ne_zero, ↓reduceIte, node_at, atom_to_nat, Int.ofNat_eq_coe, Nat.cast_ofNat,
    node_at_wdepth, AddLeftCancelMonoid.add_eq_zero, and_false, Node.nil, add_tsub_cancel_right,
    Nat.cast_one, bind, Except.bind, le_refl, tsub_eq_zero_of_le]
  simp only [gt_iff_lt, Nat.ofNat_pos, Int.reduceLT, (small_int_to_atom 3), Int.reduceAbs]
  simp only [base_b_be_to_nat_inner, List.length_nil, pow_zero, mul_one, zero_add, Nat.reduceLT,
    ↓reduceIte, Nat.reduceDiv, Nat.reduceMod, one_ne_zero]
  unfold node_at_wdepth
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.one_lt_ofNat, one_ne_zero, Node.nil]
  simp only [gt_iff_lt, Nat.ofNat_pos, Int.reduceLT, (small_int_to_atom 2), Int.reduceAbs,
    base_b_be_to_nat_inner, List.length_nil, pow_zero, mul_one, zero_add, lt_self_iff_false,
    ↓reduceIte, OfNat.ofNat_ne_zero, Nat.div_self, Nat.one_lt_ofNat, one_ne_zero, Nat.mod_self,
    zero_lt_one, (small_int_to_atom 1), isUnit_one, Int.natAbs_of_isUnit, OP_Q]
  simp only [OfNat.ofNat, Int.ofNat_eq_coe, CharP.cast_eq_zero]
  simp only [int_to_atom, int_to_twos_comp, Zero.zero, ↓reduceIte]

-- brun (+) n => 0
theorem run_add_nil_is_0 { n: Node } : bruns_to (Node.pair OP_ADD Node.nil) n 0 := by
  rw [bruns_to]
  use 1
  unfold apply_node
  simp only [OP_ADD, Function.comp_apply, Int.ofNat_eq_coe, Nat.cast_ofNat, round_trip_int]
  simp only [Nat.ofNat_pos, Int.reduceLT, (small_int_to_atom 16)]
  rfl


def cons_example : Node := [4, 2, 3]

-- brun (c 2 3) (x . y) => (x . y)
theorem run_cons { x y: Node } : bruns_to cons_example (Node.pair x y) (Node.pair x y) := by
  rw [bruns_to]
  use 2

  simp only [apply_node,  map_or_err, OfNat.ofNat_ne_zero, cons_example, Function.comp_apply, node_list_to_node,
    Int.ofNat_eq_coe, Nat.cast_ofNat, gt_iff_lt, Nat.ofNat_pos, Int.reduceLT, small_int_to_atom,
    Int.reduceAbs, Node.nil, OP_Q, List.cons.injEq, OfNat.ofNat_ne_one, and_true,
    Nat.add_one_sub_one, one_ne_zero, node_at, atom_to_nat, base_b_be_to_nat_inner, List.length_nil,
    pow_zero, mul_one, zero_add, Nat.reduceAdd, node_at_wdepth, Nat.reduceLT, Nat.reduceDiv,
    Nat.reduceMod, lt_self_iff_false, Nat.div_self, Nat.mod_self, bind_assoc, pure_bind, OP_A,
    Nat.reduceEqDiff, ↓reduceIte]

  unfold node_at_wdepth

  simp only [Node.nil, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
    add_tsub_cancel_right]
  simp only [Node.nil, bind, Except.bind, pure, Except.pure, AddLeftCancelMonoid.add_eq_zero,
    one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right]
  simp only [handle_opcode_for_atom, handle_opcode, handle_op_c]
  simp only [Nat.one_lt_ofNat]


-- brun (f 1) (x . y) => x
theorem run_first { x y: Node } : bruns_to [OP_F, 1] (Node.pair x y) x := by
  rw [bruns_to]
  use 2
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Function.comp_apply, node_list_to_node,
    Int.ofNat_eq_coe, Nat.cast_one, Node.nil, OP_Q, Nat.add_one_sub_one, one_ne_zero, OP_A, le_refl,
    tsub_eq_zero_of_le, bind_assoc, pure_bind]
  simp only [OP_F, Nat.cast_ofNat, gt_iff_lt, Nat.ofNat_pos, Int.reduceLT, small_int_to_atom,
    Int.reduceAbs, List.cons.injEq, OfNat.ofNat_ne_one, and_true, ↓reduceIte, zero_lt_one,
    Nat.one_lt_ofNat, isUnit_one, Int.natAbs_of_isUnit, Nat.reduceEqDiff]
  simp only [node_at, atom_to_nat, base_b_be_to_nat_inner, List.length_nil, pow_zero, mul_one,
    zero_add, Nat.reduceAdd, node_at_wdepth, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.one_lt_ofNat,
    one_ne_zero]
  simp only [bind, Except.bind]
  simp only [handle_opcode_for_atom, handle_opcode, handle_op_f]

-- brun (r 1) (x . y) => y
theorem run_rest { x y: Node } : bruns_to [OP_R, 1] (Node.pair x y) y := by
  rw [bruns_to]
  use 2
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Function.comp_apply, node_list_to_node,
    Int.ofNat_eq_coe, Nat.cast_one, Node.nil, OP_Q, Nat.add_one_sub_one, one_ne_zero, OP_A, le_refl,
    tsub_eq_zero_of_le, bind_assoc, pure_bind]
  simp only [OP_R, Nat.cast_ofNat, gt_iff_lt, Nat.ofNat_pos, Int.reduceLT, small_int_to_atom,
    Int.reduceAbs, List.cons.injEq, OfNat.ofNat_ne_one, and_true, ↓reduceIte, zero_lt_one,
    Nat.one_lt_ofNat, isUnit_one, Int.natAbs_of_isUnit, Nat.reduceEqDiff]
  simp only [node_at, atom_to_nat, base_b_be_to_nat_inner, List.length_nil, pow_zero, mul_one,
    zero_add, Nat.reduceAdd, node_at_wdepth, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.one_lt_ofNat,
    one_ne_zero]
  simp only [bind, Except.bind]
  simp only [handle_opcode_for_atom, handle_opcode, handle_op_r]

-- (l n) => 0 or 1 depending on whether n is an atom
theorem op_list { x: Node } : handle_op_l [x] = Except.ok (if is_atom x then Node.nil else Node.one) := by
  cases x <;> rfl

-- brun (l 1) x => 0 or 1
theorem run_list { x: Node } : bruns_to [OP_L, 1] x (if is_atom x then Node.nil else Node.one) := by
  rw [bruns_to]
  use 2
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  simp only [Function.comp_apply, node_list_to_node, Int.ofNat_eq_coe, Nat.cast_one, Node.nil, OP_Q, OP_A]
  simp only [↓reduceIte, bind_assoc, pure_bind, Node.one]
  simp only [OP_L, Nat.cast_ofNat, Nat.ofNat_pos, Int.reduceLT, small_int_to_atom, zero_lt_one, Nat.reduceEqDiff]
  simp only [node_at, atom_to_nat, base_b_be_to_nat_inner, mul_one]
  simp only [Int.reduceAbs, List.cons.injEq, OfNat.ofNat_ne_one, and_true, ↓reduceIte, isUnit_one,
    Int.natAbs_of_isUnit, List.length_nil, pow_zero, mul_one, zero_add, Nat.reduceAdd,
    Nat.reduceEqDiff]
  unfold node_at_wdepth node_at_wdepth
  simp only [bind, Except.bind, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.one_lt_ofNat, one_ne_zero]
  cases x <;> rfl


def strlen_example : Node := [OP_STRLEN, 1]

#eval! apply strlen_example (Atom.to [1, 2, 3])
#eval ((Except.ok (Node.atom [0])): Except (Node × String) Node)

-- brun (strlen 1) x => a.size (where a is the atom for x)
theorem run_strlen { a: Atom } : bruns_to strlen_example (Node.atom a) (Node.atom a.length)  := by
  rw [bruns_to]
  use 2
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, strlen_example, Function.comp_apply,
    node_list_to_node, Int.ofNat_eq_coe, Nat.cast_one, Node.nil, OP_Q, Nat.add_one_sub_one,
    one_ne_zero, OP_A, le_refl, tsub_eq_zero_of_le, bind_assoc, pure_bind]
  simp only [OP_STRLEN, Nat.cast_ofNat, gt_iff_lt, Nat.ofNat_pos, Int.reduceLT, small_int_to_atom,
    Int.reduceAbs, List.cons.injEq, OfNat.ofNat_ne_one, and_true, ↓reduceIte, zero_lt_one,
    Nat.one_lt_ofNat, isUnit_one, Int.natAbs_of_isUnit, Nat.reduceEqDiff]
  simp only [node_at, atom_to_nat, base_b_be_to_nat_inner, List.length_nil, pow_zero, mul_one,
    zero_add, Nat.reduceAdd, node_at_wdepth, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.one_lt_ofNat,
    one_ne_zero]
  simp only [bind, Except.bind]
  simp only [handle_opcode_for_atom, handle_opcode, handle_op_strlen]


-----
-- some more handle_op_xxx opcodes


-- set_option maxHeartbeats 1000000

-- (l n) => 0 or 1 depending on whether n is an atom

theorem op_sha256 { a: Atom } : handle_op_sha256 [Node.atom a] = Except.ok (Node.atom (sha256 a.data)) := by
  rfl



-- set_option maxHeartbeats 2400000



theorem run_sha256_atom { a: Atom } : bruns_to [OP_SHA256, 1] (Node.atom a) (Node.atom (sha256 a)) := by
  rw [bruns_to]
  use 2
  unfold apply_node map_or_err
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Node.nil, Nat.add_one_sub_one]
  unfold apply_node map_or_err
  simp [node_list_to_node, OP_Q, OP_A]
  simp [small_int_to_atom, OP_SHA256]
  simp [node_at, atom_to_nat, node_at_wdepth, base_b_be_to_nat_inner]
  simp [handle_opcode_for_atom, handle_opcode, handle_op_sha256]
  simp [bind, Except.bind, Except.pure, pure]
  rfl


theorem run_sha256_two_atoms { a1 a2: Atom } : bruns_to [OP_SHA256, 2, 5] [a1, a2] (Node.atom (sha256 (a1 ++ a2))) := by
  rw [bruns_to]
  use 2
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  unfold apply_node map_or_err
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Function.comp_apply, node_list_to_node,
    Int.ofNat_eq_coe, Nat.cast_ofNat, Node.nil, OP_Q, Nat.add_one_sub_one, one_ne_zero, bind_assoc,
    pure_bind, OP_A, le_refl, tsub_eq_zero_of_le]
  simp only [OP_SHA256, Nat.cast_ofNat, gt_iff_lt, Nat.ofNat_pos, Int.reduceLT, small_int_to_atom,
    Int.reduceAbs, List.cons.injEq, OfNat.ofNat_ne_one, and_true, ↓reduceIte, Nat.reduceEqDiff]
  simp only [node_at, atom_to_nat, base_b_be_to_nat_inner, List.length_nil, pow_zero, mul_one,
    zero_add, Nat.reduceAdd, node_at_wdepth, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.reduceLT,
    Nat.add_one_sub_one, Nat.reduceDiv, Nat.reduceMod, one_ne_zero, lt_self_iff_false,
    Nat.ofNat_pos, Nat.div_self, Nat.mod_self, Nat.one_lt_ofNat]
  simp only [bind, Except.bind]
  simp only [handle_opcode_for_atom, handle_opcode, handle_op_sha256, List.pure_def,
    List.bind_eq_bind]
  rfl


theorem run_sha256_three_atoms { a1 a2 a3: Atom } : bruns_to [OP_SHA256, 2, 5, 11] [a1, a2, a3] (Node.atom (sha256 ((a1 ++ a2) ++ a3))) := by
  rw [bruns_to]
  use 2
  unfold apply_node map_or_err
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Function.comp_apply, node_list_to_node,
    Int.ofNat_eq_coe, Nat.cast_ofNat, Node.nil, OP_Q, Nat.add_one_sub_one, OP_A, bind_assoc,
    pure_bind, List.append_assoc]
  simp only [OP_SHA256, Nat.cast_ofNat, gt_iff_lt, Nat.ofNat_pos, Int.reduceLT, small_int_to_atom,
    Int.reduceAbs, List.cons.injEq, OfNat.ofNat_ne_one, and_true, ↓reduceIte, Nat.reduceEqDiff]
  simp only [handle_opcode_for_atom, handle_opcode, handle_op_sha256, List.pure_def,
    List.bind_eq_bind]
  simp only [bind, Except.bind]

  unfold map_or_err
  unfold map_or_err
  unfold map_or_err
  simp only [bind, Except.bind, pure, Except.pure, Node.nil]

  simp only [apply_node, one_ne_zero, ↓reduceIte]
  simp only [node_at, atom_to_nat, base_b_be_to_nat_inner, List.length_nil, pow_zero, mul_one,
    zero_add, Nat.reduceAdd, node_at_wdepth, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.reduceLT,
    Nat.add_one_sub_one, Nat.reduceDiv, Nat.reduceMod, one_ne_zero, lt_self_iff_false,
    Nat.ofNat_pos, Nat.div_self, Nat.mod_self, Nat.one_lt_ofNat]
  simp only [node_to_list, bind_assoc, pure_bind]
  simp only [atom_only_cast]
  simp only [bind, Except.bind, pure, Except.pure, List.bind_cons, List.bind_nil,
    List.singleton_append, List.foldl_cons, List.nil_append, List.append_assoc, List.foldl_nil]


theorem op_add_nil : handle_op_add Node.nil = Except.ok 0 := by rfl


theorem round_trip_int_list (zs: List Int) : args_to_int ((node_list_to_node ∘ int_list_to_node_list) zs) = Except.ok zs := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    simp only [Function.comp_apply, int_list_to_node_list]
    simp only [node_list_to_node]
    simp only [args_to_int]
    simp only [node_to_list]
    simp only [atom_to_int_cast]
    simp only [only_atoms, round_trip_int]

    simp only [args_to_int, Function.comp_apply] at ih
    rw [ih]
    simp only [bind, Except.bind, pure, Except.pure]


theorem op_add_n_numbers { zs : List Int } : handle_op_add zs = Except.ok (Node.atom (int_to_atom (zs.foldl (fun a b => (a + b)) 0))) := by
  unfold handle_op_add
  rw [round_trip_int_list]


def quote_node (n: Node) : Node := Node.pair Node.one n


def quoted_nodes (ns : List Node) : Node :=
  match ns with
  | [] => Node.nil
  | n :: ns0 =>
      Node.pair (quote_node n) (quoted_nodes ns0)


#eval quoted_nodes [1, 2, 3]



theorem run_add_nil: bruns_to ([OP_ADD, 0]: Node) (0: Node) 0 := by
  simp [bruns_to]
  use 2
  rfl


theorem run_add_one_number_1 {z: Int}: bruns_to ([OP_ADD, 1]: Node) (z: Node) (z: Node) := by
  rw [bruns_to]
  use 2
  unfold apply_node map_or_err
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Function.comp_apply, node_list_to_node,
    Int.ofNat_eq_coe, Nat.cast_one, Node.nil, OP_Q, Nat.add_one_sub_one, OP_A, bind_assoc,
    pure_bind]
  simp only [OP_ADD, Nat.cast_ofNat, gt_iff_lt, Nat.ofNat_pos, Int.reduceLT, small_int_to_atom,
    Int.reduceAbs, List.cons.injEq, OfNat.ofNat_ne_one, and_true, ↓reduceIte, zero_lt_one,
    Nat.one_lt_ofNat, isUnit_one, Int.natAbs_of_isUnit, Nat.reduceEqDiff]
  simp only [handle_opcode_for_atom, handle_opcode]

  unfold map_or_err
  simp only [bind, Except.bind, Node.nil]

  simp only [apply_node, one_ne_zero, ↓reduceIte]
  simp only [node_at, atom_to_nat, base_b_be_to_nat_inner, List.length_nil, pow_zero, mul_one,
    zero_add, Nat.reduceAdd, node_at_wdepth, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.one_lt_ofNat,
    one_ne_zero]
  simp only [handle_op_add]
  unfold List.foldl
  simp only [args_to_int, node_to_list, atom_to_int_cast, only_atoms, round_trip_int]
  simp only [bind, Except.bind, pure, Except.pure, zero_add, List.foldl_nil]


theorem run_add_two_numbers {z1 z2: Int}: bruns_to ([OP_ADD, 2, 5]: Node) ([z1, z2]: Node) ((z1 + z2): Node) := by
  rw [bruns_to]
  use 2
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


theorem run_add_two_quoted_numbers {z1 z2: Int}: bruns_to ([(OP_ADD: Node), (Node.pair 1 z1), (Node.pair 1 z2)]: Node) Node.nil ((z1 + z2): Node) := by
  simp [bruns_to]
  use 2
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


theorem run_mul_two_quoted_numbers {z1 z2: Int}: bruns_to ([((OP_MUL): Node), (Node.pair 1 z1), (Node.pair 1 z2)]: Node) Node.nil ((z1 * z2): Node) := by
  rw [bruns_to]
  use 2
  unfold apply_node map_or_err
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, node_list_to_node, Function.comp_apply,
    Int.ofNat_eq_coe, round_trip_int, Node.nil, OP_Q, Nat.add_one_sub_one, OP_A, bind_assoc,
    pure_bind]

  unfold map_or_err apply_node
  unfold map_or_err apply_node
  simp [bind, Except.bind, Except.pure, pure]
  rw [OP_MUL]
  simp [small_int_to_atom, OP_Q, OP_A]
  simp [handle_opcode_for_atom, handle_opcode]

  simp [handle_op_mul]

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


lemma map_err_quoted_nodes_eq_nodes (ns: List Node) (h_d: d ≠ 0) {env: Node} : map_or_err (apply_node d · env) (quoted_nodes ns) = Except.ok ns := by
  induction ns with
  | nil =>
    unfold map_or_err
    simp [quoted_nodes, Except.bind, bind, Except.pure, pure, node_list_to_node]

  | cons head tail ih =>
    unfold map_or_err
    unfold quoted_nodes
    simp
    unfold quoted_atoms at ih
    rw [ih]
    simp [Except.bind, bind]
    unfold apply_node
    simp [h_d, quote_node, OP_Q, pure, Except.pure, node_list_to_node]


lemma map_err_quoted_atoms_eq_atoms (as: List Atom) (h_d: d ≠ 0) {env: Node} : map_or_err (apply_node d · env) (quoted_atoms as) = Except.ok as := by
  unfold quoted_atoms
  simp [map_err_quoted_nodes_eq_nodes (as.map Node.atom) h_d]
  rfl


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

  simp [map_err_quoted_atoms_eq_atoms]
  simp [bind, Except.bind]
  simp [args_to_int_atoms_ok]


---- unfinished proofs go after this line


lemma concat_of_quoted_atoms_is_ok (as: List Atom): node_applies (Node.pair (Node.atom [OP_CONCAT]) (quoted_atoms as)) 0 := by
  use 2
  unfold apply_node
  simp [atom_cast, clip_255, OP_CONCAT, OP_Q, OP_A]
  simp [handle_opcode_for_atom, handle_opcode]

  simp [map_err_quoted_atoms_eq_atoms]
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

  simp [map_err_quoted_atoms_eq_atoms]
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
