import Mathlib

import Clvm.HalfBaked
import Clvm.Hex
import Clvm.Node
import Clvm.Run
import Clvm.Serde
import Clvm.Sha256

import Clvm.Puzzles.Apply


/-
@[app_unexpander Node.pair]
def unexpNodePair : Lean.PrettyPrinter.Unexpander
  | `($(_) $a $b) => `(($a . $b))
  | _ => throw ()

open Lean PrettyPrinter Delaborator SubExpr

def foo : Nat → Nat := fun x => 42

@[delab app.foo]
def delabFoo : Delab := do
  `(1)


@[delab app.Node.pair]
def delabNode : Delab := do
  `(1)

-/

--#eval (h2n! "ff8080")
--#check foo
--#check foo 13

def sha256_tree_hash_node (node: Node) : Atom :=
  match node with
  | Node.atom a => sha256 (1 :: a.data)
  | Node.pair a b => sha256 (2 :: (sha256_tree_hash_node a).data ++ (sha256_tree_hash_node b).data)


def sha256_tree_hash (node: Node) : List Nat :=
  (sha256_tree_hash_node node).data


--#eval (sha256_tree_hash 0).hex


/-
(mod X
  (defun sha256tree1
      (TREE)
      (if (l TREE)
          (sha256 2 (sha256tree1 (f TREE)) (sha256tree1 (r TREE)))
          (sha256 1 TREE)
      )
  )
  (sha256tree1 X)
)

(a
  (q a 2 (c 2 (c 3 ())))
  (c (q 2 (i (l 5) (q 11 (q . 2) (a 2 (c 2 (c 9 ()))) (a 2 (c 2 (c 13 ())))) (q 11 (q . 1) 5)) 1) 1))
-/

-- set_option maxRecDepth 600

def sha256tree_prog := h2n! "ff02ffff01ff02ff02ffff04ff02ffff04ff03ff80808080ffff04ffff01ff02ffff03ffff07ff0580ffff01ff0bffff0102ffff02ff02ffff04ff02ffff04ff09ff80808080ffff02ff02ffff04ff02ffff04ff0dff8080808080ffff01ff0bffff0101ff058080ff0180ff018080"


def sha256tree_func := h2n! "ff02ffff03ffff07ff0580ffff01ff0bffff0102ffff02ff02ffff04ff02ffff04ff09ff80808080ffff02ff02ffff04ff02ffff04ff0dff8080808080ffff01ff0bffff0101ff058080ff0180"
-- (a (i (l 5) (q 11 (q . 2) (a 2 (c 2 (c 9 ()))) (a 2 (c 2 (c 13 ())))) (q 11 (q . 1) 5)) 1)

/-
def h2_pair (s: String) : Result Node (Array Nat) :=
  let b : Array Nat := h2b s
  match bytes_to_node_inner (b.size*2) b with
  | Result.ok dresult0 =>
    match bytes_to_node_inner (dresult0.bytes.size * 2) dresult0.bytes with
    | Result.ok dresult1 => Result.ok (Node.pair dresult0.node dresult1.node)
    | Result.err bytes msg => Result.err bytes msg
  | Result.err bytes msg => Result.err bytes msg
-/


def eq_if_ok (a: Except α β) (b: Except α β) := is_ok a → a = b



@[simp] def O_Q := Node.atom (Atom.to [OP_Q])
@[simp] def O_SHA256 := Node.atom (Atom.to [OP_SHA256])
@[simp] def A_5 := Node.atom (Atom.to [5])

def tree_atom_prog : Node := Node.pair O_SHA256 (Node.pair (Node.pair O_Q Node.one) (Node.pair 5 0)) -- (11 (q . 1) 5)

--#eval n2h tree_atom_prog

lemma tree_atom_works : bruns_to tree_atom_prog (Node.pair 0 (Node.pair (Node.atom a) 0)) (Node.atom (sha256_tree_hash_node (Node.atom a))) := by
  use 50
  unfold tree_atom_prog
  unfold apply_node
  unfold map_or_err map_or_err map_or_err
  unfold apply_node
  simp
  simp [Atom.to, atom_cast, max_255, OP_Q, OP_SHA256, OP_A]
  simp [handle_opcode_for_atom, handle_opcode]
  simp [bind, Except.bind]
  simp [small_int_to_atom]
  simp [apply_node, atom_to_nat, node_at, node_at_wdepth, OP_Q, base_b_be_to_nat_inner]

  unfold handle_op_sha256
  simp [node_to_list, list_except_to_except_list]
  simp only [sha256_tree_hash_node]
  simp [atom_only_cast]
  simp [bind, Except.bind, pure, Except.pure]


set_option maxRecDepth 1000

lemma sha256tree_func_atom_works { a: Atom } : bruns_to sha256tree_func (Node.pair sha256tree_func (Node.pair (Node.atom a) 0)) (Node.atom (sha256_tree_hash_node (Node.atom a))) := by
  use 50
  simp only [sha256tree_func]
  simp [h2n!, h2n, h2n_parsed_node]
  unfold h2b_lc
  simp [bind, Except.bind]
  unfold hex_pair_to_byte hex_nibble_to_byte Char.toLower Char.ofNat
  simp [Nat.isValidChar]
  unfold bytes_to_parsed_node
  simp [pure, Except.pure]
  simp [bytes_to_parsed_node, h2b_lc, bind, Except.bind, pure, Except.pure, hex_pair_to_byte, hex_nibble_to_byte, Char.toLower, Char.ofNat, Nat.isValidChar, pure, Except.pure, bytes_to_parsed_node, bytes_to_atom]

  simp [MAX_SINGLE_BYTE, bytes_to_parsed_node, bytes_to_atom, atom_cast, max_255, bind, Except.bind, pure, Except.pure]


  simp only [apply_node, OfNat.ofNat_ne_zero, ↓reduceIte, OP_Q, List.cons.injEq, OfNat.ofNat_ne_one,
    and_true, Nat.succ_sub_succ_eq_sub, tsub_zero, OP_A]

  unfold map_or_err map_or_err map_or_err
  simp only [Node.nil]
  simp only [apply_node, node_at, atom_to_nat, node_at_wdepth, OP_Q, OP_A]
  simp only [↓reduceIte, Nat.zero_shiftLeft, zero_add, Nat.one_lt_ofNat, List.cons.injEq,
    OfNat.ofNat_ne_one, and_true, Nat.succ_sub_succ_eq_sub, tsub_zero, Nat.succ.injEq]
  simp [base_b_be_to_nat_inner]
  simp [bind, Except.bind, pure, Except.pure]

  unfold map_or_err map_or_err map_or_err map_or_err
  simp
  simp only [apply_node, node_at, atom_to_nat, node_at_wdepth, OP_Q, OP_A]
  simp only [↓reduceIte, List.cons.injEq, OfNat.ofNat_ne_one, and_true, Nat.succ_sub_succ_eq_sub,
    tsub_zero, Nat.succ.injEq]
  simp [base_b_be_to_nat_inner]
  simp [bind, Except.bind, pure, Except.pure]

  simp only [map_or_err]
  simp
  simp only [apply_node, node_at, atom_to_nat, node_at_wdepth, OP_Q, OP_A]
  simp only [↓reduceIte, List.cons.injEq, OfNat.ofNat_ne_one, and_true, Nat.succ_sub_succ_eq_sub,
    tsub_zero, Nat.succ.injEq]
  simp [node_at_wdepth]
  simp [base_b_be_to_nat_inner]
  simp [bind, Except.bind, pure, Except.pure]

  simp [handle_opcode_for_atom, handle_opcode, handle_op_l, handle_op_i]

  simp [apply_node, OP_Q, map_or_err, node_at, atom_to_nat, node_at_wdepth, base_b_be_to_nat_inner, exactly_two_args]
  simp [OP_A]

  simp [handle_opcode_for_atom, handle_opcode, handle_op_sha256, node_to_list, List.length]
  simp [bind, Except.bind, pure, Except.pure]

  simp [List.map, atom_only_cast]

  rfl


--#eval sha256tree_prog
--#eval toString sha256tree_prog

--set_option maxHeartbeats 1000000


lemma tree_works: bruns_to sha256tree_func (Node.pair sha256tree_func (Node.pair X 0)) (Node.atom (sha256_tree_hash_node X)) := by
  induction X with
  | atom a => apply sha256tree_func_atom_works
  | pair n1 n2 ih1 ih2 =>
    obtain ⟨n1', h1⟩ := ih1
    obtain ⟨n2', h2⟩ := ih2
    use (max n1' n2') + 6

    unfold apply_node
    have h_n1'_gt_0 : (max n1' n2') > 0 := by

      have h_n2'_gt_0 : n2' > 0 := by

        by_contra h0
        have n2'_eq_0 : n2' = 0 := by
          simp [Nat.max_eq_zero_iff] at h0
          exact h0
        simp [n2'_eq_0] at h2
        unfold apply_node at h2
        simp only [↓reduceIte, Except.err] at h2

      exact lt_max_of_lt_right h_n2'_gt_0

    have h_max_ne_0' : max n1' n2' > 0 := by
      linarith

    simp [h_max_ne_0']

    rewrite (config := {occs := .pos [1]}) [sha256tree_func]
    simp [h2n!, h2n, h2n_parsed_node]
    unfold h2b_lc
    simp [bind, Except.bind]
    unfold hex_pair_to_byte hex_nibble_to_byte Char.toLower Char.ofNat
    simp [Nat.isValidChar]
    simp [pure, Except.pure]
    simp [bytes_to_parsed_node, h2b_lc, bind, Except.bind, pure, Except.pure, hex_pair_to_byte, hex_nibble_to_byte, Char.toLower, Char.ofNat, Nat.isValidChar, pure, Except.pure, bytes_to_parsed_node, bytes_to_atom]
    simp [MAX_SINGLE_BYTE, bytes_to_parsed_node, bytes_to_atom, atom_cast, max_255, bind, Except.bind, pure, Except.pure]

    simp [OP_Q, OP_A]

    unfold map_or_err map_or_err map_or_err
    simp only [bind, Except.bind, pure, Except.pure]

    rewrite (config := {occs := .pos [1]}) [apply_node]
    simp only [add_eq_zero, Nat.max_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte,
      node_at, atom_to_nat, base_b_be_to_nat_inner, List.length_nil, pow_zero, mul_one, zero_add,
      Nat.reduceAdd, node_at_wdepth, Nat.one_lt_ofNat, one_ne_zero, Node.nil]

    rewrite (config := {occs := .pos [1]}) [apply_node]
    simp only [add_eq_zero, Nat.max_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte, OP_Q,
      List.cons.injEq, OfNat.ofNat_ne_one, and_true, Nat.add_succ_sub_one, OP_A, Nat.succ_ne_self]

    rw [map_or_err]
    rw [map_or_err]
    rw [map_or_err]
    rw [map_or_err]
    simp only [bind, Except.bind, pure, Except.pure]

    rewrite (config := {occs := .pos [1]}) [apply_node]
    simp only [OP_Q, add_eq_zero, Nat.max_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte,
      List.cons.injEq, and_true, Nat.add_succ_sub_one, Node.nil]

    rewrite (config := {occs := .pos [1]}) [apply_node]
    simp only [OP_Q, add_eq_zero, Nat.max_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte,
      List.cons.injEq, and_true, Nat.add_succ_sub_one]

    rewrite (config := {occs := .pos [1]}) [apply_node]
    simp only [add_eq_zero, Nat.max_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte, OP_Q,
      List.cons.injEq, OfNat.ofNat_ne_one, and_true, Nat.add_succ_sub_one]
    simp only [bind, Except.bind, pure, Except.pure]

    rw [map_or_err, map_or_err, apply_node]
    simp only [Node.nil, add_eq_zero, Nat.max_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      node_at, atom_to_nat, base_b_be_to_nat_inner, List.length_nil, pow_zero, mul_one, zero_add,
      Nat.reduceAdd, node_at_wdepth, OfNat.ofNat_ne_zero, Nat.reduceLT, Nat.reduceSub,
      Nat.reduceDiv, Nat.reduceMod, lt_self_iff_false, Nat.ofNat_pos, Nat.div_self, Nat.mod_self,
      Nat.one_lt_ofNat, OP_A, Nat.reduceEqDiff]

    simp only [bind, Except.bind, pure, Except.pure]
    simp only [handle_opcode_for_atom, handle_opcode, handle_op_l, Node.one, handle_op_i,
      exactly_two_args]

    simp only [apply_node, atom_to_nat, node_at, node_at_wdepth, OP_Q, OP_A]
    simp
    rw [map_or_err, map_or_err, map_or_err, map_or_err, apply_node]
    simp only [bind, Except.bind, add_eq_zero, Nat.max_eq_zero_iff, OfNat.ofNat_ne_zero, and_false,
      ↓reduceIte, List.cons.injEq, and_true, Nat.add_succ_sub_one, pure, Except.pure, Node.nil, OP_Q]
    simp only [OfNat.ofNat_ne_one, ↓reduceIte]

    rw [map_or_err, map_or_err, map_or_err]
    simp only [bind, Except.bind, pure, Except.pure]
    simp only [OP_A]
    simp only [Node.nil, ↓reduceIte]

    rewrite (config := {occs := .pos [1]}) [apply_node]
    simp only [add_eq_zero, Nat.max_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, node_at,
      atom_to_nat, base_b_be_to_nat_inner, List.length_nil, pow_zero, mul_one, zero_add,
      Nat.reduceAdd, node_at_wdepth, OfNat.ofNat_ne_zero, lt_self_iff_false, Nat.reduceSub,
      Nat.ofNat_pos, Nat.div_self, Nat.mod_self]
    unfold node_at_wdepth
    simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.one_lt_ofNat, one_ne_zero]

    rw [apply_node]
    simp only [OP_Q, add_eq_zero, Nat.max_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      List.cons.injEq, and_true, add_tsub_cancel_right]
    simp only [OfNat.ofNat_ne_one, ↓reduceIte]
    rw [map_or_err, map_or_err, map_or_err, apply_node]
    simp only [bind, Except.bind, pure, Except.pure]

    rewrite (config := {occs := .pos [1]}) [apply_node]
    simp only [h_n1'_gt_0, ↓reduceIte, List.cons.injEq, and_true, Node.nil, OP_Q]
    simp only [OfNat.ofNat_ne_one, ↓reduceIte]

    rw [map_or_err, map_or_err, map_or_err, apply_node]
    simp only [bind, Except.bind, pure, Except.pure]
    simp only [node_at, atom_to_nat, node_at_wdepth]
    simp only [↓reduceIte, Node.nil, add_tsub_cancel_right]
    simp [base_b_be_to_nat_inner]

    rw [apply_node]
    simp only [node_at, atom_to_nat, node_at_wdepth, base_b_be_to_nat_inner]

    simp only [↓reduceIte, Node.nil, add_tsub_cancel_right]
    simp only [List.length_nil, pow_zero, mul_one, zero_add, Nat.reduceLT, ↓reduceIte,
      Nat.reduceDiv, Nat.reduceMod, one_ne_zero]

    simp only [node_at_wdepth, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.reduceLT, Nat.reduceSub,
      Nat.reduceDiv, Nat.reduceMod, one_ne_zero]

    unfold node_at_wdepth
    simp [OP_Q, OP_A]

    rewrite (config := {occs := .pos [1]}) [handle_opcode_for_atom]
    simp only [handle_opcode, handle_op_c, handle_opcode_for_atom, exactly_two_args]

    rw [apply_node]
    rw [apply_node]

    simp only [add_eq_zero, Nat.max_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte,
      List.cons.injEq, and_true, Nat.add_succ_sub_one]
    simp [OP_Q]
    rw [map_or_err, map_or_err, map_or_err, apply_node, apply_node]
    simp only [bind, Except.bind, pure, Except.pure]
    simp only [OP_Q, ↓reduceIte, List.cons.injEq, and_true, Nat.add_succ_sub_one, Node.nil]
    simp only [OfNat.ofNat_ne_one, ↓reduceIte]


    rw [map_or_err, map_or_err, map_or_err, apply_node, apply_node]
    simp only [OP_Q, OP_A]
    simp only [Node.nil, add_eq_zero, Nat.max_eq_zero_iff, OfNat.ofNat_ne_zero, and_false,
      ↓reduceIte, List.cons.injEq, and_true, Nat.add_succ_sub_one, bind_assoc, pure_bind]
    simp only [bind, Except.bind, pure, Except.pure]
    simp only [OfNat.ofNat_ne_one, ↓reduceIte, Nat.reduceEqDiff]
    rw [map_or_err, map_or_err, map_or_err, apply_node, apply_node]
    simp only [OP_Q, OP_A]
    simp only [Node.nil, add_eq_zero, Nat.max_eq_zero_iff, OfNat.ofNat_ne_zero, and_false,
      ↓reduceIte, List.cons.injEq, and_true, Nat.add_succ_sub_one, bind_assoc, pure_bind]
    simp only [bind, Except.bind, pure, Except.pure]
    simp only [node_at, atom_to_nat, base_b_be_to_nat_inner, zero_add, node_at_wdepth, one_ne_zero,
      ↓reduceIte, Nat.ofNat_pos, Node.nil, List.length_nil, pow_zero, mul_one, Nat.reduceAdd,
      OfNat.ofNat_ne_zero, Nat.reduceLT, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod,
      lt_self_iff_false, Nat.div_self, Nat.mod_self]

    unfold node_at_wdepth
    simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.one_lt_ofNat, one_ne_zero,
      handle_opcode_for_atom, handle_opcode, handle_op_c, exactly_two_args]

    have h_rw1: apply_node (max n1' n2' + 3) sha256tree_func
            (sha256tree_func.pair (n1.pair (Node.atom { data := [], lt := Node.nil.proof_1 }))) =
            apply_node n1' sha256tree_func
            (sha256tree_func.pair (n1.pair 0)) := by
      have h_ok_1 : is_ok (apply_node n1' sha256tree_func (sha256tree_func.pair (n1.pair 0))) := by
        use Node.atom (sha256_tree_hash_node n1)
      have h_ineq : n1' ≤ max n1' n2' + 3:= by
        have h_p: n1' ≤ max n1' n2' := by
          apply le_max_left n1' n2'
        linarith
      obtain h_lemma := apply_node_converges h_ok_1 h_ineq
      conv_rhs at h_lemma =>
        conv in n1.pair 0 =>
          unfold OfNat.ofNat Node.instOfNat
          simp [zero_to_atom]

      rw [← h_lemma]

    rw [h_rw1]
    rw [h1]

    have h_rw2: apply_node (max n1' n2' + 3) sha256tree_func
            (sha256tree_func.pair (n2.pair (Node.atom { data := [], lt := Node.nil.proof_1 }))) =
            apply_node n2' sha256tree_func
            (sha256tree_func.pair (n2.pair 0)) := by
      have h_ok_1 : is_ok (apply_node n2' sha256tree_func (sha256tree_func.pair (n2.pair 0))) := by
        use Node.atom (sha256_tree_hash_node n2)
      have h_ineq : n2' ≤ max n1' n2' + 3:= by
        have h_p: n2' ≤ max n1' n2' := by
          apply le_max_right n1' n2'
        linarith
      obtain h_lemma := apply_node_converges h_ok_1 h_ineq
      conv_rhs at h_lemma =>
        conv in n2.pair 0 =>
          unfold OfNat.ofNat Node.instOfNat
          simp [zero_to_atom]

      rw [← h_lemma]

    rw [h_rw2]
    rw [h2]
    simp only

    simp only [handle_op_sha256, node_to_list, bind_assoc, pure_bind, List.pure_def,
      List.bind_eq_bind]

    simp only [bind, Except.bind, pure, Except.pure]
    simp [atom_only_cast]

    rw [sha256_tree_hash_node]
    simp


lemma sha256tree_func_atom_works1 : bruns_to sha256tree_func (Node.pair sha256tree_func (Node.pair (Node.atom a) 0)) (Node.atom (sha256_tree_hash_node (Node.atom a))) := by
  apply tree_works
