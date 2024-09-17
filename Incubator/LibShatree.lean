import Mathlib

import Clvm.H2n
import Clvm.Hex
import Clvm.Node
import Clvm.Run
import Clvm.Serde
import Clvm.Sha256
import Clvm.SmallIntToAtom

import Clvm.Puzzles.Apply

import Incubator.H2n

import Lean.Elab.Tactic


macro "unfold_apply_node_1" : tactic => `(tactic| rewrite (config := {occs := .pos [1]}) [apply_node])


macro "do_apply_node" : tactic => `(tactic| simp only [
    apply_node,
    List.cons.injEq,
    List.length_nil,
    Nat.one_lt_ofNat,
    Nat.reduceAdd,
    Nat.succ_sub_succ_eq_sub,
    Node.nil,
    OP_A,
    OP_Q,
    OfNat.ofNat_ne_one,
    OfNat.ofNat_ne_zero,
    and_true,
    apply_node,
    atom_to_nat,
    base_b_be_to_nat,
    base_b_be_to_nat_inner,
    mul_one,
    node_at,
    node_at_wdepth,
    one_ne_zero,
    pow_zero,
    small_int_to_atom,
    tsub_zero,
    zero_add,
    ↓reduceIte,
    ]
)


macro "collapse" : tactic => `(tactic|   simp only [
    Int.ofNat_eq_coe,
    Nat.cast_ofNat,
    Int.ofNat,
    Nat.ofNat_pos,
    Except.bind,
    Except.pure,
    List.cons.injEq,
    List.length_nil,
    Nat.div_self,
    Nat.one_lt_ofNat,
    Nat.reduceDiv,
    Nat.reduceLT,
    Nat.succ.injEq,
    Nat.succ_sub_succ_eq_sub,
    Nat.zero_shiftLeft,
    Node.nil,
    OP_A,
    OP_Q,
    OfNat.ofNat_ne_one,
    and_true,
    apply_node,
    atom_to_nat,
    base_b_be_to_nat,
    base_b_be_to_nat_inner,
    bind,
    exactly_two_args,
    lt_self_iff_false,
    map_or_err,
    mul_one,
    node_at,
    node_at_wdepth,
    one_ne_zero,
    pow_zero,
    pure,
    small_int_to_atom,
    tsub_zero,
    zero_add,
    ↓reduceIte,
    ])

macro "resolve_opcode" : tactic => `(tactic|
    simp [handle_opcode_for_atom, handle_opcode, node_to_list, List.length, bind, Except.bind, pure, Except.pure, atom_only_cast,
    handle_op_sha256,
    handle_op_l,
    handle_op_i,
    handle_op_c,
    ]
)


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
  unfold tree_atom_prog O_SHA256 OP_SHA256 O_Q
  do_apply_node
  simp [Atom.to, atom_cast, clip_255, OP_Q, OP_SHA256, OP_A]

  unfold apply_node
  do_apply_node
  collapse
  simp [small_int_to_atom]
  collapse
  resolve_opcode

  simp only [sha256_tree_hash_node, List.foldl, List.nil_append, List.singleton_append]


set_option maxRecDepth 1000

lemma sha256tree_func_atom_works { a: Atom } : bruns_to sha256tree_func (Node.pair sha256tree_func (Node.pair (Node.atom a) 0)) (Node.atom (sha256_tree_hash_node (Node.atom a))) := by
  use 50
  simp only [sha256tree_func]
  h2n!_peel

  --h2n!_eval

  conv in h2n! _ =>
    simp [h2n!, h2n, h2n_parsed_node, h2n_parsed_node!]
    unfold h2b_lc
    simp [bind, Except.bind]
    unfold hex_pair_to_byte hex_nibble_to_byte Char.toLower Char.ofNat
    simp [Nat.isValidChar]
    unfold bytes_to_parsed_node
    simp [pure, Except.pure]
    simp [bytes_to_parsed_node, h2b_lc, bind, Except.bind, pure, Except.pure, hex_pair_to_byte, hex_nibble_to_byte, Char.toLower, Char.ofNat, Nat.isValidChar, pure, Except.pure, bytes_to_parsed_node, bytes_to_atom]
    simp [MAX_SINGLE_BYTE, bytes_to_parsed_node, bytes_to_atom, atom_cast, clip_255, bind, Except.bind, pure, Except.pure]

  do_apply_node

  --simp [exactly_two_args, Bind.bind, Except.bind, pure, Except.pure]

  h2n!_peel


  conv in h2n! _ =>
    simp [h2n_second!, h2n_second, h2n!, h2n, h2n_parsed_node, h2n_parsed_node!]
    unfold h2b_lc
    simp [bind, Except.bind]
    unfold hex_pair_to_byte hex_nibble_to_byte Char.toLower Char.ofNat
    simp [Nat.isValidChar]
    unfold bytes_to_parsed_node
    simp [pure, Except.pure]
    simp [bytes_to_parsed_node, h2b_lc, bind, Except.bind, pure, Except.pure, hex_pair_to_byte, hex_nibble_to_byte, Char.toLower, Char.ofNat, Nat.isValidChar, pure, Except.pure, bytes_to_parsed_node, bytes_to_atom]
    simp [MAX_SINGLE_BYTE, bytes_to_parsed_node, bytes_to_atom, atom_cast, clip_255, bind, Except.bind, pure, Except.pure]

  collapse

  have: h2n_second! "02ffff03ffff07ff0580ffff01ff0bffff0102ffff02ff02ffff04ff02ffff04ff09ff80808080ffff02ff02ffff04ff02ffff04ff0dff8080808080ffff01ff0bffff0101ff058080ff0180" =
                  h2n!          "ffff03ffff07ff0580ffff01ff0bffff0102ffff02ff02ffff04ff02ffff04ff09ff80808080ffff02ff02ffff04ff02ffff04ff0dff8080808080ffff01ff0bffff0101ff058080ff0180" := by
      rfl

  rw [this]
  clear this



  h2n!_peel
  h2n!_peel
  conv in h2n! _ =>
    simp [h2n!, h2n, h2n_parsed_node, h2n_parsed_node!]
    unfold h2b_lc
    simp [bind, Except.bind]
    unfold hex_pair_to_byte hex_nibble_to_byte Char.toLower Char.ofNat
    simp [Nat.isValidChar]
    unfold bytes_to_parsed_node
    simp [pure, Except.pure]
    simp [bytes_to_parsed_node, h2b_lc, bind, Except.bind, pure, Except.pure, hex_pair_to_byte, hex_nibble_to_byte, Char.toLower, Char.ofNat, Nat.isValidChar, pure, Except.pure, bytes_to_parsed_node, bytes_to_atom]
    simp [MAX_SINGLE_BYTE, bytes_to_parsed_node, bytes_to_atom, atom_cast, clip_255, bind, Except.bind, pure, Except.pure]

  have: h2n_second! "ff03ffff07ff0580ffff01ff0bffff0102ffff02ff02ffff04ff02ffff04ff09ff80808080ffff02ff02ffff04ff02ffff04ff0dff8080808080ffff01ff0bffff0101ff058080ff0180" =
    h2n! "ffff07ff0580ffff01ff0bffff0102ffff02ff02ffff04ff02ffff04ff09ff80808080ffff02ff02ffff04ff02ffff04ff0dff8080808080ffff01ff0bffff0101ff058080ff0180" := by
      simp [h2n_second!, h2n!]
      sorry

  simp [this]
  clear this

  h2n!_peel
  h2n!_peel

  unfold h2n_second! h2n_second
  simp [h2n!, h2n, h2n_parsed_node, h2n_parsed_node!]
  unfold h2b_lc
  simp [bind, Except.bind]
  unfold hex_pair_to_byte hex_nibble_to_byte Char.toLower Char.ofNat
  simp [Nat.isValidChar]
  unfold bytes_to_parsed_node
  simp [pure, Except.pure]
  simp [bytes_to_parsed_node, h2b_lc, bind, Except.bind, pure, Except.pure, hex_pair_to_byte, hex_nibble_to_byte, Char.toLower, Char.ofNat, Nat.isValidChar, pure, Except.pure, bytes_to_parsed_node, bytes_to_atom]
  simp [MAX_SINGLE_BYTE, bytes_to_parsed_node, bytes_to_atom, atom_cast, clip_255, bind, Except.bind, pure, Except.pure]


  simp [map_or_err]

  resolve_opcode

  do_apply_node
  collapse
  resolve_opcode
  sorry


--#eval sha256tree_prog
--#eval toString sha256tree_prog

--set_option maxHeartbeats 1000000


lemma tree_works: bruns_to sha256tree_func (Node.pair sha256tree_func (Node.pair X 0)) (Node.atom (sha256_tree_hash_node X)) := by
  induction X with
  | atom a => apply sha256tree_func_atom_works
  | pair n1 n2 ih1 ih2 =>
    obtain ⟨n1', h1⟩ := ih1
    obtain ⟨n2', h2⟩ := ih2
    use (max n1' n2') + 5

    have h_n2'_eq_0 : n2' ≠ 0 := by
      by_contra h0
      unfold apply_node at h2
      simp [h0, Except.err] at h2

    have h_n2'_gt_0 : n2' > 0 := by
      by_contra h0
      simp at h0
      simp [h_n2'_eq_0] at h0

    have h_max_gt_0 : max n1' n2' > 0 := by
      exact lt_max_of_lt_right h_n2'_gt_0

    unfold apply_node
    simp [h_max_gt_0]

    rewrite (config := {occs := .pos [1]}) [sha256tree_func]
    simp [h2n!, h2n, h2n_parsed_node, h2n_parsed_node!]
    unfold h2b_lc
    simp [bind, Except.bind]
    unfold hex_pair_to_byte hex_nibble_to_byte Char.toLower Char.ofNat
    simp [Nat.isValidChar]
    simp [pure, Except.pure]
    simp [bytes_to_parsed_node, h2b_lc, bind, Except.bind, pure, Except.pure, hex_pair_to_byte, hex_nibble_to_byte, Char.toLower, Char.ofNat, Nat.isValidChar, pure, Except.pure, bytes_to_parsed_node, bytes_to_atom]
    simp [MAX_SINGLE_BYTE, bytes_to_parsed_node, bytes_to_atom, atom_cast, clip_255, bind, Except.bind, pure, Except.pure]

    simp [OP_Q, OP_A]

    unfold map_or_err map_or_err map_or_err
    simp only [bind, Except.bind, pure, Except.pure]

    do_apply_node
    collapse
    resolve_opcode

    collapse
    resolve_opcode

    unfold node_at_wdepth
    simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.one_lt_ofNat, one_ne_zero]

    simp [h_n2'_eq_0]

    have h_rw1: apply_node (max n1' n2' + 2) sha256tree_func
            (sha256tree_func.pair (n1.pair (Node.atom { data := [], lt := Node.nil.proof_1 }))) =
            apply_node n1' sha256tree_func
            (sha256tree_func.pair (n1.pair 0)) := by
      have h_ok_1 : is_ok (apply_node n1' sha256tree_func (sha256tree_func.pair (n1.pair 0))) := by
        use Node.atom (sha256_tree_hash_node n1)
      have h_ineq : n1' ≤ max n1' n2' + 2:= by
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

    have h_rw2: apply_node (max n1' n2' + 2) sha256tree_func
            (sha256tree_func.pair (n2.pair (Node.atom { data := [], lt := Node.nil.proof_1 }))) =
            apply_node n2' sha256tree_func
            (sha256tree_func.pair (n2.pair 0)) := by
      have h_ok_1 : is_ok (apply_node n2' sha256tree_func (sha256tree_func.pair (n2.pair 0))) := by
        use Node.atom (sha256_tree_hash_node n2)
      have h_ineq : n2' ≤ max n1' n2' + 2:= by
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

    collapse
    resolve_opcode

    simp [List.foldl]

    rw [sha256_tree_hash_node]
    simp


lemma sha256tree_func_atom_works1 : bruns_to sha256tree_func (Node.pair sha256tree_func (Node.pair (Node.atom a) 0)) (Node.atom (sha256_tree_hash_node (Node.atom a))) := by
  apply tree_works
