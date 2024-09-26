import Mathlib

import Clvm.H2n
import Clvm.H2b
import Clvm.Node
import Clvm.Run
import Clvm.SmallIntToAtom
import Clvm.String


import Incubator.H2b
import Incubator.String

import Lean

open Lean
open Lean.Elab.Tactic

open Lean.Meta



open Lean Elab Tactic Meta


theorem peel_2_from_h2n: is_ok (h2n s) → s.take 2 = "ff" → h2n! s = Node.pair (h2n_first! (s.drop 2)) (h2n_second! (s.drop 2)) := by
  intro h h_ff
  obtain z := h2n_ff s h (s0 := s.drop 2)

  sorry

@[simp]
lemma string_drop_rw {s: String}: s.drop k = String.mk (s.data.drop k) := by
  ext n0 c
  simp only [String.data_drop]

-- goal: come up with a way to rewrite `h2n! "ff..."` to `Node.pair (h2n! "...") (h2n_second! "...")`


lemma round_trip_node {n: Node}: n = h2n! (n2h n) := by sorry


lemma bruns_to_quote_100: bruns_to (h2n! "ff0164") 0 100 := by
  have: is_ok (h2n "ff0164") := by
    simp [is_ok, h2n, h2n_parsed_node, h2b_lc, hex_pair_to_byte, hex_nibble_to_byte, bind, Except.bind, pure, Except.pure, bytes_to_parsed_node, bytes_to_atom, MAX_SINGLE_BYTE]

  unfold bruns_to

  -- do peel
  rw [peel_2_from_h2n this (by decide)]

  -- simplify `String.drop`
  simp only [string_drop_rw, ↓Char.isValue, List.drop_succ_cons, List.drop_zero, String.reduceMk]

  -- swap `h2n_second!` with simpler `h2n!` versions
  conv in (h2n_second! _) => simp [h2n_second!, h2n_second, h2n_parsed_node!, h2n_parsed_node, h2b_lc, hex_pair_to_byte, hex_nibble_to_byte, bytes_to_parsed_node, bytes_to_atom, MAX_SINGLE_BYTE, bind, Except.bind, pure, Except.pure, atom_cast, clip_255]
  rw [round_trip_node (n := Node.atom { data := [100], lt := _ })]
  simp [n2h, node_to_bytes, atom_to_serialized_bytes, MAX_SINGLE_BYTE, b2h, nat_to_hex, String.join]

  -- swap `h2n_first!` with simpler `h2n!` versions
  conv in (h2n_first! _) => simp [h2n_first!, h2n_parsed_node!, h2n_parsed_node, h2b_lc, hex_pair_to_byte, hex_nibble_to_byte, bytes_to_parsed_node, bytes_to_atom, MAX_SINGLE_BYTE, bind, Except.bind, pure, Except.pure, atom_cast, clip_255]
  rw [round_trip_node (n := Node.atom { data := [1], lt := _ })]
  simp [n2h, node_to_bytes, atom_to_serialized_bytes, MAX_SINGLE_BYTE, b2h, nat_to_hex, String.join]

  -- now let's unfold a level of the program
  unfold apply_node
  use 2
  simp
  conv in h2n! _ =>
    simp [h2n!, h2n_parsed_node!, h2n_parsed_node, h2b_lc, hex_pair_to_byte, hex_nibble_to_byte, bytes_to_parsed_node, bytes_to_atom, MAX_SINGLE_BYTE, bind, Except.bind, pure, Except.pure, atom_cast, clip_255]

  simp [OP_Q]

  -- we've solved it
  conv in h2n! _ =>
    simp [h2n!, h2n_parsed_node!, h2n_parsed_node, h2b_lc, hex_pair_to_byte, hex_nibble_to_byte, bytes_to_parsed_node, bytes_to_atom, MAX_SINGLE_BYTE, bind, Except.bind, pure, Except.pure, atom_cast, clip_255]

  simp [OfNat.ofNat]
  simp [small_int_to_atom]







@[simp]
lemma string_drop {s: String}: s.drop n = String.mk (s.data.drop n) := by
  ext n0 c
  simp only [String.data_drop]





-- recursively search for `h2n! LITERAL` in the expression
def find_h2n!_lit_in_exp (e : Expr) : MetaM (Option String) := do
    match e with
    | Expr.app (.const `h2n! _) (.lit (.strVal s)) => return some s
    | Expr.app f a =>
      --logInfo m!"Expr.app: {f} {a}"
      let r1 ← find_h2n!_lit_in_exp f
      match r1 with
      | some s => return some s
      | none => find_h2n!_lit_in_exp a
    | Expr.lam _ _ b _ => find_h2n!_lit_in_exp b  -- Search in lambda body
    | Expr.letE _ _ v b _ =>
      -- Search in let binding and body
      return ← find_h2n!_lit_in_exp v <|> find_h2n!_lit_in_exp b
    | Expr.mdata _ b => find_h2n!_lit_in_exp b  -- Search in metadata body
    | Expr.proj _ _ b => find_h2n!_lit_in_exp b  -- Search in projections
    | _ => return none


-- Define the custom syntax for the tactic
syntax (name := h2n!_peel_tactic) "h2n!_peel" : tactic


@[tactic h2n!_peel_tactic]
def h2n!_peel_imp : Tactic := fun _ => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  --logInfo m!"Full goal type: {goalType}"

  match ← find_h2n!_lit_in_exp goalType with
  | none => throwError "Expected h2n! literal in the goal"
  | some s =>
    --logInfo m!"s : {s}"
    if s.length < 2 then
      throwError "h2n! string must have at least 2 characters"
    let rest := s.drop 2

    --let t1 := ← `(tactic| have: h2n! $(Lean.Syntax.mkStrLit s) = Node.pair (h2n! $(Lean.Syntax.mkStrLit rest))  (h2n_second! $(Lean.Syntax.mkStrLit rest)) := by
    --  apply h2n!_split
    --  simp [h2n, is_ok, bind, Except.bind, h2n_parsed_node,
    --    h2b_lc, hex_pair_to_byte, hex_nibble_to_byte, bytes_to_parsed_node,
    --    bytes_to_atom, Except.err, MAX_SINGLE_BYTE, pure, Except.pure]
    --  rfl
    --)
    --logInfo m!"t1: {t1}"
    Lean.Elab.Tactic.evalTactic (← `(tactic| have: h2n! $(Lean.Syntax.mkStrLit s) = Node.pair (h2n! $(Lean.Syntax.mkStrLit rest))  (h2n_second! $(Lean.Syntax.mkStrLit rest)) := by
      apply h2n!_split
      simp only [is_ok, h2n, bind, Except.bind, h2n_parsed_node, h2b_lc, hex_pair_to_byte,
    hex_nibble_to_byte, ↓Char.isValue, Char.reduceToLower, Char.reduceToNat, ge_iff_le,
    Nat.reduceLeDiff, decide_True, decide_False, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
    le_refl, Bool.and_self, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, tsub_eq_zero_of_le,
    zero_mul, add_zero, bytes_to_parsed_node, OfNat.zero_ne_ofNat, bytes_to_atom, MAX_SINGLE_BYTE,
    zero_le, Nat.reduceEqDiff, pure, Except.pure, Except.ok.injEq, exists_eq']

      simp only [substring_take, ↓Char.isValue, List.take_succ_cons, List.take_zero, String.reduceMk]
    ))
    Lean.Elab.Tactic.evalTactic (← `(tactic| rw (config := {occs := .pos [1]}) [this] ))
    Lean.Elab.Tactic.evalTactic (← `(tactic| clear this ))



example : h2n! "ff0022" = Node.pair (h2n! "0022")  (h2n_second! "0022") := by
  apply h2n!_split

  simp only [is_ok, h2n, bind, Except.bind, h2n_parsed_node, h2b_lc, hex_pair_to_byte,
    hex_nibble_to_byte, ↓Char.isValue, Char.reduceToLower, Char.reduceToNat, ge_iff_le,
    Nat.reduceLeDiff, decide_True, decide_False, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
    le_refl, Bool.and_self, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, tsub_eq_zero_of_le,
    zero_mul, add_zero, bytes_to_parsed_node, OfNat.zero_ne_ofNat, bytes_to_atom, MAX_SINGLE_BYTE,
    zero_le, Nat.reduceEqDiff, pure, Except.pure, Except.ok.injEq, exists_eq']

  simp only [substring_take, ↓Char.isValue, List.take_succ_cons, List.take_zero, String.reduceMk]



example : h2n! "ff8022" = Node.pair 0 34 := by
  h2n!_peel


  simp only [Node.pair.injEq]

  constructor

  simp [h2n!, h2n_parsed_node!, h2n_parsed_node, h2b_lc, hex_pair_to_byte, hex_nibble_to_byte,
    Except.pure, pure, bind, Except.bind, bytes_to_parsed_node, bytes_to_atom, MAX_SINGLE_BYTE]

  unfold OfNat.ofNat Node.instOfNat int_to_atom int_to_twos_comp
  simp [Int.ofNat]


  simp [h2n_second!, h2n_second, h2n_parsed_node, h2b_lc, hex_pair_to_byte, hex_nibble_to_byte,
    Except.pure, pure, bind, Except.bind, bytes_to_parsed_node, bytes_to_atom, MAX_SINGLE_BYTE]

  simp [atom_cast, clip_255]
  simp [OfNat.ofNat]
  simp [small_int_to_atom]




example : h2n! "ff0022" = Node.pair (h2n_first! "0022") (h2n_second! "0022") := by
  h2n!_peel

  unfold h2n! h2n_first!
  simp




example : h2n! "ff0022" = Node.pair (Node.atom (Atom.mk [0] (by decide))) (h2n_second! "0022") := by
  h2n!_peel
  simp
  sorry

--#lint
