import Mathlib

import Clvm.Hex
import Clvm.String
import Clvm.Util


import Incubator.SmallIntToAtom


import Lean
open Lean
open Lean.Elab.Tactic

open Lean.Meta



open Lean Elab Tactic Meta

-- Assume these lemmas exist
lemma h2b_cons (h1 h2 : Char) (t : String) :
  h2b! s!"{h1}{h2}{t}" = (h2b! s!"{h1}{h2}") ++ (h2b! t) := by sorry


lemma h2b_single (h1 h2 : Char) :
  h2b! s!"{h1}{h2}" = [h1.toNat * 16 + h2.toNat] := by sorry


-- Define the custom syntax for the tactic
syntax (name := hexToBytesTactic) "hex_to_bytes" term : tactic



@[tactic hexToBytesTactic]
def evalHexToBytes : Tactic := fun stx => do
  match stx with
  | `(tactic| hex_to_bytes $str) => do
    let hexStr ← match str.raw.isStrLit? with
      | some s => pure s
      | _ => throwError "hex_to_bytes tactic requires a string literal"

    let goal ← getMainGoal
    let (goalType: Expr) ← goal.getType
    logInfo m!"goalType: {goalType}"

    if let Expr.app (.app (.const ``Eq _) lhs) _ := goalType then do
      if let Expr.app (.const ``h2b! _) (.lit (Literal.strVal lhsStr)) := lhs then
        if hexStr != lhsStr then
          throwError "String in tactic doesn't match left-hand side of equality"

          -- Start the proof
          let proof ← `(by {
            rw [h2b_cons]
            simp
            rw [h2b_single]
            -- You might need more steps here depending on the specifics of h2b!
            rfl
          })

          Lean.Elab.Tactic.evalTactic proof
        else
          throwError "Left-hand side should be h2b! with a string literal"
      else
        throwError "Expected h2b! application on the left-hand side"

  | _ => throwError "Unsupported syntax"




lemma peel_2_from_h2b: is_ok (h2b s) → s.data.length ≥ 2 → h2b! s = [hex_pair_to_byte! (s.data[0]!) (s.data[1]!)] ++ h2b! (s.drop 2) := by
  intro h h_len
  conv_lhs => simp [h2b!]
  simp [h2b] at h
  obtain ⟨ ns, h_ns ⟩ := h
  simp [h_ns]
  unfold h2b_lc at h_ns


  cases h_s: s.data with
  | nil => simp [h_s, String.length, List.length] at h_len
  | cons c0 tail0 =>
    cases h_t: tail0 with
    | nil => simp [h_s, h_t, List.length] at h_len
    | cons c1 tail1 =>
      simp [h_s, h_t] at h_ns
      have: is_ok (hex_pair_to_byte c0 c1) := by
        by_contra h_c
        obtain ⟨c, h_err⟩ := not_ok h_c
        simp [h_err, bind, Except.bind] at h_ns

      obtain ⟨b, h_b⟩ := this
      simp [h_b, bind, Except.bind] at h_ns

      have: is_ok (h2b_lc tail1) := by
        by_contra h_c
        obtain ⟨c, h_err⟩ := not_ok h_c
        simp [h_err, bind, Except.bind] at h_ns

      obtain ⟨ns0, h_ns0⟩ := this
      simp [h_ns0] at h_ns
      simp [decidableGetElem?, hex_pair_to_byte!, h_b, h_ns, h2b!, h_s, h_t, h_ns0]



-- Example usage
example : h2b! "ff0022" = [255] ++ h2b! "0022" := by
  apply peel_2_from_h2b
  simp [is_ok, h2b_lc, hex_pair_to_byte, hex_nibble_to_byte, Except.bind, bind]
  simp [String.length]

  --hex_to_bytes "ff0022"
  --hex_to_bytes "0022"
  --hex_to_bytes "22"




example : h2b! "ff0022" = 255 :: h2b! "0022" := by
  have h_ok: is_ok (h2b "ff0022") := by
    conv in h2b _ =>
      simp only [h2b, h2b_lc, bind, Except.bind, hex_pair_to_byte, hex_nibble_to_byte, Char.toLower,
        ↓Char.isValue, Char.reduceToNat, ge_iff_le, Nat.reduceLeDiff, and_false, ↓reduceIte,
        decide_True, decide_False, Bool.and_false, Bool.false_eq_true, le_refl, Bool.and_self,
        Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, and_true, tsub_eq_zero_of_le, zero_mul, add_zero]
    simp only [is_ok, Except.ok.injEq, exists_eq']

  have h_len: "ff0022".data.length ≥ 2 := by
    simp only [↓Char.isValue, List.length_cons, List.length_singleton, Nat.succ_eq_add_one,
      Nat.reduceAdd, ge_iff_le, Nat.reduceLeDiff]

  apply peel_2_from_h2b
  assumption
  assumption





-- Define the custom syntax for the tactic
syntax (name := h2b!_peel_tactic) "h2b!_peel" : tactic

-- recursively search for `h2b! LITERAL` in the expression
def find_h2b!_lit_in_exp (e : Expr) : MetaM (Option String) := do
    match e with
    | Expr.app (.const `h2b! _) (.lit (.strVal s)) => return some s
    | Expr.app f a =>
      --logInfo m!"Expr.app: {f} {a}"
      let r1 ← find_h2b!_lit_in_exp f
      match r1 with
      | some s => return some s
      | none => find_h2b!_lit_in_exp a
    | Expr.lam _ _ b _ => find_h2b!_lit_in_exp b  -- Search in lambda body
    | Expr.letE _ _ v b _ =>
      -- Search in let binding and body
      return ← find_h2b!_lit_in_exp v <|> find_h2b!_lit_in_exp b
    | Expr.mdata _ b => find_h2b!_lit_in_exp b  -- Search in metadata body
    | Expr.proj _ _ b => find_h2b!_lit_in_exp b  -- Search in projections
    | _ => return none



@[tactic h2b!_peel_tactic]
def h2b!_peel_imp : Tactic := fun _ => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  --logInfo m!"Full goal type: {goalType}"

  match ← find_h2b!_lit_in_exp goalType with
  | none => throwError "Expected h2b! literal in the goal"
  | some s =>
    if s.length < 2 then
      throwError "h2b! string must have at least 2 characters"
    let rest := s.drop 2
    let first_byte := Syntax.mkNumLit (toString (hex_pair_to_byte! s.data[0]! s.data[1]!))

    Lean.Elab.Tactic.evalTactic (← `(tactic| have: h2b! $(Lean.Syntax.mkStrLit s) = $(first_byte) :: h2b! $(Lean.Syntax.mkStrLit rest) := by
      apply peel_2_from_h2b
      simp only  [is_ok, h2b, h2b_lc, bind, Except.bind, hex_pair_to_byte, hex_nibble_to_byte,
↓Char.isValue, Char.reduceToLower, Char.reduceToNat, ge_iff_le, Nat.reduceLeDiff, decide_True,
decide_False, Bool.and_false, Bool.false_eq_true, ↓reduceIte, le_refl, Bool.and_self,
Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, tsub_eq_zero_of_le, zero_mul, add_zero,
Except.ok.injEq, exists_eq']
      simp only [↓Char.isValue, List.length_cons, List.length_singleton, Nat.succ_eq_add_one,
Nat.reduceAdd, ge_iff_le, Nat.reduceLeDiff]
    ))
    Lean.Elab.Tactic.evalTactic (← `(tactic| rw [this] ))
    Lean.Elab.Tactic.evalTactic (← `(tactic| clear this ))


-- Example usage
example : h2b! "ff0022" = [255] ++ h2b! "0022" := by
  h2b!_peel
  simp


example : k = [255, 0, 34, 136, 25] → h2b! "ff00228819" = k := by
  intro h
  h2b!_peel
  h2b!_peel
  h2b!_peel
  h2b!_peel
  h2b!_peel
  simp [h, h2b!, h2b_lc]
