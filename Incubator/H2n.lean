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



@[simp]
lemma string_drop {s: String}: s.drop n = String.mk (s.data.drop n) := by
  ext n0 c
  simp only [String.data_drop]


-- write a tactic `h2b_peel_2` that peels off the first two characters of a hex string



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


/-
-- Define the custom syntax for the tactic
syntax (name := hexToBytesTactic) "hex_to_bytes" term : tactic





-- Define the evaluation function for the custom tactic
@[tactic hexToBytesTactic]
def evalHexToBytes : Tactic := fun stx =>
  match stx with
  | `(tactic| hex_to_bytes $str) => do
    -- Access the raw syntax of the string literal
    let hexStr ← match str.raw.isStrLit? with
    | some s => pure s
    | none => throwError "hex_to_bytes tactic requires a string literal"

    -- Convert the hex string to a list of bytes
    let bytes := h2b! hexStr
    -- Create an expression for the list of bytes
    let bytesExpr : Expr := bytes.foldr (fun b acc =>
      mkApp (mkApp (mkApp (mkConst ``List.cons [Level.zero]) (mkConst ``UInt8)) (mkApp (mkConst ``UInt8.ofNat) (mkNatLit b))) acc)
      (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``UInt8))
    -- Close the main goal with the generated expression
    Lean.Elab.Tactic.closeMainGoal bytesExpr
  | _ => throwError "Unsupported syntax"


-- Example usage
example : h2b! "ff0022" = [255] ++ h2b! "0022" := by
  hex_to_bytes "ff0022"


-- Example functions for hex conversion
def h2b (s : String) : List UInt8 :=
  let rec aux (i : Nat) (acc : List UInt8) :=
    if i + 1 < s.length then
      let byte := hex_to_byte (s.get i) (s.get (i + 1))
      aux (i + 2) (acc ++ [byte])
    else
      acc
  aux 0 []

def hex_to_byte (c1 c2 : Char) : UInt8 :=
  let d1 := if '0' ≤ c1 ∧ c1 ≤ '9' then c1.toNat - '0'.toNat
            else if 'a' ≤ c1 ∧ c1 ≤ 'f' then c1.toNat - 'a'.toNat + 10
            else if 'A' ≤ c1 ∧ c1 ≤ 'F' then c1.toNat - 'A'.toNat + 10
            else panic! "Invalid hex character"
  let d2 := if '0' ≤ c2 ∧ c2 ≤ '9' then c2.toNat - '0'.toNat
            else if 'a' ≤ c2 ∧ c2 ≤ 'f' then c2.toNat - 'a'.toNat + 10
            else if 'A' ≤ c2 ∧ c2 ≤ 'F' then c2.toNat - 'A'.toNat + 10
            else panic! "Invalid hex character"
  UInt8.ofNat (d1 * 16 + d2)

-- Example usage
example : h2b "ff0022" = [255] ++ h2b "0022" := by
  hex_to_bytes "ff0022"

example : List UInt8 :=
by
  hex_to_bytes "ff0022"





syntax (name := hexToBytesTactic) "hex_to_bytes" term : tactic

set_option pp.rawOnError true

variable (stx: Syntax)
#check stx

variable (tstx: TSyntax α)
#check tstx.raw[0].isStrLit?

@[tactic hexToBytesTactic]
def evalHexToBytes : Tactic := fun stx =>
  do
  --logInfo m!"received syntax: {stx}"
  match stx with
  | `(tactic| hex_to_bytes $str) =>
    --logInfo m!"received str: {str}"
    --logInfo m!"str.raw: {str.raw}"
    --logInfo m!"str.raw[0]: {str.raw[0]}"
    --logInfo m!"str.raw.isStrLit?: {str.raw.isStrLit?}"
    match str.raw.isStrLit? with
    | some hexStr =>
      -- Convert the hex string to a list of bytes
      --logInfo m!"hexStr: {hexStr}"
      let bytes := h2b! hexStr
      -- Create an expression for the list of bytes
      let bytesExpr := bytes.foldr (fun b acc =>
        mkApp (mkApp (mkApp (mkConst ``List.cons [levelZero]) (mkConst ``UInt8)) (mkApp (mkConst ``UInt8.ofNat) (mkNatLit b))) acc)
        (mkApp (mkConst ``List.nil [levelZero]) (mkConst ``UInt8))
      -- Close the main goal with the generated expression
      Lean.Elab.Tactic.closeMainGoal bytesExpr
    | none => throwError "hex_to_bytes tactic requires a string literal"
  | _ => throwError "Unsupported syntax"



example : List UInt8 :=
by
  hex_to_bytes "ff0022"



example : h2b! "ff0022" = [255] ++ h2b! "0022" := by

  hex_to_bytes "ff0022"


---







lemma node_serde_round_trip: h2n! (n2h n) = n := by
  sorry



lemma h2n!_ff (s: String) (h: s.take 2 = "ff") (h_ok: is_ok (h2n s)): h2n! s = Node.pair (h2n_first! (s.drop 2)) (h2n! (n2h (h2n_second! (s.drop 2)))) := by

  obtain z := h2n!_split s h_ok h
  rw [z]

  have: s.drop 2 = String.mk (s.data.drop 2) := by
    ext n a : 3
    simp_all only [String.data_drop, List.get?_drop, Option.mem_def]

  simp [this]
  simp [node_serde_round_trip]



def s := "ff01ff02ff03ff0480"


def n := h2n! s

#check n
#eval n


example: h2n! "ff01ff02ff03ff0480" = Node.pair (Node.atom (Atom.mk [1] (by decide))) (h2n! "ff02ff03ff0480") := by

  let s := "ff01ff02ff03ff0480"

  have h : is_ok (h2n s) := by
    simp only [h2n, bind, Except.bind, h2n_parsed_node, h2b_lc, hex_pair_to_byte,
      hex_nibble_to_byte, ↓Char.isValue, Char.reduceToLower, Char.reduceToNat, ge_iff_le,
      Nat.reduceLeDiff, decide_True, decide_False, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      le_refl, Bool.and_self, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, tsub_eq_zero_of_le,
      zero_mul, zero_add, add_zero, bytes_to_parsed_node, OfNat.one_ne_ofNat, bytes_to_atom,
      MAX_SINGLE_BYTE, Nat.one_le_ofNat, Nat.reduceEqDiff, Node.nil, pure, Except.pure]
    simp only [is_ok, Except.ok.injEq, exists_eq']

  rw [h2n!_ff s (by rfl) h]

  simp only [h2n_first!]

  simp only [n2h, h2n_parsed_node!, h2n_parsed_node, bind, Except.bind, h2b_lc,
    hex_pair_to_byte, hex_nibble_to_byte, Char.toLower, ↓Char.isValue, Char.reduceToNat, ge_iff_le,
    Nat.reduceLeDiff, and_true, ↓reduceIte, le_refl, decide_True, Bool.and_self, tsub_eq_zero_of_le,
    Nat.reduceSub, zero_mul, zero_add, and_false, decide_False, Bool.and_false, Bool.false_eq_true,
    Nat.reduceMul, Nat.reduceAdd, add_zero, bytes_to_parsed_node, OfNat.one_ne_ofNat, bytes_to_atom,
    MAX_SINGLE_BYTE, Nat.one_le_ofNat, pure, Except.pure, s, Node.pair.injEq]

  simp only [node_to_bytes, atom_to_serialized_bytes, atom_cast, List.map_cons, max_255,
    Nat.one_le_ofNat, ↓reduceIte, List.map_nil, List.length_singleton, Nat.reduceBEq,
    Bool.false_eq_true, beq_self_eq_true, getElem!, zero_lt_one, ↓reduceDite, Fin.zero_eta,
    Fin.isValue, List.get_cons_zero, MAX_SINGLE_BYTE, and_self]

  simp only [true_and]

  -- that takes care of the first part of the pair




  conv in b2h [1] =>
    simp [b2h, String.join, nat_to_hex]

  --simp






  have s2: h2n_second! (s.drop 2) = h2n! "ff02ff03ff0480" := by
    simp [h2n_second!]
    simp [h2n_second]
    simp [h2n_parsed_node!, h2n_parsed_node, h2b_lc, hex_pair_to_byte, hex_nibble_to_byte,
      Char.toLower, Char.ofNat, Nat.isValidChar, pure, Except.pure, bytes_to_parsed_node,
      bytes_to_atom, MAX_SINGLE_BYTE, bind, Except.bind]

    simp [h2n!, h2n, h2n_parsed_node, h2b_lc, hex_pair_to_byte, hex_nibble_to_byte,
      Char.toLower, Char.ofNat, Nat.isValidChar, pure, Except.pure, bytes_to_parsed_node,
      bytes_to_atom, MAX_SINGLE_BYTE, bind, Except.bind]

  rw [s2]


  sorry



----
-- from chat gpt


#eval h2b "f0"

-/





-- Define the custom syntax for the tactic
syntax (name := h2n!_peel_tactic) "h2n!_peel" : tactic

-- recursively search for `h2b! LITERAL` in the expression
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

    let t1 := ← `(tactic| have: h2n! $(Lean.Syntax.mkStrLit s) = Node.pair (h2n_first! $(Lean.Syntax.mkStrLit rest))  (h2n_second! $(Lean.Syntax.mkStrLit rest)) := by
      apply h2n!_split
      simp [h2n, is_ok, bind, Except.bind, h2n_parsed_node,
        h2b_lc, hex_pair_to_byte, hex_nibble_to_byte, bytes_to_parsed_node,
        bytes_to_atom, Except.err, MAX_SINGLE_BYTE, pure, Except.pure]
      rfl
    )
    --logInfo m!"t1: {t1}"
    Lean.Elab.Tactic.evalTactic (← `(tactic| have: h2n! $(Lean.Syntax.mkStrLit s) = Node.pair (h2n_first! $(Lean.Syntax.mkStrLit rest))  (h2n_second! $(Lean.Syntax.mkStrLit rest)) := by
      apply h2n!_split
      simp only [is_ok, h2n, bind, Except.bind, h2n_parsed_node, h2b_lc, hex_pair_to_byte,
    hex_nibble_to_byte, ↓Char.isValue, Char.reduceToLower, Char.reduceToNat, ge_iff_le,
    Nat.reduceLeDiff, decide_True, decide_False, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
    le_refl, Bool.and_self, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, tsub_eq_zero_of_le,
    zero_mul, add_zero, bytes_to_parsed_node, OfNat.zero_ne_ofNat, bytes_to_atom, MAX_SINGLE_BYTE,
    zero_le, Nat.reduceEqDiff, pure, Except.pure, Except.ok.injEq, exists_eq']

      simp only [substring_take, ↓Char.isValue, List.take_cons_succ, List.take_zero, String.reduceMk]
    ))
    Lean.Elab.Tactic.evalTactic (← `(tactic| rw [this] ))
    Lean.Elab.Tactic.evalTactic (← `(tactic| clear this ))



example : h2n! "ff0022" = Node.pair (h2n_first! "0022")  (h2n_second! "0022") := by
  apply h2n!_split

  simp only [is_ok, h2n, bind, Except.bind, h2n_parsed_node, h2b_lc, hex_pair_to_byte,
    hex_nibble_to_byte, ↓Char.isValue, Char.reduceToLower, Char.reduceToNat, ge_iff_le,
    Nat.reduceLeDiff, decide_True, decide_False, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
    le_refl, Bool.and_self, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, tsub_eq_zero_of_le,
    zero_mul, add_zero, bytes_to_parsed_node, OfNat.zero_ne_ofNat, bytes_to_atom, MAX_SINGLE_BYTE,
    zero_le, Nat.reduceEqDiff, pure, Except.pure, Except.ok.injEq, exists_eq']

  simp only [substring_take, ↓Char.isValue, List.take_cons_succ, List.take_zero, String.reduceMk]



example : h2n! "ff8022" = Node.pair 0 34 := by
  h2n!_peel

  simp only [Node.pair.injEq]

  constructor

  simp [h2n_first!, h2n_parsed_node!, h2n_parsed_node, h2b_lc, hex_pair_to_byte, hex_nibble_to_byte,
    Except.pure, pure, bind, Except.bind, bytes_to_parsed_node, bytes_to_atom, MAX_SINGLE_BYTE]

  unfold OfNat.ofNat Node.instOfNat int_to_atom int_to_twos_comp
  simp [Int.ofNat]


  simp [h2n_second!, h2n_second, h2n_parsed_node, h2b_lc, hex_pair_to_byte, hex_nibble_to_byte,
    Except.pure, pure, bind, Except.bind, bytes_to_parsed_node, bytes_to_atom, MAX_SINGLE_BYTE]

  simp [atom_cast, max_255]
  simp [OfNat.ofNat]
  simp [small_int_to_atom]




example : h2n! "ff0022" = Node.pair (h2n_first! "0022") (h2n_second! "0022") := by
  apply h2n!_split
  simp [h2n, is_ok, bind, Except.bind, h2n_parsed_node, h2b_lc, hex_pair_to_byte, hex_nibble_to_byte,
    bytes_to_parsed_node, bytes_to_atom, Except.err, MAX_SINGLE_BYTE, pure, Except.pure]
  exact Eq.refl ("ff0022".take 2)



--#lint
