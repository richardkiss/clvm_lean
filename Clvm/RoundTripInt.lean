-- import Mathlib
import Mathlib.Tactic.Linarith
import Mathlib.Data.UInt

import Init.Data.ByteArray
import Init.Data.UInt
import Init.Prelude
import Init.Data.Fin
import Init.Data.Nat
import Init.Util
--import Init.Data.Nat.Lemmas

import Clvm.Atom
import Clvm.Basic
import Clvm.Casts
import Clvm.Coe
import Clvm.Hex
import Clvm.Node
import Clvm.Opcodes
import Clvm.Result
import Clvm.Run
import Clvm.Serde
import Clvm.Util


import Init.Data
import Init.Data.Nat.Bitwise
import Init.Tactics
import Init.Coe

import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Fin.Basic




section round_trip_int

/-
We now move to proving things about integers so we can show that `handle_op_add` etc. works right

The challenge is that we have to prove that the conversion from integers to atoms and back works right
Our ultimate goal in this section is to prove that `atom_to_int (int_to_atom z) = z`

`int_to_atom` is defined in terms of nat_to_atom, so let's first prove that `atom_to_nat (nat_to_atom x) = x`

We define an alternate version of `nat_to_atom` that's easier to reason about, and then prove it's
equivalent to the original
-/



def to_base_256_nl (n: Nat) (digits : Nat) : List Nat :=
  let next_digit := (n / (256 ^ digits))
  next_digit ::
    if digits > 0 then
      to_base_256_nl (n % 256^digits) (digits - 1)
    else
      []



def from_base_256_nl (acc : Nat) (l: List Nat): Nat :=
  match l with
  | [] => acc
  | x :: rest =>
      from_base_256_nl (x + acc * 256) rest



theorem from_base_to_base_round_trip (d: Nat) : ∀ n, ∀ m, from_base_256_nl m (to_base_256_nl n d) = n + m * 256 ^ (d+1) := by
  induction d with
  | zero =>
      unfold to_base_256_nl
      simp
      simp [from_base_256_nl]
  | succ d1 ih =>
      intro n0
      intro m0
      unfold to_base_256_nl
      have h1: Nat.succ d1 > 0 := by
        exact Nat.zero_lt_succ d1
      simp [h1]
      unfold from_base_256_nl
      -- this is a mess and I'm surprised simplification isn't more automatic
      have h2: from_base_256_nl (n0 / 256 ^ Nat.succ d1 + m0 * 256) (to_base_256_nl (n0 % 256 ^ Nat.succ d1) d1)  = (n0 % 256 ^ Nat.succ d1) + (n0 / 256 ^ Nat.succ d1 + m0 * 256) * 256 ^ (d1 + 1) := by
        exact ih (n0 % 256 ^ Nat.succ d1) (n0 / 256 ^ Nat.succ d1 + m0 * 256)
      rw [h2]
      have h_sd : Nat.succ d1 = d1 + 1 := by rfl
      have h3: n0 % 256 ^ Nat.succ d1 + n0 / 256 ^ Nat.succ d1 * 256 ^ Nat.succ d1 = n0 := by
        exact Nat.mod_add_div' n0 (256 ^ Nat.succ d1)

      have h_sub1: (n0 / 256 ^ Nat.succ d1 + m0 * 256) * 256 ^ (d1 + 1) = (n0 / 256 ^ Nat.succ d1) * 256 ^ (d1 + 1) + m0 * 256 * 256 ^ (d1 + 1) := by
        ring
      rw [h_sub1]

      have h_m0 : m0 * 256 * 256 ^ (d1 + 1) = m0 * 256 ^ (Nat.succ d1 + 1) := by
        rw [h_sd]
        ring

      rw [h_m0]
      have h_99 : n0 % 256 ^ Nat.succ d1 + (n0 / 256 ^ Nat.succ d1 * 256 ^ (d1 + 1) + m0 * 256 ^ (Nat.succ d1 + 1)) =
        n0 % 256 ^ Nat.succ d1 + n0 / 256 ^ Nat.succ d1 * 256 ^ (d1 + 1) + m0 * 256 ^ (Nat.succ d1 + 1) := by ring
      rw [h_99]
      rw [h3]



-- figure out how many digits we need to represent a number in base 256
def digits_for_nat_as_base_256 (n: Nat) : Nat :=
  if h256: n >= 256 then
    let n' := n / 256
    have hn : n' < n := by
      exact Nat.div_lt_self (by linarith) (by decide)
    1 + digits_for_nat_as_base_256 (n / 256)
  else
    1
termination_by n




-- we define a simpler version of nat_to_atom that's easier to reason about
def nat_to_list_nat (n: Nat) : List Nat :=
  let rec inner_func (n: Nat) : List Nat :=
    if h256: n > 256 then
      have h0: n > 0 := Nat.zero_lt_of_lt h256
      have : n >>> 8 < n := shift_decreasing h0
      (inner_func (n >>> 8)) ++  [n % 256]
    else
      [n]
  inner_func n

#eval nat_to_atom 65536
#eval digits_for_nat_as_base_256 65536

/-
theorem size_of_nat_to_atom : ∀ k, n > 0 → n ≤ k → (nat_to_atom n).size = digits_for_nat_as_base_256 n := by
  intro k
  intro n0
  intro h
  induction k with
  | zero =>
      linarith
  | succ k0 ih =>
      unfold digits_for_nat_as_base_256
      simp
      by_cases h256: 256 ≤ n
      simp [h256]
      simp [nat_to_atom]
      have hn0: ¬ n = 0 := by linarith
      simp [hn0]
      unfold nat_to_atom.inner_func
      simp [h256]
      unfold Array.size
      unfold List.length

      unfold nat_to_atom.inner_func
      unfold digits_for_nat_as_base_256
      by_cases ((n >>> 8) ≥ 256) with
      | true => sorry
      | false => sorry







      sorry

-/


def b256_digit (n k: Nat) : Nat :=
  let total_size := digits_for_nat_as_base_256 n
  (n / 256 ^ (total_size - 1 - k)) % 256


/-
lemma b256_digit_shifted (n k: Nat) : n ≥ 256 → b256_digit (n / 256) 0 = b256_digit n 0 :=
  let s1 := digits_for_nat_as_base_256 n
  let s2 := digits_for_nat_as_base_256 (n / 256)
  have hs: s1 = s2 + 1 := by sorry
  have hs1: digits_for_nat_as_base_256 n = digits_for_nat_as_base_256 (n / 256) + 1 := by
    rw [← hs]
  by
    intro h256
    unfold b256_digit
    simp
    rw [hs1]
    simp
    sorry
-/

#eval b256_digit (1000 / 256) 0
#eval b256_digit 1000 0
#eval b256_digit 256000 0


-- first, we find `nat_to_atom.size` in closed form
-- then, we write `b256_digit` in closed form
-- then we prove it matches `nat_to_atom`

-- (nat_to_atom n) = (nat_to_atom (n / 256)).extract 1 (nat_to_atom (n / 256)).size
-- so then we can use induction on `n` to show that `b256_digit` matches `nat_to_atom`
-- with the single extra case of the last digit treated specially


lemma nat_to_atom_inner_prefix: n ≥ 256 → (nat_to_atom.inner_func n) = (nat_to_atom.inner_func (n >>> 8)) ++ #[Nat.toUInt8 n] := by
  intro h_n
  conv_lhs => unfold nat_to_atom.inner_func
  simp
  have h1: 256 ≤ n := by linarith
  intro h_n1
  exfalso
  linarith



lemma extended_list_size: 1 + List.length a = List.length (a ++ [b]) := by
  induction a with
  | nil =>
    unfold List.length
    simp
  | cons head tail _ih =>
    unfold List.length
    simp
    ring



lemma extended_array_size: Array.size (a ++ #[b]) = 1 + Array.size a := by
  induction a.data with
  | nil =>
    unfold Array.size
    simp
    ring
  | cons head tail _ih =>
    unfold Array.size
    simp
    ring



theorem nat_to_atom_prefix: n ≥ 256 → (nat_to_atom n) = (nat_to_atom (n >>> 8)) ++ #[Nat.toUInt8 n] := by
  intro h_n
  unfold nat_to_atom
  have h1: ¬ n=0 := by linarith
  simp [h1]
  have h_256: n≥256 := by linarith
  have h_a: (nat_to_atom.inner_func n) = (nat_to_atom.inner_func (n >>> 8)) ++ #[Nat.toUInt8 n] := by
    exact nat_to_atom_inner_prefix h_256
  rw [h_a]
  have hs8: n >>> 8 > 0 :=
  calc
    n >>> 8 = n / (2 ^ 8) := Nat.shiftRight_eq_div_pow n 8
    _ = n / 256 := by ring_nf
    _ >= 256 / 256 := Nat.div_le_div_right h_256
    _ = 1 := by rfl
    _ > 0 := by linarith
  have hs9: ¬ n >>> 8 = 0 := by linarith
  simp [hs9]


lemma z: n < k → n / k = 0 := Nat.div_eq_of_lt


lemma nat_to_atom_size_increment: n>0 → (nat_to_atom n).size = (nat_to_atom (n >>> 8)).size + 1 := by
  intro h0
  by_cases h1: n ≥ 256
  have h_x: (nat_to_atom n) = (nat_to_atom (n >>> 8)) ++ #[Nat.toUInt8 n] := by
    exact nat_to_atom_prefix h1
  have h1: Array.size (nat_to_atom (n >>> 8) ++ #[Nat.toUInt8 n]) = 1 + Array.size (nat_to_atom (n >>> 8)) := by
    exact extended_array_size
  rw [h_x]
  rw [h1]
  ring

  unfold Array.size List.length
  unfold nat_to_atom
  have h_n0: ¬ n = 0 := by linarith
  unfold nat_to_atom.inner_func
  simp [h1]
  simp [h_n0]
  have h3: ¬ n ≥ 256 := by linarith
  have h4: n < 256 := by linarith

  have h5: n / 256 = 0 := Nat.div_eq_of_lt h4

  have h2: n>>>8 = 0 :=
    calc
      n>>>8 = n / (2 ^ 8) := Nat.shiftRight_eq_div_pow n 8
      _ = n / 256 := by ring_nf
      _ = 0 := by rw [h5]
  simp [h2]



lemma nat_to_atom_size: n < 256 ^ k → n > 0 → (nat_to_atom n).size = digits_for_nat_as_base_256 n := by
  induction k with
  | zero =>
      intro h1 h2
      have h3: 256 ^ Nat.zero = 1 := by rfl
      rw [h3] at h1
      linarith
  | succ k0 ih =>
      intro h1 h2
      have h3: n < 256 * 256 ^ k0 := by ring_nf; exact h1
      by_cases h4: n ≥ 256

      let n1 := n >>> 8
      have h_n1_r: n1 = n >>> 8 := by rfl
      unfold digits_for_nat_as_base_256
      simp [h4]
      have h5: Array.size (nat_to_atom n) = (nat_to_atom (n >>> 8)).size + 1 := by
        exact nat_to_atom_size_increment h2
      rw [h5]
      have h_n1_0: n / 256 = n1 := by
        calc
          n / 256 = n / 2 ^ 8 := by ring_nf
          _ = n >>> 8 := by rw [Nat.shiftRight_eq_div_pow n 8]
          _ = n1 := by rfl
      have h_n1 : n1 < 256 ^ k0 := by
        calc
          n1 = n / 256 := by rw [h_n1_0]
          _ < (256 ^ Nat.succ k0) / 256 := by sorry
          _ = 256 ^ k0 := by sorry
      rw [← h_n1_r]
      rw [← h_n1_0]
      have h6: n > 0 → Array.size (nat_to_atom n) = digits_for_nat_as_base_256 n := by sorry
      by_cases h7: n>0
      have h8: Array.size (nat_to_atom (n/256)) = digits_for_nat_as_base_256 (n/256) := by sorry
      rw [h8]
      ring

      exfalso
      exact h7 h2

      have h9: n ≤ 255 := by linarith
      unfold digits_for_nat_as_base_256
      simp [h4]
      unfold nat_to_atom Array.size
      simp
      have hn0 : ¬ n = 0 := by linarith
      simp [hn0]
      unfold nat_to_atom.inner_func
      simp [h4]



def n0 := 1000000000000000
def k0 := 2

#eval b256_digit n0 0
#eval b256_digit (n0 / 256)  0


lemma some_power_thing { n m d : Nat } : n / m / (m ^ d) = n / m ^ (d + 1) := by
  calc
    n / m / (m ^ d) = n / (m * (m ^ d)) := by exact Nat.div_div_eq_div_mul n m (m ^ d)
    _ = n / (m ^ (d + 1)) := by ring_nf
    _ = n / m ^ (d + 1) := by rfl


lemma some_power_thing_2 { n m a b : Nat } : n / (m ^ a) / (m ^ b) = n / m ^ (a + b) := by
  ring_nf
  exact Nat.div_div_eq_div_mul n (m ^ a) (m ^ b)



lemma b256_digit_prefix: k < digits_for_nat_as_base_256 (n / 256) → (b256_digit n k) = (b256_digit (n / 256) k) := by
  intro k0
  unfold b256_digit
  simp
  have h1: digits_for_nat_as_base_256 n = digits_for_nat_as_base_256 (n / 256) + 1 := by
    sorry
  rw [h1]
  ring_nf
  simp
  have h2: n / 256 / 256 ^ (digits_for_nat_as_base_256 (n / 256) - k - 1) = n / 256 ^ (digits_for_nat_as_base_256 (n / 256) - k) := by
    sorry
    -- exact some_power_thing_2 n 256 (digits_for_nat_as_base_256 256 1 (digits_for_nat_as_base_256 (n / 256) - k - 1))
  have h3: n / 256 / 256 ^ (digits_for_nat_as_base_256 (n / 256) - 1 - k) =  n / 256 ^ (digits_for_nat_as_base_256 (n / 256) - k) := by
    calc
      n / 256 / 256 ^ (digits_for_nat_as_base_256 (n / 256) - 1 - k) = n / 256 / 256 ^ (digits_for_nat_as_base_256 (n / 256) - k - 1) := by sorry
      _ = n / 256 ^ (digits_for_nat_as_base_256 (n / 256) - k) := by exact h2
  rw [← h3]



lemma int_to_atom_of_nat { u : UInt8 } { z : Int } : (z > 0) → int_to_atom z = (nat_to_atom z.natAbs) ∨ (int_to_atom z) = (#[(0: UInt8)] ++ (nat_to_atom z.natAbs)) := by
  intro hz

  by_cases h1 : ((nat_to_atom z.natAbs)[0]? = some u) → (u &&& 128 = 0)

  unfold int_to_atom
  have hn: ¬ z < 0 := by linarith
  simp [hn]
  unfold getElem?
  simp







  have h3: int_to_atom z.natAbs = #[] := by
    rw [h2]
    rfl
  rw [h2]
  simp [nat_to_atom]
  simp [int_to_atom]
  unfold getElem?
  simp [nat_to_atom]
  simp






  have h4: nat_to_atom n = #[] := by

    unfold int_to_atom
    simp [h2]



  unfold int_to_atom
  unfold nat_to_atom
  unfold nat_to_atom.inner_func
  simp
  rfl





theorem round_trip_int (n: Nat) : atom_to_int (int_to_atom n) = n := by
    by_cases hn: n = 0
    simp [hn]
    simp [int_to_atom, atom_to_int, nat_to_atom]
    rfl
    have h1: n > 0 := by sorry


      simp [Int.ofNat]
      unfold Nat.cast NatCast.natCast instNatCastInt Int.ofNat
      simp

      simp [int_to_atom]









      simp [Int.ofNat]
      unfold int_to_atom


      simp [int_to_atom]
      cases n with
      | zero =>
          simp

          unfold atom_to_int
          simp


          simp
          rfl
      | succ n =>
          simp
          simp [nat_to_atom]
          unfold nat_to_atom.inner_func
          have h1: ¬ n+1 < 0 := by linarith
          sorry
  | negSucc n => sorry







theorem zz: ∀ n>0, ∀ k, (h: k < (nat_to_atom n).size) → (nat_to_atom n)[k] = b256_digit n k := by
  intro n0
  intro h0
  intro k0
  induction k0 with
  | zero =>
      intro h1
      simp
      unfold b256_digit
      simp

      unfold nat_to_atom
      have hn0: ¬ n0 = 0 := by linarith
      simp [hn0]
      unfold nat_to_atom.inner_func


      sorry
  | succ k0 ih =>
      sorry




#help tactic rw

theorem b256_digit_nat_to_list_nat : ∀ m, ∀ n, (a = nat_to_atom n) → (m > a.size) → (h: k < a.size) → (b256_digit n (a.size - 1 - k) = a[k].toNat) := by
  intro m0
  intro n0
  intro h1
  intro h2
  induction m0 with
  | zero =>
      simp at h2
  | succ n ih =>
      -- idea: check the last digit matches
      -- then, with n0 = n/256 show that the rest matches using induction hypothesis
      let last_k := a.size - 1
      by_cases h3: k = a.size - 1
      simp [h1]
      by_cases h4: n0 = 0
      sorry

      unfold nat_to_atom.inner_func
      have ha: a.size = 0 := by
        rw [h1]
        simp [nat_to_atom, h4]
      rw [ha] at h3
      linarith

      rw [h1]
      unfold nat_to_atom
      unfold nat_to_atom.inner_func
      simp [h4]
      by_cases h5: 256 ≤ n0


      sorry






theorem eq1 : nat_to_list_nat n = to_base_256_nl n (digits_for_nat_as_base_256 n) := by
  by_cases h: n > 256
  have h1: digits_for_nat_as_base_256 n > 2 := by
    simp [digits_for_nat_as_base_256, h]
    rfl
  unfold to_base_256_nl
  simp
  unfold nat_to_list_nat
  unfold nat_to_list_nat.inner_func
  simp
  simp [h]



  unfold digits_for_nat_as_base_256

  induction' n using digits_for_nat_as_base_256 with
    | zero => rfl
    | succ n ih =>
      unfold digits_for_nat_as_base_256
      unfold nat_to_list_nat
      unfold to_base_256_nl
      have h1: n > 256 := by
        exact h
      have h2: n / 256 < n := by
        exact Nat.div_lt_self (by linarith) (by decide)
      have h3: n % 256 = n - (n / 256) * 256 := by
        exact Nat.mod_eq_of_lt h2
      have h4: n >>> 8 = n / 256 := by rfl
      have h5: n % 256 = n - (n >>> 8) * 256 := by
        rw [h4]
        rw [h3]
      have h6: nat_to_list_nat (n >>> 8) = to_base_256_nl (n >>> 8) (digits_for_nat_as_base_256 (n >>> 8)) := by
        exact ih
      rw [h6]
      rw [h5]
      rfl
  simp [nat_to_list_nat, nat]

  cases h: (n > 256) with
  | true =>
    sorry
  | false =>
    sorry




def to_array_nat (k : Atom) : Array Nat := k.map (fun x => x.toNat)


lemma nat_to_list_nat_eq_nat_to_atom (n: Nat) : (nat_to_list_nat n).toArray = to_array_nat (nat_to_atom n) := by
  cases n > 256 with
  | nil =>
      sorry
  | cons head tail => sorry



#eval to_base_256_nl 1 ((log_256 1) - 1)


-- this will be tough to prove. Maybe we can induct on `log_256 (n+1)`.
-- Base case should be easy since we just check it.
-- Then we split n into the part that's too big (which will be just one digit) and the rest.
-- The tricky part is that `nat_to_atom` recurses on the wrong side


theorem nat_to_atom_is_to_base256 : ∀ n, to_list_nat (nat_to_atom (n + 1)) = to_base_256_nl (n + 1) ((log_256 (n + 1) - 1)) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>

     sorry




-- this one is very difficult so we'll punt for now
theorem round_trip_int { z: Int } : atom_to_int (int_to_atom z) = z := by
  sorry




-- node_list_to_node ∘ int_list_to_node_list) [z])

def t1 : Node → (Node → NResult Int) → NResult (List Int) := node_to_list
def t2 := node_to_list ( α := Int )


#check node_to_list ( α := Int )
#check t1
#check t2
#print t2
#eval node_to_list_int (Node.pair (Node.atom (int_to_atom 0)) Node.nil) atom_to_int_cast



lemma h_lemma1 { a: Atom } : node_to_list (Node.pair (Node.atom (int_to_atom z)) Node.nil) atom_to_int_cast = NResult.ok [z] := by

  have h_no_err { a: Atom } : atom_to_int_cast a = NResult.ok (atom_to_int a) := by rfl
  have h_nil_node : node_to_list Node.nil atom_to_int_cast = NResult.ok [] := by rfl
  have h_atoi : atom_to_int_cast (Node.atom (int_to_atom z)) = NResult.ok (atom_to_int (int_to_atom z)) := by rfl

  delta node_to_list
  unfold Node.below

  sorry




lemma h_lemma { a: Atom } : node_to_list_int (Node.pair (Node.atom (int_to_atom z)) Node.nil) atom_to_int_cast = NResult.ok [z] := by
  have h_nil_node : node_to_list Node.nil atom_to_int_cast = NResult.ok [] := by rfl
  have h_atoi : atom_to_int_cast (Node.atom (int_to_atom z)) = NResult.ok (atom_to_int (int_to_atom z)) := by rfl

  simp [node_to_list_int, h_atoi, round_trip_int, h_nil_node]


theorem try_args_to_int_singleton_val { z: Int }: args_to_int [z] = NResult.ok [z] := by
  simp [int_list_to_node_list, node_list_to_node]
  unfold args_to_int
  apply h_lemma
  exact #[]




  --unfold node_to_list[Int]









#eval handle_op_add [100]

theorem op_add_one_number { z: Int } : handle_op_add [z] = Result.ok (Node.atom (int_to_atom z)) := by
  simp [int_list_to_node_list, node_list_to_node, handle_op_add, args_to_int]



  sim
  unfold handle_op_add
  unfold args_to_int
  unfold node_to_list
  rw [node_to_node_list_terminator_rewrite]
  simp [rightmost_node]
  simp [alt_node_to_node_list_terminator_without_terminator]






















theorem run_add_one_number { z: Int } : apply add_example_nodes (int_to_atom z) = Result.ok (Node.atom (int_to_atom z)) := by
  simp [apply, add_example_nodes]
  unfold apply_node
  cases z with
  |





/-
theorem round_trip_nat { x: Nat } : atom_to_nat (nat_to_atom x) = x := by
  unfold nat_to_atom
  unfold atom_to_nat
  unfold nat_to_atom.inner_func
  cases x
  rfl
  simp
  unfold nat_to_atom.inner_func
-/






theorem run_add_x_is_x { x: Nat } : apply (Node.pair OP_ADD (Node.pair (int_to_atom x) 0)) Node.nil = Result.ok (Node.atom (int_to_atom x)) := by
  simp [apply]
  unfold apply_node
  have h: ¬ 100 = 0 := by decide
  unfold apply_node
  unfold map_or_err
  unfold as_list
  unfold Array.size
  unfold List.length
  sorry


/-
TACTICS:

intro
apply
exact
induction

unfold
split
have
simp
rw
refine
cases

convert

? rintro

https://notabug.org/LinusTuring/lean4/src/master/doc/tactics.md


-/


def add_example : Node := [OP_ADD.toNat, 1, 0]

def add_example_nodes : Node := Node.pair (Node.atom #[OP_ADD]) (Node.pair (Node.atom #[1]) (Node.atom #[]))

theorem try_args_to_int_empty : args_to_int Node.nil = NResult.ok [] := by
  rfl


theorem try_args_to_int_singleton_0  : args_to_int [0] = NResult.ok [0] := by
  rfl

theorem try_args_to_int_singleton_1  : args_to_int [1] = NResult.ok [1] := by
  rfl
