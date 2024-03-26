-- goals:
-- show that our simplest formula for getting the nth digit of a number in base b is correct
--
-- show that the round-trip works, ie. is idempotent
--
-- prove that our more efficient mechanism to generate the digits of a number in base b matches
--  the simple mechanism
--

import Mathlib

set_option maxHeartbeats 2000000

def BASE := 10
def B: BASE > 1 := by decide



def nth_digit_of_nat_in_base_b_le {b : Nat} (n: Nat) (v: Nat) (_: b>1) : Nat :=
  (v / (b ^ n)) % b



def nat_to_base_b_le {b: Nat} (v: Nat) (hb: b>1): List Nat :=
    if _: v ≥ b then
      let new_v := v/b
      have _: v/b < v := by exact Nat.div_lt_self (by linarith) hb
      (v % b) :: nat_to_base_b_le new_v hb
    else
      [v]


def base_b_le_to_nat (ds: List Nat) (b: Nat) : Nat :=
  match ds with
  | [] => 0
  | d :: tail =>
      d + b * base_b_le_to_nat tail b



theorem round_trip_le_base { b : Nat } {hb : b > 1} : ∀ k, ∀ v, v < b ^ k → base_b_le_to_nat (nat_to_base_b_le v hb) b = v := by
  intro k0
  have h1: ¬ b = 0 := by linarith
  induction k0 with
  | zero =>
    intro v0
    intro h0
    simp at h0
    simp [h0]
    unfold nat_to_base_b_le
    simp [hb, h1]
    rfl
  | succ n ih =>
    intro v0
    intro h0
    unfold nat_to_base_b_le
    have hb0: b > 0 := by linarith
    have h4: v0 / b < b^n := by
      simp [Nat.nat_repr_len_aux v0 b n hb0 h0]

    have h5: base_b_le_to_nat (nat_to_base_b_le (v0/b) hb) b = v0 / b := by
      exact ih (v0/b) h4
    simp
    unfold base_b_le_to_nat
    by_cases h2: v0 ≥ b
    simp [h2]
    simp [h5]
    exact Nat.mod_add_div v0 b
    simp [h2]
    unfold base_b_le_to_nat
    simp


theorem round_trip_le { b : Nat } {hb : b > 1} : base_b_le_to_nat (nat_to_base_b_le v hb) b = v := by
  have h1: ∃ k, v < b ^ k := by
    use (v + v)
    induction v with
    | zero => simp
    | succ v1 ih =>
        have h2: b ^ (v1 + v1) < b ^ (Nat.succ v1 + Nat.succ v1) := by
          refine (Nat.pow_lt_pow_iff_right hb).mpr ?_
          linarith
        have h3: Nat.succ v1 ≤ b ^ (v1 + v1) := by linarith
        linarith
  obtain ⟨k, h2⟩ := h1
  exact round_trip_le_base k v h2



def base_b_be_to_nat (ds: List Nat) (b: Nat) : Nat :=
  base_b_le_to_nat ds.reverse b


def nat_to_base_b_be (v: Nat) {b: Nat} (hb: b>1): List Nat :=
  (nat_to_base_b_le v hb).reverse


theorem round_trip_be { b : Nat } {hb : b > 1} : base_b_be_to_nat (nat_to_base_b_be v hb) b = v := by
  unfold nat_to_base_b_be
  unfold base_b_be_to_nat
  rw [List.reverse_reverse]
  exact round_trip_le







theorem general_round_trip { f: List Nat → Nat} { g: Nat → List Nat } : g (f []) = [] → (∀ as, (g (f as) = as) → (∀ a0, g (f (a0 :: as)) = a0 :: as)) → ∀ v, g (f v) = v := by
  intro h0
  intro h1
  intro v
  induction v with
  | nil => assumption
  | cons head tail ih => simp [h1 tail ih]




theorem general_equality { f: α → β } { g: α → β } { p: α → (α × α) } {s : (β × β) → β} { m : α → Nat }
    -- g is some function
    -- f is a function we're trying to prove equals g
    -- m is a "measure" function on α
    -- p is a "partition" function, which splits p into a list, each of which has strictly smaller measure than the original
    -- s is a "sum" function which sums the outputs of f applied to each partition
    -- the idea is: is f matches g on each α of measure zero, and we can partition f into parts of strictly smaller measure, and the sum of the outputs of f on each partition matches g, then f = g,
    --  without affecting the value of f, then f has to match g everywhere
    (hp: ∀ a, (m (p a).1 ≤ m a - 1 ∧ m (p a).2 ≤  m a - 1)) -- the partition function reduces measure towards zero
    (h0: ∀ a, m a = 0 → f a = g a ) -- f matches g on measure zero
    (h1: ∀ a0, (s ⟨f (p a0).1, f (p a0).2⟩) = f a0)
    (h2: ∀ a0, (s ⟨g (p a0).1, g (p a0).2⟩) = g a0)
      -- if p and s "work" on f, ie. you can partition a0 into smaller measure, apply f to the partition elements, then sum with s
    -- the proof is, roughly choose an a in α and keep paritioning and summing until all terms are of measure 0,
    -- where things work by assumption
    : f = g := by
      refine funext ?a
      intro a0
      have hxxz: ∀ k0, ∀ a, (m a ≤ k0) → (f a = g a) := by
        intro k0
        induction k0 with
        | zero =>
          intro a
          intro ha
          have hm0 : m a = 0 := by
            linarith
          exact h0 a hm0
        | succ n ih =>
            intro a
            intro hma
            rw [← h1]
            rw [← h2]
            have hhh: m (p a).1 ≤ m a - 1 ∧ m (p a).2 ≤ m a - 1 := by exact hp a
            have hmpa1 : m (p a).1 ≤ n := by
              have hhh1: m (p a).1 ≤ m a - 1 := hhh.1
              have hma1n: m a - 1 ≤ n := by simp [hma]
              linarith
            have hmpa2 : m (p a).2 ≤ n := by
              have hhh1: m (p a).2 ≤ m a - 1 := hhh.2
              have hma1n: m a - 1 ≤ n := by simp [hma]
              linarith
            have hfg1 : f (p a).1 = g (p a).1 := by exact ih (p a).1 hmpa1
            have hfg2 : f (p a).2 = g (p a).2 := by exact ih (p a).2 hmpa2
            rw [hfg1, hfg2]
      exact hxxz (m a0) a0 (by linarith)



def nth_digit_of_nat_in_base_b {b : Nat} (n: Nat) (v: Nat) (hb: b>1) : Nat :=
  nth_digit_of_nat_in_base_b_le  (Nat.clog b v - 1 - n) v hb


def nat_to_base_b {b: Nat} (v: Nat) (hb: b>1): List Nat :=
  (nat_to_base_b_le v hb).reverse


#eval nat_to_base_b 239398 B


def base_b_to_nat (ds: List Nat) (b: Nat) : Nat :=
  match ds with
  | [] => 0
  | d :: tail =>
      b ^ tail.length * d + base_b_to_nat tail b



def N := 2006
#eval Nat.clog BASE N
#eval nth_digit_of_nat_in_base_b 3 N B


#eval base_b_to_nat [1, 2, 3, 4, 9] 10


def nat_to_base_b_acc (v: Nat) (acc: List Nat) (hb: b>1): List Nat :=
    if h1: v > 0 then
      let new_v := v/b
      have _: v/b < v := by exact Nat.div_lt_self h1 hb
      nat_to_base_b_acc new_v ((v % b) :: acc) hb
    else
      acc


def base_b_to_nat_acc (ds: List Nat) (b: Nat) (acc: Nat) : Nat :=
  match ds with
  | [] => acc
  | d :: ds' =>
    base_b_to_nat_acc ds' b (acc * b + d)


def d := 10
def ds := [1, 2, 3, 4]
def b := 10
def acc := 948

#eval base_b_to_nat_acc (d :: ds) b acc = base_b_to_nat_acc ds b (acc * b + d * b ^ ds.length)


lemma base_b_to_nat_acc_incremental {acc b d: Nat} {ds: List Nat}: (base_b_to_nat_acc (d :: ds) b acc  = base_b_to_nat_acc ds b (acc * b + d)) := by
    conv_lhs => unfold base_b_to_nat_acc

lemma xxx: 2 < 3 := by linarith

def n0 := 239398
def h1: b > 1 := by decide
#eval base_b_to_nat_acc (nat_to_base_b_acc (n0/b) [] h1) b 0
