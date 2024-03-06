import Mathlib.Data.Nat.Prime
import Mathlib.Data.ZMod.Basic


structure Curve where
  p: Nat
  is_prime: Nat.Prime p
  a: ZMod p
  b: ZMod p
  deriving Repr
