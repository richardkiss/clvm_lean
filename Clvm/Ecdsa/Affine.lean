import Mathlib.Data.ZMod.Basic


import Clvm.Ecdsa.Curve



structure AffinePointNotInfinity ( curve: Curve ) where
  x : ZMod curve.p
  y : ZMod curve.p
  proof :  y ^ 2 - x ^ 3 - curve.a * x - curve.b = 0
  deriving Repr


inductive AffinePoint ( curve: Curve ) where
  | mk : AffinePointNotInfinity curve → AffinePoint curve
  | infinity : AffinePoint curve
  deriving Repr
