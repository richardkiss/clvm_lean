import Mathlib.Data.ZMod.Basic


import Clvm.Ecdsa.Curve

/-!
This file creates the `AffinePoint` structure, which represents a point on an elliptic curve.

There are two cases: `AffinePoint.infinity` and `AffinePoint.mk ap`, where `ap` is a `FiniteAffinePoint`.
-/


/--
A non-infinity affine point, with x and y coordinate
-/
structure FiniteAffinePoint ( curve: Curve ) where
  x : ZMod curve.p
  y : ZMod curve.p
  proof :  y ^ 2 - x ^ 3 - curve.a * x - curve.b = 0
  deriving Repr


/--
An affine point; either finite or infinity
-/
inductive AffinePoint ( curve: Curve ) where
  | mk : FiniteAffinePoint curve → AffinePoint curve
  | infinity : AffinePoint curve
  deriving Repr
