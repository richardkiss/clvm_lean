import Lean.Attributes

import Init.Prelude
import Init.Data.UInt
import Init.Data.Fin
import Init.Data.Nat

import Mathlib

import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic

import Mathlib.Tactic.Ring

import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp

import Clvm.Ecdsa.Affine
import Clvm.Ecdsa.Curve
import Clvm.Ecdsa.Jacobian


theorem affine_to_jac_works {curve : Curve} {x y z : ZMod curve.p} :
    (y ^ 2 - x ^ 3 - curve.a * x - curve.b = 0) →
    (z = 1) →
    (y ^ 2 - x ^ 3 - curve.a * x * z ^ 4 - curve.b * z ^ 6 = 0) := by
    intro h0
    intro h1
    rewrite [h1]
    simp
    exact h0


def affine_ni_to_jacobian {curve : Curve} (ap : FiniteAffinePoint curve) : JacobianPoint curve :=
  let x := ap.x
  let y := ap.y
  let z := 1
  let proof := affine_to_jac_works ap.proof rfl
  ⟨x, y, z, proof⟩


def affine_to_jacobian {curve : Curve} (ap : AffinePoint curve) : JacobianPoint curve :=
  match ap with
  | AffinePoint.mk ap => affine_ni_to_jacobian ap
  | AffinePoint.infinity =>
    let x : ZMod curve.p := 1
    let y : ZMod curve.p := 1
    let z : ZMod curve.p := 0
    have proof : y ^ 2 - x ^ 3 - curve.a * x * z ^ 4 - curve.b * z ^ 6 = 0 := by
      sorry
    ⟨x, y, z, proof⟩


def jacobian_to_affine {curve : Curve} (jp : JacobianPoint curve) (is_unit: IsUnit jp.z): AffinePoint curve :=
  let x := jp.x
  let y := jp.y
  let z := jp.z

  if is_infinity jp then
    AffinePoint.infinity
  else
    let w := jp.z⁻¹
    let _z_inv_squared := w * w

    let x' := x * w ^ 2
    let y' := y * w ^ 3


    have h_inv: 1 = w * z := by
      symm
      refine ZMod.inv_mul_of_unit jp.z ?h
      exact is_unit

    have p1 : y ^ 2 - x ^ 3 - curve.a * x * z ^ 4 - curve.b * z ^ 6 = 0 := jp.proof

    have new_proof : y' ^ 2 - x' ^ 3 - curve.a * x' - curve.b = 0 :=
      calc
        y' ^ 2 - x' ^ 3 - curve.a * x' - curve.b = (y * w ^ 3) ^ 2 - (x * w ^ 2) ^ 3 - curve.a * x * w ^ 2 - curve.b := by ring
        _ = (y * w ^ 3 ) ^ 2 - (x * w ^ 2) ^ 3 - curve.a * x * w ^ 2 * 1       ^ 4 - curve.b * 1       ^ 6 := by ring
        _ = (y * w ^ 3 ) ^ 2 - (x * w ^ 2) ^ 3 - curve.a * x * w ^ 2 * (w * z) ^ 4 - curve.b * (w * z) ^ 6 := by rw [h_inv]
        _ = (y * w ^ 3 ) * (y * w ^ 3 ) - (x * w ^ 2) * (x * w ^ 2) * (x * w ^ 2) - curve.a * x * w ^ 2 * (w * z) * (w * z) * (w * z) * (w * z) - curve.b * (w * z)  * (w * z)  * (w * z)  * (w * z)  * (w * z)  * (w * z) := by ring
        _ = y ^ 2 * w ^ 6 - x ^ 3 * w ^ 6 - curve.a * x * w ^ 6 * z ^ 4 - curve.b * w ^ 6 * z ^ 6 := by ring
        _ = (w ^ 6) * (y ^ 2 - x ^ 3 - curve.a * x * z ^ 4 - curve.b * z ^ 6) := by ring
        _ = (w ^ 6) * 0 := by rw [p1]
        _ = 0 := by ring

    AffinePoint.mk (FiniteAffinePoint.mk x' y' new_proof)



instance affineCoeJacobian {curve : Curve} : Coe (AffinePoint curve) (JacobianPoint curve) where
  coe := affine_to_jacobian


instance affineNotInfinityCoeJacobian {curve : Curve} : Coe (FiniteAffinePoint curve) (JacobianPoint curve) where
  coe := affine_ni_to_jacobian
