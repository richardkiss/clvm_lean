import Init.NotationExtra
import Init.Data.Nat.Linear

import Std
import Lean.Attributes

import Init.Prelude
import Init.Data.UInt
import Init.Data.Fin
import Init.Data.Nat

import Clvm.Atom
import Clvm.Ecdsa.Affine
import Clvm.Ecdsa.Bls12381
import Clvm.Ecdsa.Coe
import Clvm.Ecdsa.Curve
import Clvm.Ecdsa.Jacobian
import Clvm.Ecdsa.Secp256k1

import Mathlib.Data.Nat.Prime
import Mathlib.Data.ZMod.Basic

import Mathlib.Tactic.Ring

-- import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.FieldSimp


def pubkey_for_exp (exp : Nat) : JacobianPoint CurveBLS12381 :=
  exp * generator_bls12381_g1


def nat_to_bytes48 (n : Nat) : Array UInt8 :=
  let rec loop (count : Nat) (n : Nat) : List UInt8 :=
    if count = 0 then
      []
    else
      let byte : UInt8 := UInt8.ofNat (n % 256)
      loop (count - 1) (n / 256) ++ [byte]
  (loop 48 n).toArray


def serialize_point (p : JacobianPoint CurveBLS12381) : Array UInt8 :=
  let ap : AffinePoint CurveBLS12381 := jacobian_to_affine p
  match ap with
  | AffinePoint.infinity =>
    #[0xc0] ++ (Array.mkArray 47 0)
  | AffinePoint.mk ap =>
    let x_bytes := nat_to_bytes48 ap.x.val
    let exceeds_half := ap.y.val > CurveBLS12381.p / 2
    let new_x_bytes_0 := x_bytes[0]! ||| 0b10000000 ||| (if exceeds_half then 0b00100000 else 0b00000000)
    let new_x_bytes := #[new_x_bytes_0] ++ (x_bytes.extract 1 48)
    new_x_bytes




def pow_zmod {curve : Curve}  (x : ZMod curve.p) (n : Nat) : ZMod curve.p :=
  if n = 0 then
    1
  else
    x * (pow_zmod x (n - 1))


def pow_zmod_fast {curve : Curve}  (x : ZMod curve.p) (n : Nat) : ZMod curve.p :=
  let rec loop (x : ZMod curve.p) (n : Nat) (acc : ZMod curve.p) : ZMod curve.p :=
    if h: n >= 2 then
      have : n / 2 < n := by
        exact Nat.log2_terminates n h
      loop (x * x) (n / 2) (if n % 2 = 0 then acc else (x * acc))
    else
      x * acc
  if n = 0 then
    1
  else
    loop x n 1

/-

theorem pow_zmod_eq_pow_zmod_fast {curve : Curve} (x : ZMod curve.p) (n : Nat) : pow_zmod x n = pow_zmod_fast x n := by
  induction n with
  | zero =>
      simp [pow_zmod, pow_zmod_fast, pow_zmod_fast.loop]
  | succ n ih =>
    simp [pow_zmod, pow_zmod_fast, pow_zmod_fast.loop]
    rw [ih]

-/


def points_for_x {curve : Curve} (x : ZMod curve.p) : (AffinePointNotInfinity curve) × (AffinePointNotInfinity curve) :=
  let alpha : ZMod curve.p := x ^ 3 + curve.a * x + curve.b
  let exp : Nat := (curve.p + 1) / 4
  let y0 := pow_zmod_fast alpha exp
  let y1 := -y0
  let y0_nat : Nat := y0.val
  let y1_nat : Nat := y1.val
  /-let proof : y0^2 - x^3 - curve.a * x - curve.b = 0 := by
    simp
    ring
-/
  if y0_nat < y1_nat then
    (⟨x, y0⟩, ⟨x, y1⟩)
  else
    (⟨x, y1⟩, ⟨x, y0⟩)


def deserialize_point (bytes : List Nat) : Option (JacobianPoint CurveBLS12381) :=
  if bytes.length = 48 then
    if bytes[0]! = 0xc0 then
      if bytes = 0xc0 :: (Array.mkArray 47 0).toList then
        some zero
      else
        none
    else
      let new_x_bytes : Atom := bytes.modify 0 (fun b => b &&& 0b00011111)
      let x0 := bytes[0]!
      let x : Nat := atom_to_nat new_x_bytes
      let x_mod : ZMod CurveBLS12381.p := x % CurveBLS12381.p
      let points := points_for_x x_mod
      let chosen_point: AffinePointNotInfinity CurveBLS12381 := (
        if x0 &&& 0b100000 = 0 then
          points.1
        else
          points.2
      )
      let jp : JacobianPoint CurveBLS12381 := affine_ni_to_jacobian chosen_point
      some jp
  else
    none



def normalize_point {curve : Curve} (p : JacobianPoint curve) : JacobianPoint curve :=
  affine_to_jacobian (jacobian_to_affine p)
