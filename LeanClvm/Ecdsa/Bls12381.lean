import LeanClvm.Ecdsa.Affine
import LeanClvm.Ecdsa.Coe
import LeanClvm.Ecdsa.Curve
import LeanClvm.Ecdsa.Jacobian

import Mathlib.Data.ZMod.Basic


def bls_prime := 0x1A0111EA397FE69A4B1BA7B6434BACD764774B84F38512BF6730D2A0F6B0F6241EABFFFEB153FFFFB9FEFFFFFFFFAAAB
axiom bls_prime_is_prime : Nat.Prime bls_prime

def CurveBLS12381 := Curve.mk bls_prime bls_prime_is_prime 0 4

def bls_gen_x : ZMod CurveBLS12381.p := ⟨ 3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507, by decide⟩
def bls_gen_y : ZMod CurveBLS12381.p := ⟨ 1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569, by decide⟩

def generator_bls12381_g1 : JacobianPoint CurveBLS12381 := AffinePoint.mk (AffinePointNotInfinity.mk bls_gen_x bls_gen_y)

/-
#eval jacobian_to_affine (generator_bls12381_g1 + generator_bls12381_g1 + generator_bls12381_g1)


def pubkey_for_exp (exp : Nat) : JacobianPoint CurveBLS12381 :=
  exp * generator_bls12381_g1

#eval jacobian_to_affine (pubkey_for_exp 3)


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
    #[0xc0] ++ (Array.mkArray 95 0)
  | AffinePoint.mk ap =>
    let x_bytes := nat_to_bytes48 ap.x.val
    let exceeds_half := ap.y.val > CurveBLS12381.p / 2
    let new_x_bytes_0 := x_bytes[0]! ||| 0b10000000 ||| (if exceeds_half then 0b00100000 else 0b00000000)
    let new_x_bytes := #[new_x_bytes_0] ++ x_bytes.extract 1 x_bytes.size
    new_x_bytes


#eval serialize_point (2001 * generator_bls12381_g1)


def points_for_x {curve : Curve} (x : ZMod curve.p) : (AffinePointNotInfinity curve) × (AffinePointNotInfinity curve) :=
  let alpha := x * x * x + curve.a * x + curve.b
  let y0 := alpha ^ ((curve.p + 1) / 4)
  let y1 := -y0
  let y0_nat : Nat := y0.val
  let y1_nat : Nat := y1.val
  if y0_nat > y1_nat then
    (⟨x, y0⟩, ⟨x, y1⟩)
  else
    (⟨x, y1⟩, ⟨x, y0⟩)


def deserialize_point (bytes : Array UInt8) : Option (JacobianPoint CurveBLS12381) :=
  if bytes.size == 48 then
    if bytes[0]! == 0xc0 then
      if bytes.extract 1 48 = (Array.mkArray 47 0) then
        some ⟨1, 1, 0⟩
      else
        none
    else
      let new_x_bytes := bytes.modify 0 (fun b => b &&& 0b00011111)
      let x0 := bytes[0]!
      let x : Nat := new_x_bytes.foldl (fun acc b => acc * 256 + b.toNat) 0
      let _x_mod : ZMod CurveBLS12381.p := x % CurveBLS12381.p
      let points := points_for_x x
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



def ap: AffinePoint CurveBLS12381 := jacobian_to_affine (2001 * generator_bls12381_g1)
#eval ap
#eval deserialize_point (serialize_point (2001 * generator_bls12381_g1))
-/
