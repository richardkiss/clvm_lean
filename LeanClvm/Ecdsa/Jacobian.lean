import LeanClvm.Ecdsa.Curve



structure JacobianPoint ( curve: Curve ) where
  x : ZMod curve.p
  y : ZMod curve.p
  z : ZMod curve.p
  -- proof : y ^ 2 - x ^ 3 - curve.a * x * z ^ 4 - curve.b * z ^ 6 = 0
  deriving Repr


def is_infinity {curve : Curve} (p : JacobianPoint curve) : Bool :=
  p.z = 0


def zero {curve : Curve} : JacobianPoint curve :=
  ⟨1, 1, 0⟩


def double_jacobian {curve : Curve} ( p : (JacobianPoint curve)) : JacobianPoint curve :=
  -- from https://en.wikibooks.org/wiki/Cryptography/Prime_Curve/Jacobian_Coordinates
  let x  := p.x
  let y  := p.y
  let z  := p.z
  let s  := 4 * x * y * y
  let m  := 3 * x * x + curve.a * z * z * z * z
  let x' := m * m - 2 * s
  let y' := m * (s - x') - 8 * (y * y) ^ 2
  let z' := 2 * y * z

  -- let proof := p.proof

  -- have hy' : y' = m * (s - x') - 8 * (y ^ 2) ^ 2 := by ring

  -- TO TRY: `simp only` and putting `sorry` in front of slow proofs

  /-
  have hK : y ^ 8 * 64 - x * curve.a * z ^ 4 * y ^ 6 * 64 - x ^ 3 * y ^ 6 * 64 - z ^ 6 * y ^ 6 * curve.b * 64 = 0 :=
    calc
      y ^ 8 * 64 - x * curve.a * z ^ 4 * y ^ 6 * 64 - (x ^ 3 * y ^ 6 * 64) - z ^ 6 * y ^ 6 * curve.b * 64 = 64 * (y ^ 6) * (y ^ 2 - x * curve.a * z ^ 4 - x ^ 3 - z ^ 6 * curve.b) := by ring
      _ = 64 * (y ^ 6) * (y ^ 2 - x * curve.a * z ^ 4 - x ^ 3 - z ^ 6 * curve.b) := by ring
      _ = 64 * (y ^ 6) * (y ^ 2 - x ^ 3 - curve.a * x * z ^ 4  - curve.b * z ^ 6) := by ring
      _ = 64 * (y ^ 6) * 0 := by rw [p.proof]
      _ = 0 := by ring

  have h : y' ^ 2 - x' ^ 3 - curve.a * x' * z' ^ 4 - curve.b * z' ^ 6 = 0 := by
    simp
    ring_nf

    sorry
  -/
  if z' = 0 then
    zero
  else
    ⟨x', y', z'⟩


def add_jacobian { curve : Curve } ( p1 p2 : JacobianPoint curve ) : JacobianPoint curve :=
  -- from https://en.wikibooks.org/wiki/Cryptography/Prime_Curve/Jacobian_Coordinates
  if p1.z = 0 then
    p2
  else if p2.z = 0 then
    p1
  else
    let x1 := p1.x
    let y1 := p1.y
    let z1 := p1.z
    let x2 := p2.x
    let y2 := p2.y
    let z2 := p2.z
    let u1 := x1 * z2 * z2
    let u2 := x2 * z1 * z1
    let s1 := y1 * z2 * z2 * z2
    let s2 := y2 * z1 * z1 * z1
    if u1 == u2 then
      if s1 == s2 then
        double_jacobian p1
      else
        zero
    else
      let h := u2 - u1
      let h_squared := h * h
      let h_cubed := h_squared * h
      let r := s2 - s1
      let u1h_squared := u1 * h_squared
      let x3 := r * r - h_cubed - 2 * u1h_squared
      let y3 := r * (u1h_squared - x3) - s1 * h_cubed
      let z3 := h * z1 * z2
      ⟨x3, y3, z3⟩


instance {curve : Curve} : Add (JacobianPoint curve) where
  add := add_jacobian



def fin_mul_jac (b : Nat) (a : JacobianPoint curve) : JacobianPoint curve :=
  if b = 0 then
    ⟨1, 1, 0⟩
  else if h0: b <= 1 then
    a
  else
    have h0 : b >= 1 := by
      push_neg at h0
      exact Nat.le_of_lt h0
    have _h: b / 2 < b := by
      exact Nat.div_lt_self h0 Nat.le.refl
    let half_mul := fin_mul_jac (b / 2) a
    if b % 2 == 0 then
      half_mul + half_mul
    else
      half_mul + half_mul + a


instance {curve : Curve} : HMul Nat (JacobianPoint curve) (JacobianPoint curve) where
  hMul := fin_mul_jac
