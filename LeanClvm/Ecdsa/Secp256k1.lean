import LeanClvm.Ecdsa.Affine
import LeanClvm.Ecdsa.Coe
import LeanClvm.Ecdsa.Curve
import LeanClvm.Ecdsa.Jacobian


-- variable (p : ℕ) [Fact p.Prime]




def secp256k1_prime := 115792089237316195423570985008687907853269984665640564039457584007908834671663
def s7 : ZMod secp256k1_prime := ⟨7, by decide⟩
def s0 : ZMod secp256k1_prime := ⟨0, by decide⟩

axiom secp256k1_prime_is_prime : Nat.Prime secp256k1_prime

def CurveSecp256k1 := Curve.mk secp256k1_prime secp256k1_prime_is_prime s0 s7


def Gx : ZMod CurveSecp256k1.p := ⟨ 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798, by decide⟩
def Gy : ZMod CurveSecp256k1.p := ⟨ 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8, by decide⟩


theorem legit_b : Gx * Gx * Gx + CurveSecp256k1.a * Gx + CurveSecp256k1.b = Gy * Gy := by rfl


def generator_secp256k1 : JacobianPoint CurveSecp256k1 := JacobianPoint.mk Gx Gy 1



#eval jacobian_to_affine generator_secp256k1

#eval jacobian_to_affine (generator_secp256k1+ (generator_secp256k1 + generator_secp256k1))
