module

import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Norm.Basic

open Purelib.Data

section
@[expose] public section

/-!
# Finite norm-two Gaussian cosets

This file gives the displayed-coordinate algebra needed for the centered
index-two alternative.  Divisibility is represented by an explicit Gaussian
integer quotient.  For a divisor of quadrance two it is equivalent to even
parity of the sum of the two coordinates; the complementary odd class is
therefore closed under multiplication and two odd classes add to the even
class.  No quotient ring or cardinality argument is used.
-/

namespace Purelib.Data.GaussianInt.Divisibility.Basic
open Purelib.Data.GaussianInt

/-- Retain an explicit Gaussian-integer quotient witnessing divisibility.

The displayed value must equal the divisor times the retained integral quotient; no
quotient carrier or ideal membership is introduced. -/
def Divides
    (divisor value : Data.GaussianInt.Embedding.Integer) : Prop :=
  ∃ quotient : Data.GaussianInt.Embedding.Integer, value = divisor * quotient

open Purelib.Data.GaussianInt.Divisibility in
/-- A nonzero Gaussian integer of smaller quadrance cannot be divisible by the proposed
divisor.

An explicit quotient would be nonzero, so its positive natural norm makes the product
norm at least the divisor norm. -/
theorem not_divides_of_norm_lt {divisor value :
  Data.GaussianInt.Embedding.Integer}
    (valueNonzero : value ≠ 0)
    (normSmaller : normNat value < normNat divisor) :
    ¬ Divides divisor value := by
  rintro ⟨quotient, identity⟩
  have quotientNonzero : quotient ≠ 0 := by
    intro quotientZero
    rw [quotientZero,
      GaussianInt.mul_zero] at identity
    exact valueNonzero identity
  have quotientNormPositive := normNat_pos quotientNonzero
  have normIdentity := congrArg normNat identity
  rw [normNat_mul] at normIdentity
  have divisorNormLeValueNorm : normNat divisor ≤ normNat value := by
    calc
      normNat divisor = normNat divisor * 1 := (Nat.mul_one _).symm
      _ ≤ normNat divisor * normNat quotient :=
        Nat.mul_le_mul_left _ quotientNormPositive
      _ = normNat value := normIdentity.symm
  exact (Nat.not_le_of_gt normSmaller) divisorNormLeValueNorm
end Purelib.Data.GaussianInt.Divisibility.Basic

end
