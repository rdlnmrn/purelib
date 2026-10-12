module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Embedding

open Purelib.Data

open Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Finite denominator-height lower bounds for polynomial residuals

The finite coefficient list is cleared to Gaussian integers by a structural
product of the canonical coordinate denominators.  Homogeneous evaluation at
a displayed common-denominator Gaussian fraction then gives an integral
numerator.  If the residual is nonzero, its integral norm is at least one.
-/

namespace Purelib.Data.GaussianInt.Arithmetic.Scale

section GaussianInt

/-- Multiply a Gaussian integer by a displayed natural regarded as a real integral value. -/
def scale (factor : Nat) (value : GaussianInt) :
  GaussianInt :=
  GaussianInt.ofNat factor * value

open Purelib.Data.GaussianInt.Arithmetic.Scale in
/-- Embedding natural scaling agrees with multiplying by the same real rational Gaussian
scalar. -/
@[simp] theorem toGaussian_scale (factor : Nat) (value :
  GaussianInt) :
    GaussianInt.toGaussian
        (scale factor value) =
      ⟨(factor : Rational), 0⟩ *
        GaussianInt.toGaussian value := by
  rw [scale, GaussianInt.toGaussian_mul, GaussianInt.toGaussian_ofNat]
end GaussianInt
end Purelib.Data.GaussianInt.Arithmetic.Scale

end
