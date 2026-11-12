module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.InfinityCoefficients
public import Purelib.Polynomial.Ascending.Gaussian.Antiderivative.Reciprocal

/-! # The retained infinity principal product and its finite nonlogarithmic primitive -/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.InfinityCoefficients.Jet.Principal

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian

variable {genus : Nat} {curve : HyperellipticCurve genus} {jet : Jet curve}
  {polynomial : Dense.Basic.DensePolynomial Canonical} {scale : Canonical}

/-- The actual retained principal product's finite reciprocal primitive, omitting precisely its logarithmic pivot. -/
@[expose] def nonlogarithmic (retained : jet.Principal polynomial scale) :
    Antiderivative.ReciprocalPrimitive retained.val genus :=
  Antiderivative.reciprocalPrimitive retained.val genus

/-- The actual retained infinity principal product has its own finite primitive coefficient, logarithmic pivot and tail.

The same supplied primitive cache consumes that original retained C table.
The coordinate guard justifies its reciprocal powers; no sheet, completed
local expansion or physical residue identification is an input or conclusion.
-/
theorem nonlogarithmic_split (retained : jet.Principal polynomial scale)
    (primitive : Antiderivative.ReciprocalPrimitive retained.val genus) (point : Canonical) (nonzero : point ≠ 0) :
    Evaluation.eval retained.val point * (point ^ (genus + 1))⁻¹ =
      primitive.derivativeValue point + Coefficient.coefficient retained.val genus * point⁻¹ +
        Evaluation.eval (Arithmetic.divideByPower (genus + 1) retained.val) point :=
  primitive.split point nonzero

/-- The even original numerator functional is exactly the logarithmic scalar beside its same finite primitive.

The original padded numerator, same retained jet and same retained C product
supply the coefficient identity. This finite guarded identity does not turn
the coefficient functional into a definition of physical residue.
-/
theorem even_nonlogarithmic_split (numerator : Dense.Basic.DensePolynomial Canonical)
    (bound : numerator.degreeCount ≤ 2 * genus + 1)
    (padded : { value : Dense.Basic.DensePolynomial Canonical //
      value = Dense.Gaussian.Reciprocal.padded numerator (2 * genus) })
    (retained : jet.Principal padded.val scale)
    (primitive : Antiderivative.ReciprocalPrimitive retained.val genus) (point : Canonical) (nonzero : point ≠ 0) :
    Evaluation.eval retained.val point * (point ^ (genus + 1))⁻¹ =
      primitive.derivativeValue point +
        (-scale * evenFunctional curve jet (Dense.Evaluation.toVector (2 * genus + 1)
          (Dense.Evaluation.fromDense numerator.normalize))) * point⁻¹ +
        Evaluation.eval (Arithmetic.divideByPower (genus + 1) retained.val) point := by
  rw [retained.nonlogarithmic_split primitive point nonzero,
    even_coefficient curve jet numerator scale bound padded retained]

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.InfinityCoefficients.Jet.Principal

end
