module
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
public import Purelib.Computation.Arithmetic.Cost.Rational

import Purelib.Tactic.QuotientFreeOmega

section
@[expose] public section

/-! Gaussian arithmetic work charges. -/

namespace Purelib.Computation.Arithmetic.Cost.Gaussian

open Purelib.Data.Gaussian
open Purelib.Computation.Arithmetic.Cost.Basic
open Purelib.Computation.Arithmetic.Cost

/-- Add the rational comparison charges of the real and imaginary components. -/
def gaussianEqualityCost (left right : Basic.Canonical) : Nat :=
  Rational.rationalEqualityCost left.re right.re +
    Rational.rationalEqualityCost left.im right.im

/-- Charge the six rational operations in a Gaussian product.

Four products are followed by the real-part subtraction and imaginary-part addition. Each charge uses the corresponding
actual rational operands and result. -/
def gaussianMulWork (left right : Basic.Canonical) : Work :=
  let realLeft := Rational.rationalMulWork left.re right.re
  let realRight := Rational.rationalMulWork left.im right.im
  let imaginaryLeft := Rational.rationalMulWork left.re right.im
  let imaginaryRight := Rational.rationalMulWork left.im right.re
  realLeft + realRight + imaginaryLeft + imaginaryRight +
    Rational.rationalSubWork (left.re * right.re) (left.im * right.im) +
    Rational.rationalAddWork (left.re * right.im) (left.im * right.re)

/-- Charge the two squares and addition forming a Gaussian squared norm. -/
def gaussianNormWork (value : Basic.Canonical) : Work :=
  Rational.rationalMulWork value.re value.re +
    Rational.rationalMulWork value.im value.im +
    Rational.rationalAddWork (value.re * value.re) (value.im * value.im)
end Purelib.Computation.Arithmetic.Cost.Gaussian

end
