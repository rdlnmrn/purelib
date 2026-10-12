module
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
public import Purelib.RationalFunctions.Reduction.Nonzero
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RationalFunctions.Reduction.Nonzero (NonzeroReducedInput)

section
public section

/-!
# Common finite outer square for a reduced rational function

The two nonzero reduced cofactors share one coefficient-computed rational
square.  Their constructive polynomial windings give the quotient's degree
difference directly, including constant and linear cofactors.
-/

namespace Purelib.RationalFunctions.Reduction.Nonzero.NonzeroReducedInput

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- Compute a common positive outer radius for the reduced numerator and denominator.

Take the maximum of their coefficient-computed large-square radii, retaining a single square for both cofactors. -/
@[expose] def outerRadius
    {numerator denominator : CoefficientPolynomial}
    (input : NonzeroReducedInput numerator denominator) : Rat.Fraction.Rational :=
  max
    (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius
      input.reduction.numeratorReduced)
    (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius
      input.reduction.denominatorReduced)

section
open Purelib.Polynomial
open Purelib.RationalFunctions
/-- The reduced numerator's large-square radius is at most the common outer radius. -/
theorem numeratorRadius_le_outerRadius
    {numerator denominator : CoefficientPolynomial}
    (input : NonzeroReducedInput numerator denominator) :
    Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius
        input.reduction.numeratorReduced ≤ input.outerRadius :=
  Purelib.Data.Rat.Fraction.Order.Basic.le_max_left _ _

/-- The reduced denominator's large-square radius is at most the common outer radius. -/
theorem denominatorRadius_le_outerRadius
    {numerator denominator : CoefficientPolynomial}
    (input : NonzeroReducedInput numerator denominator) :
    Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius
        input.reduction.denominatorReduced ≤ input.outerRadius :=
  Purelib.Data.Rat.Fraction.Order.Basic.le_max_right _ _

/-- The common outer radius is strictly positive. -/
theorem outerRadius_pos
    {numerator denominator : CoefficientPolynomial}
    (input : NonzeroReducedInput numerator denominator) :
    0 < input.outerRadius :=
  (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos
    input.reduction.numeratorReduced).trans_le
      input.numeratorRadius_le_outerRadius

end

open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- Construct the symmetric rational square with the common outer radius of the reduced pair. -/
@[expose] def outerBox
    {numerator denominator : CoefficientPolynomial}
    (input : NonzeroReducedInput numerator denominator) : Rational.Box :=
  Rational.Box.symmetric input.outerRadius
    input.outerRadius_pos.le

open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- The common outer square has strictly ordered bounds in both coordinates. -/
theorem outerBox_proper
    {numerator denominator : CoefficientPolynomial}
    (input : NonzeroReducedInput numerator denominator) :
    input.outerBox.Proper := by
  change -input.outerRadius < input.outerRadius ∧
    -input.outerRadius < input.outerRadius
  have belowZero := Purelib.Data.Rat.Fraction.Order.Arithmetic.neg_lt_neg_direct input.outerRadius_pos
  rw [_root_.neg_zero] at belowZero
  exact ⟨belowZero.trans input.outerRadius_pos, belowZero.trans input.outerRadius_pos⟩
end Purelib.RationalFunctions.Reduction.Nonzero.NonzeroReducedInput

end
