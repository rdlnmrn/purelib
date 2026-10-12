module
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Polynomial.Clearance.Box.Boundary.Constant
import Purelib.Polynomial.Clearance.Box.Boundary.Operations
import Purelib.Polynomial.Clearance.Box.Boundary.Translated
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Polynomial.Winding.Box.Affine
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Constant
import Purelib.Polynomial.Winding.Box.Product
public import Purelib.RationalFunctions.ArgumentPrinciple.General
import Purelib.RationalFunctions.Winding.Box.Basic
import Purelib.RationalFunctions.Winding.Box.Quotient

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Dense.Gaussian.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.RationalFunctions

section
@[expose] public section

/-!
# Executable RFAP examples

These small displayed dense polynomials exercise both public branches.  The
first quotient has two coprime squarefree numerator zeros and one coprime
squarefree denominator pole.  The second has one repeated numerator factor;
its finite rational box has ordinary winding two rather than one.
-/

namespace Purelib.Examples.RationalFunctions.ArgumentPrinciple.Multiplicity.WorkedExamples

open Purelib.Examples

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Linear

/-- The square of the monic linear polynomial with its zero at one. -/
def repeatedNumerator :
  CoefficientPolynomial :=
  Translated.translatedCoordinate 1 * Translated.translatedCoordinate
    1

/-- The constant unit denominator for the repeated-root quotient. -/
def repeatedDenominator :
  CoefficientPolynomial := Dense.Basic.DensePolynomial.constant 1

/-- The symmetric rational box of radius two surrounding the repeated root. -/
def repeatedBox :
  Rational.Box :=
  Rational.Box.symmetric 2 (by decide)

/-- The quotient has ordinary box winding two.

The two translated linear factors each contribute one; their retained boundary clearances justify product and quotient
winding identities on the proper box. -/
theorem
  repeatedFactor_boxWinding :
    Winding.Box.Basic.rationalBoxWinding
      repeatedNumerator
        repeatedDenominator
        repeatedBox = 2 := by
  have proper : repeatedBox.Proper := by
    change (-2 : Fraction.Rational) < 2 ∧
      (-2 : Fraction.Rational) < 2
    exact ⟨by decide, by decide⟩
  have left : repeatedBox.xLower < (1 :
    Gaussian.Basic.Canonical).re := by decide
  have right : (1 : Gaussian.Basic.Canonical).re <
    repeatedBox.xUpper := by decide
  have below : repeatedBox.yLower < (1 :
    Gaussian.Basic.Canonical).im := by decide
  have above : (1 : Gaussian.Basic.Canonical).im <
    repeatedBox.yUpper := by decide
  let linearClearance :=
    Clearance.Box.Boundary.Translated.Affine.translatedCoordinate_boundaryClearanceBox
      (1 : Gaussian.Basic.Canonical) left right below above
  let repeatedClearance :=
    Clearance.Box.Boundary.Basic.BoundaryClearance.mul
      linearClearance linearClearance
  let denominatorClearance :=
    Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance
      (c := (1 : Gaussian.Basic.Canonical)) one_ne_zero
        repeatedBox
  have linearWinding :
      Winding.Box.Basic.quadrupledBoxWinding
        (Translated.translatedCoordinate 1)
          repeatedBox = 4 := by
    simpa only [Translated.translatedCoordinate] using
      Winding.Box.Affine.quadrupledBoxWinding_translatedCoordinate
        (1 : Gaussian.Basic.Canonical) left right below above
  have productWinding :=
    Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances
      (Translated.translatedCoordinate 1)
        (Translated.translatedCoordinate 1)
        repeatedBox proper linearClearance
        linearClearance
  have denominatorWinding :=
    Winding.Box.Constant.quadrupledBoxWinding_gaussianConstant
      (c := (1 : Gaussian.Basic.Canonical)) one_ne_zero
        repeatedBox
  have quotientWinding :=
    Winding.Box.Quotient.rationalQuadrupledWinding_eq_sub_of_boundaryClearances
      repeatedNumerator
        repeatedDenominator
        repeatedBox proper
      repeatedClearance denominatorClearance
  apply Winding.Box.Basic.rationalBoxWinding_eq_of_quadrupled_eq_four_mul
  rw [quotientWinding]
  change Winding.Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1 *
        Translated.translatedCoordinate 1)
        repeatedBox -
      Winding.Box.Basic.quadrupledBoxWinding
        (Dense.Gaussian.Constants.gaussianConstant 1)
          repeatedBox = 4 * 2
  rw [productWinding, linearWinding, denominatorWinding]
  ring1

/-- The executable argument-principle result for the displayed repeated-root quotient.

The constructor retains the original numerator and constant denominator and checks the denominator is nonzero before
constructing multiplicity-aware sites. -/
def repeatedFactorResult :=
  ArgumentPrinciple.General.prove repeatedNumerator
    repeatedDenominator
    (by decide)

end Purelib.Examples.RationalFunctions.ArgumentPrinciple.Multiplicity.WorkedExamples

end
