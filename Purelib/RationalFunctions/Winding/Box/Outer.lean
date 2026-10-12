module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Global
public import Purelib.RationalFunctions.Bounds.Outer.Box
import Purelib.RationalFunctions.Reduction.Nonzero
public import Purelib.RationalFunctions.Winding.Box.Basic
import Purelib.RationalFunctions.Winding.Box.Quotient
import Purelib.RationalFunctions.Clearance.Box.Outer
import Purelib.Tactic.Ring

section
public section

/-!
# Common finite outer square for a reduced rational function

The two nonzero reduced cofactors share one coefficient-computed rational
square.  Their constructive polynomial windings give the quotient's degree
difference directly, including constant and linear cofactors.
-/

namespace Purelib.RationalFunctions.Reduction.Nonzero
namespace NonzeroReducedInput

open Purelib.Polynomial
open Purelib.RationalFunctions
/-- Quadrupled quotient winding on the common outer square is four times the reduced degree difference.

Both reduced cofactors are nonzero and clear on that exact square, so the polynomial degree laws combine by subtraction.
-/
theorem outer_rationalWinding_eq_degreeDifference
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Reduction.Nonzero.NonzeroReducedInput numerator denominator) :
    Winding.Box.Basic.rationalQuadrupledWinding
        input.reduction.numeratorReduced input.reduction.denominatorReduced
        input.outerBox =
      (4 : Int) * input.reduction.numeratorReduced.natDegree -
        (4 : Int) * input.reduction.denominatorReduced.natDegree := by
  have quotient :=
    Winding.Box.Quotient.rationalQuadrupledWinding_eq_sub_of_boundaryClearances
      input.reduction.numeratorReduced input.reduction.denominatorReduced
      input.outerBox input.outerBox_proper input.numeratorOuterClearance
      input.denominatorOuterClearance
  have numeratorWinding :
      Winding.Box.Basic.quadrupledBoxWinding input.reduction.numeratorReduced input.outerBox =
        (4 : Int) * input.reduction.numeratorReduced.natDegree := by
    simpa only [Reduction.Nonzero.NonzeroReducedInput.outerBox] using
      Winding.Box.Global.quadrupledBoxWinding_symmetric_eq_degree_of_nonzero
        input.numeratorReducedNonzero input.numeratorRadius_le_outerRadius
  have denominatorWinding :
      Winding.Box.Basic.quadrupledBoxWinding input.reduction.denominatorReduced input.outerBox =
        (4 : Int) * input.reduction.denominatorReduced.natDegree := by
    simpa only [Reduction.Nonzero.NonzeroReducedInput.outerBox] using
      Winding.Box.Global.quadrupledBoxWinding_symmetric_eq_degree_of_nonzero
        input.denominatorReducedNonzero input.denominatorRadius_le_outerRadius
  rw [quotient, numeratorWinding, denominatorWinding]

/-- Ordinary quotient winding on the common outer square equals the reduced numerator degree minus denominator degree.
-/
theorem outer_boxWinding_eq_degreeDifference
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Reduction.Nonzero.NonzeroReducedInput numerator denominator) :
    Winding.Box.Basic.rationalBoxWinding
        input.reduction.numeratorReduced input.reduction.denominatorReduced
        input.outerBox =
      (input.reduction.numeratorReduced.natDegree : Int) -
        input.reduction.denominatorReduced.natDegree := by
  apply Winding.Box.Basic.rationalBoxWinding_eq_of_quadrupled_eq_four_mul
  rw [input.outer_rationalWinding_eq_degreeDifference]
  ring1

end NonzeroReducedInput

end Purelib.RationalFunctions.Reduction.Nonzero

end
