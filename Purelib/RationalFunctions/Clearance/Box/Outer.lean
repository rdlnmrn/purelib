module
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.RootRadius
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RationalFunctions.Bounds.Outer.Box
import Purelib.RationalFunctions.Reduction.Nonzero

section
@[expose] public section

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
/-- Construct a boundary clearance for the reduced numerator on the common outer square.

Its nonzeroness and coefficient-computed radius bound supply the certificate on that exact square. -/
def numeratorOuterClearance
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Reduction.Nonzero.NonzeroReducedInput numerator denominator) :
    Clearance.Box.Boundary.Basic.BoundaryClearance
      input.reduction.numeratorReduced input.outerBox := by
  simpa only [Reduction.Nonzero.NonzeroReducedInput.outerBox] using
    Clearance.Box.Boundary.RootRadius.symmetric_boundaryClearance_of_nonzero
      input.numeratorReducedNonzero input.numeratorRadius_le_outerRadius

/-- Construct a boundary clearance for the reduced denominator on the common outer square.

Its nonzeroness and coefficient-computed radius bound supply the certificate on that exact square. -/
def denominatorOuterClearance
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Reduction.Nonzero.NonzeroReducedInput numerator denominator) :
    Clearance.Box.Boundary.Basic.BoundaryClearance
      input.reduction.denominatorReduced input.outerBox := by
  simpa only [Reduction.Nonzero.NonzeroReducedInput.outerBox] using
    Clearance.Box.Boundary.RootRadius.symmetric_boundaryClearance_of_nonzero
      input.denominatorReducedNonzero input.denominatorRadius_le_outerRadius
end NonzeroReducedInput

end Purelib.RationalFunctions.Reduction.Nonzero

end
