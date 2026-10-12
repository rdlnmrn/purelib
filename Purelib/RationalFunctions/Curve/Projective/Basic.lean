module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Chordal.Equivalence
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
public import Purelib.RationalFunctions.Curve.Basic

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Projective.Line (Proj)

section
@[expose] public section

/-!
# Quantitative projective bounds for finite rational curves

The homogeneous numerator and denominator of a rational curve are ordinary
finite coordinate polynomials.  Componentwise Horner bounds therefore give
an explicit Lipschitz coefficient for their projective cross product.  Once
the denominator coordinates carry a positive Bézout clearance on a bounded
parameter interval, this becomes a squared-chordal image bound proportional
to the square of the parameter width.

No affine division, square root, completed point, or limiting argument is
used.  The result is the finite shrinking-cylinder estimate needed to compare
a persistent curve event with a simultaneously shrinking winding box.
-/

namespace Purelib.RationalFunctions.Curve.Projective

open Purelib.Data
open Purelib.Geometry
open Purelib.RationalFunctions
/-- Evaluate the curve as the homogeneous pair of numerator and denominator values. -/
def projective (curve : Curve.RationalCurve) (parameter :
  Rational) : Projective.Line.GaussianLine :=
  ⟨curve.numeratorAt parameter, curve.denominatorAt parameter⟩

/-- At a nonzero denominator, the homogeneous curve value is equivalent to its affine point. -/
theorem projective_equivalent_affine
    (curve : Curve.RationalCurve) (parameter : Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (projective curve parameter).Equivalent
      (Proj.affine (curve.point parameter)) := by
  dsimp only [projective, Projective.Line.Proj.Equivalent, Proj.affine]
  rw [Gaussian.Basic.mul_one]
  exact curve.numeratorAt_eq_point_mul_denominatorAt parameter
    denominatorNonzero

/-- Replacing a non-pole homogeneous curve value by its affine point preserves squared chordal distance. -/
theorem chordalSq_projective_eq_affine
    (curve : Curve.RationalCurve) (parameter : Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0)
    (other : Projective.Line.GaussianLine) :
    Projective.Chordal.Basic.chordalSq (projective curve parameter) other =
      Projective.Chordal.Basic.chordalSq
        (Proj.affine (curve.point parameter)) other := by
  exact Projective.Chordal.Equivalence.chordalSq_eq_of_equivalent_left
    (Or.inr denominatorNonzero)
    (Projective.Line.Gaussian.Proj.affine_hasNonzeroCoordinate
      (curve.point parameter))
    (projective_equivalent_affine curve parameter denominatorNonzero) other
end Purelib.RationalFunctions.Curve.Projective

end
