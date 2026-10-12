module
public import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic

public import Purelib.CCL.Measure.Basic
public import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.CCL

open Purelib.Data.CCL.Encoding

open Purelib.Data.CCL.Encoding.Cylinder.Basic

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line.Basic

section
@[expose] public section

/-!
# Stability between finite CCL prefix realizations

Any two explicit realizations of the same completed CCL prefix are close in
squared chordal distance.  A supplied probe sensitivity certificate turns
that geometric fact into direct pointwise, L1, powered-Lp, and tail bounds
between two complete finite realization families.  No limiting CCL value is
chosen.
-/

namespace Purelib.Approximation.CCL.Prefix

open Purelib.CCL.Measure (Coordinate)

/-- Two explicit realizations of one finite prefix have probe separation at most the sensitivity-scaled cylinder spread.
-/
theorem realized_probe_separation_le
    {blocks : List Data.CCL.Encoding.Block} {leftPoint rightPoint : Line.GaussianLine}
    (leftRealizes : Cylinder.Basic.Realizes blocks leftPoint)
    (rightRealizes : Cylinder.Basic.Realizes blocks rightPoint)
    (probe : Line.GaussianLine → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Distance.rationalSeparation
        (probe leftPoint) (probe rightPoint) ≤
      factor * Cylinder.cylinderSpread blocks := by
  exact (sensitive leftPoint rightPoint).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Realizes.chordalSq_le_half_pow
        leftRealizes rightRealizes)
      factorNonnegative)
end Purelib.Approximation.CCL.Prefix

end
