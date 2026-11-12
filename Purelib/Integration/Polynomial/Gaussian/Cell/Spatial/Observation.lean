module

public import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial
public import Purelib.Geometry.Rational.Box.Segment
import Purelib.Data.Gaussian.Scale

/-!
# Original observation points of cached spatial cells

The shared segment coordinate supplies one actual point for all polynomial
pullbacks. Its point readback agrees with both the original local polynomial
and the original integration observation, preserving cached displacement.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Cell.Spatial

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Ascending.Gaussian

namespace Coordinate

/-- Read one actual point using the original shared segment's retained displacement. -/
@[expose] def point {start finish : Canonical} (coordinate : Coordinate start finish) (parameter : Rational) :
    Canonical :=
  start + Scale.scale parameter coordinate.displacement

/-- The shared point is the exact affine point of the original ordered endpoints. -/
theorem point_eq {start finish : Canonical} (coordinate : Coordinate start finish) (parameter : Rational) :
    coordinate.point parameter = start + (⟨parameter, 0⟩ : Canonical) * (finish - start) := by
  have scalar := Scale.scalar_mul_eq_scale parameter (finish - start)
  change (⟨parameter, 0⟩ : Canonical) * (finish - start) = Scale.scale parameter (finish - start) at scalar
  unfold point
  rewrite [coordinate.displacement_eq, ← scalar]
  rfl

/-- Every unit-parameter point remains in the original box containing this segment's endpoints. -/
theorem point_inside {start finish : Canonical} (coordinate : Coordinate start finish)
    {box : Geometry.Rational.Box} (startInside : box.Contains start) (finishInside : box.Contains finish)
    {parameter : Rational} (lower : 0 ≤ parameter) (upper : parameter ≤ 1) :
    box.Contains (coordinate.point parameter) := by
  rewrite [coordinate.point_eq]
  exact Geometry.Rational.Box.contains_line startInside finishInside ⟨lower, upper⟩

end Coordinate

namespace Pullback

/-- Read the actual original source polynomial at the shared cached segment point. -/
theorem eval_point {start finish : Canonical} {coordinate : Coordinate start finish}
    {source : Polynomial.Dense.Basic.DensePolynomial Canonical} {allowance : Rational}
    (pullback : Pullback coordinate source allowance) (parameter : Rational) :
    Evaluation.eval pullback.model.polynomial ⟨parameter, 0⟩ = source.eval (coordinate.point parameter) := by
  rewrite [coordinate.point_eq]
  exact pullback.eval_local ⟨parameter, 0⟩

/-- The original integration observation uses exactly the shared cached spatial point. -/
theorem observationPoint_eq {start finish : Canonical} {coordinate : Coordinate start finish}
    {source : Polynomial.Dense.Basic.DensePolynomial Canonical} {allowance : Rational}
    (pullback : Pullback coordinate source allowance)
    (observation : Basic.LocalObservation pullback.model.polynomial pullback.model.localAllowance) :
    Basic.CellModel.observationPoint pullback.model observation = coordinate.point observation.parameter := by
  unfold Basic.CellModel.observationPoint Basic.CellModel.displacement Coordinate.point
  rewrite [pullback.start_eq, pullback.finish_eq, coordinate.displacement_eq]
  rfl

end Pullback

end Purelib.Integration.Polynomial.Gaussian.Cell.Spatial

end
