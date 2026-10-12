module
import Purelib.Algebra.Field.Resource.Magnitude
import Purelib.Data.Rat.Fraction.Resource.Model
public import Purelib.Data.Rat.Interval.Candidates.Resource
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Resource
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Rational.Nonzero.Search.Resource
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.Polynomial.Elimination.Axis.Cuts

import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

/-!
# Magnitude of axis-safe cut coordinates

The vertical and horizontal eliminants select nonzero coordinates from finite interior lists. The supplied box bound
controls the endpoint representations and the resulting safe-cut envelope.
-/

namespace Purelib.Polynomial.Elimination.Axis.Cuts.Resource

open Purelib
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-- The selected vertical safe coordinate satisfies the finite safe-cut magnitude envelope.

The bound uses the retained box coordinate bound and the displayed vertical eliminant degree. -/
public theorem verticalSafeCoordinate_magnitude_le
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {degreeBound bound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (box : Box) (proper : box.Proper) (boxWithin : Box.Resource.BoxWithin box bound) :
    Fraction.Resource.Model.coordinateMagnitude
        (Elimination.Axis.Cuts.verticalSafeCoordinate elimination box proper) ≤
      Data.Rat.Interval.Candidates.Resource.safeCutMagnitudeEnvelope bound degreeBound := by
  have selected := Dense.Rational.Nonzero.Search.Resource.centralSearchValue_magnitude_le elimination.vertical
    degreeBound proper.1 elimination.vertical_nonzero elimination.vertical_degree
  unfold Elimination.Axis.Cuts.verticalSafeCoordinate
  exact selected.trans (Algebra.Field.Resource.Magnitude.grow_mono_bound Fraction.Resource.Model.rationalModel
    (Data.Rat.Interval.Candidates.Resource.intervalSource_le_safeCutSource boxWithin.1 boxWithin.2.1) 8)

/-- The selected horizontal safe coordinate satisfies the finite safe-cut magnitude envelope.

The bound uses the retained box coordinate bound and the displayed horizontal eliminant degree. -/
public theorem horizontalSafeCoordinate_magnitude_le
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {degreeBound bound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (box : Box) (proper : box.Proper) (boxWithin : Box.Resource.BoxWithin box bound) :
    Fraction.Resource.Model.coordinateMagnitude
        (Elimination.Axis.Cuts.horizontalSafeCoordinate elimination box proper) ≤
      Data.Rat.Interval.Candidates.Resource.safeCutMagnitudeEnvelope bound degreeBound := by
  have selected := Dense.Rational.Nonzero.Search.Resource.centralSearchValue_magnitude_le elimination.horizontal
    degreeBound proper.2 elimination.horizontal_nonzero
      elimination.horizontal_degree
  unfold Elimination.Axis.Cuts.horizontalSafeCoordinate
  exact selected.trans (Algebra.Field.Resource.Magnitude.grow_mono_bound Fraction.Resource.Model.rationalModel
    (Data.Rat.Interval.Candidates.Resource.intervalSource_le_safeCutSource boxWithin.2.2.1 boxWithin.2.2.2) 8)
end Purelib.Polynomial.Elimination.Axis.Cuts.Resource
