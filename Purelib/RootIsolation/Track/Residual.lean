module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual.Radius
import Purelib.Polynomial.Winding.Box.Residual
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Residual readback from a retained track refinement

The original track is refined at its computed radius. Its stored accuracy
and the ambient Lipschitz certificate bound that same anchor residual.
-/

namespace Purelib.RootIsolation.Track.Residual

/-- A retained track refinement produces an anchor with the requested residual.

The positive threshold determines the same refinement radius and track call.
Its stored accuracy and ambient Lipschitz estimate bound the winding-one
state's original polynomial evaluation at that retained anchor. -/
public theorem refined_anchor_residual_le
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : Basic.WindingOneTrack p ambient)
    (current : State.WindingOne.Basic.WindingOneState p ambient) {threshold :
      Fraction.Rational}
    (thresholdPositive : 0 < threshold) :
    let radius := Dense.Gaussian.Bounds.Box.Residual.Radius.residualRefinementRadius p ambient threshold
    let refined := track.refine current radius
      (Dense.Gaussian.Bounds.Box.Residual.Radius.residualRefinementRadius_pos p ambient thresholdPositive)
    Data.Gaussian.Norm.Basic.normSq (p.eval refined.box.anchor) ≤ threshold := by
  let radius := Dense.Gaussian.Bounds.Box.Residual.Radius.residualRefinementRadius p ambient threshold
  let radiusPositive := Dense.Gaussian.Bounds.Box.Residual.Radius.residualRefinementRadius_pos p ambient
    thresholdPositive
  let refined := track.refine current radius radiusPositive
  have residual :=
    Winding.Box.Residual.anchor_residual_le_of_quadrupledBoxWinding_ne_zero p degreePositive
      refined.refinesAmbient refined.proper refined.raw.rawWinding_ne
  have diagonal := track.accurate current radius radiusPositive
  calc
    Data.Gaussian.Norm.Basic.normSq (p.eval refined.box.anchor) ≤
        Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient refined.box := residual
    _ = Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * refined.box.diagonalSq := rfl
    _ ≤ Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * radius ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct diagonal
        (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient).le
    _ ≤ threshold := Dense.Gaussian.Bounds.Box.Residual.Radius.lipschitz_mul_residualRadius_sq_le p ambient
      thresholdPositive

end Purelib.RootIsolation.Track.Residual
