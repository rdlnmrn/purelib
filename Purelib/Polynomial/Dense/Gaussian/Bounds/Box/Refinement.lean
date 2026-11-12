module

public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Gaussian.Bounds.Horner

/-! # Comparing the actual numerator folds on retained refined boxes

Both original folds use the same coefficient list and zero starting bounds.
Original box refinement bounds their radius inputs; the existing finite
Horner monotonicity proof then preserves both complete value/slope readings.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Box

open Purelib
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Rat

/-- Original box refinement bounds both readings of the SAME polynomial's actual retained Horner folds. -/
theorem denseHornerNormBounds_mono (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    {first last : Box} (refines : first.Refines last) :
    (denseHornerNormBounds polynomial first).value ≤ (denseHornerNormBounds polynomial last).value ∧
      (denseHornerNormBounds polynomial first).slope ≤ (denseHornerNormBounds polynomial last).slope :=
  Horner.fold_bounds_mono polynomial.coeffs first.normSqBound_nonneg
    (Geometry.Rational.Box.normSqBound_le_of_refines refines) ⟨0, 0⟩ ⟨0, 0⟩
    (Fraction.Order.Basic.le_refl _) (Fraction.Order.Basic.le_refl _)
    (Fraction.Order.Basic.le_refl _) (Fraction.Order.Basic.le_refl _)

end Purelib.Polynomial.Dense.Gaussian.Bounds.Box

end
