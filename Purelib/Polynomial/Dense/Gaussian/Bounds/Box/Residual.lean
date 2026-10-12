module
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Bounds
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free local residual extraction

A fixed rational corner of a shrinking box supplies the local sample.  Finite
Horner bounds and the box diagonal bound its residual variation.  If that
sample value were larger than the variation, a finite Rouché contraction to
the nonzero constant path would force raw winding zero.  Thus every proper
nonzero-winding box has an explicitly small rational residual.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual

/-- Coefficient-computed upper bound for residual variation from the fixed
rational anchor of a subbox. -/
def anchorResidualBound (p :
  CoefficientPolynomial)
    (ambient small : Box) : Fraction.Rational :=
  Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * small.diagonalSq

/-- The ambient Lipschitz multiplier times the small box's squared diagonal is nonnegative. -/
theorem anchorResidualBound_nonneg (p :
  CoefficientPolynomial)
    (ambient small : Box) : 0 ≤ anchorResidualBound p ambient small
      :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient).le small.diagonalSq_nonneg

/-- Every point of the small box differs from its fixed rational anchor by at
most the displayed finite coefficient bound. -/
theorem normSq_eval_sub_anchor_le
    (p : CoefficientPolynomial) {ambient small : Box}
    (refines : small.Refines ambient) {z : Gaussian.Basic.Canonical}
    (inside : small.Contains z) :
    Data.Gaussian.Norm.Basic.normSq (p.eval z - p.eval small.anchor) ≤
      anchorResidualBound p ambient small := by
  have zAmbient : ambient.Contains z := refines.contains inside
  have anchorAmbient : ambient.Contains small.anchor :=
    refines.contains small.contains_anchor
  have variation := Dense.Gaussian.Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound
    p zAmbient anchorAmbient
  have distance := small.normSq_sub_anchor_le inside
  exact variation.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct distance
      (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient).le)
end Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual

end
