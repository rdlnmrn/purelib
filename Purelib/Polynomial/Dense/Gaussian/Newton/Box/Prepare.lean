module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

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

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Box.Prepare

/-- Construct the Newton certificate when the displayed point residual itself
meets the derivative threshold.  The enclosing-box residual majorant is still
retained for displacement accounting, but need not fit below the threshold. -/
def computeNewtonCenterOfPointResidualSeparated
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) {ambient small : Box}
    (separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p ambient)
    (refines : small.Refines ambient)
    (residual : Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) ≤
      Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small)
    (pointThreshold : Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) ≤ separation.threshold) :
    Dense.Gaussian.Newton.Box.Certificate.SeparatedNewtonCenterCertificate p ambient small separation := open
      Purelib.Data.Rat in by
  have anchorInside : ambient.Contains small.anchor :=
    refines.contains small.contains_anchor
  have derivativeLower := separation.lower anchorInside pointThreshold
  have derivativeNonzero :
      (Dense.Gaussian.GCD.derivative p).eval small.anchor ≠ 0 := by
    intro derivativeZero
    rw [derivativeZero, Gaussian.Norm.Basic.normSq_zero] at derivativeLower
    exact (not_lt_of_ge derivativeLower) separation.margin_pos
  have derivativeNormPositive :
      0 < Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.GCD.derivative p).eval small.anchor) :=
    Gaussian.Norm.Basic.normSq_pos derivativeNonzero
  have inverseBound :
      (Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.GCD.derivative p).eval small.anchor))⁻¹ ≤
        separation.margin⁻¹ :=
    Fraction.Order.Field.inv_le_inv_of_pos_direct
      separation.margin_pos derivativeLower
  exact
    { point := Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p small
      point_eq := rfl
      residual := residual
      derivativeNonzero := derivativeNonzero
      derivativeLower := derivativeLower
      displacement := by
        rw [Dense.Gaussian.Newton.Box.Anchor.normSq_anchorNewtonCenter_sub_anchor derivativeNonzero]
        exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          residual
          (Fraction.Order.Field.inv_pos_direct
            derivativeNormPositive).le
      displacementMargin := by
        rw [Dense.Gaussian.Newton.Box.Anchor.normSq_anchorNewtonCenter_sub_anchor derivativeNonzero]
        calc
          Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) *
                (Data.Gaussian.Norm.Basic.normSq
                  ((Dense.Gaussian.GCD.derivative p).eval small.anchor))⁻¹ ≤
              Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small *
                (Data.Gaussian.Norm.Basic.normSq
                  ((Dense.Gaussian.GCD.derivative p).eval small.anchor))⁻¹ :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
              residual
              (Fraction.Order.Field.inv_pos_direct
                derivativeNormPositive).le
          _ ≤ Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small * separation.margin⁻¹ :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              inverseBound (Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound_nonneg p ambient small)
          _ = Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small / separation.margin := rfl }

/-- Construct the Newton certificate from an enclosing residual estimate and
an explicit derivative-separation resource. -/
def computeNewtonCenterOfResidualSeparated
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) {ambient small : Box}
    (separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p ambient)
    (refines : small.Refines ambient)
    (residual : Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) ≤
      Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small)
    (threshold : Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small ≤
      separation.threshold) :
    Dense.Gaussian.Newton.Box.Certificate.SeparatedNewtonCenterCertificate p ambient small separation :=
  computeNewtonCenterOfPointResidualSeparated p separation refines residual
    (residual.trans threshold)
end Purelib.Polynomial.Dense.Gaussian.Newton.Box.Prepare

end
