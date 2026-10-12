module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Bezout
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Winding bands from displayed rational residuals

A sufficiently small value of a squarefree polynomial at a displayed
Gaussian-rational sample gives a finite Newton certificate.  When supplied
with explicit rational displacement, Taylor, and containment budgets, the
selected eliminant-safe band has winding four and therefore starts a normal
shrinking track.

Nothing in this module turns a small residual, a winding count, or a Sturm
count into a root.  The only distinguished point is the supplied rational
anchor of `source`.
-/

namespace Purelib.RootIsolation.Newton.Restart.Displacement

/-- Sharper Newton displacement bound using the actual displayed rational
residual, rather than the coarser whole-source variation budget. -/
theorem newton_displacementResidualMargin
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient source : Box}
    {squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
    (newton : Dense.Gaussian.Newton.Box.Squarefree.NewtonCenterCertificate p ambient source squarefree) :
    Data.Gaussian.Norm.Basic.normSq (newton.point - source.anchor) ≤
      Data.Gaussian.Norm.Basic.normSq (p.eval source.anchor) /
        Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree ambient := open Purelib.Data.Rat in
          by
  have derivativeNormPositive :
      0 < Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.GCD.derivative p).eval source.anchor) :=
    Gaussian.Norm.Basic.normSq_pos newton.derivativeNonzero
  have marginPositive := Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin_pos squarefree ambient
  have inverseBound :
      (Data.Gaussian.Norm.Basic.normSq
        ((Dense.Gaussian.GCD.derivative p).eval source.anchor))⁻¹ ≤
      (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree ambient)⁻¹ :=
    Fraction.Order.Field.inv_le_inv_of_pos_direct marginPositive
      newton.derivativeLower
  rw [newton.point_eq,
    Dense.Gaussian.Newton.Box.Anchor.normSq_anchorNewtonCenter_sub_anchor newton.derivativeNonzero]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    inverseBound (Gaussian.Norm.Basic.normSq_nonneg (p.eval source.anchor))

end Purelib.RootIsolation.Newton.Restart.Displacement

end
