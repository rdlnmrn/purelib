module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Box
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Coprime.Basic (CoprimeCertificate)

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
public section

/-!
# Quantitative finite bounds for two coprime polynomials

This module extracts the reusable two-polynomial content of the squarefree
derivative-margin argument.  A displayed Bézout certificate gives an explicit
threshold below which a small value of the left polynomial forces a positive
lower bound for the right polynomial.  Applying the estimate to every point
of a sufficiently refined winding-one box supplies boundary clearance and
zero winding for the other polynomial.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Protection

/-- A positive request small enough to force the left residual threshold and
make the right polynomial locally constant in winding. -/
@[expose] def protectionRadius
    {p q : CoefficientPolynomial} (coprime :
      CoprimeCertificate p q)
    (pAmbient : Box) : Fraction.Rational :=
  min 1 (min
    (Dense.Gaussian.Coprime.Bounds.Box.leftThreshold coprime pAmbient /
      (8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient))
    (Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient /
      (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient)))

/-- The coprimality protection radius is positive.

Both residual and derivative ratios have positive numerators and positive Lipschitz denominators. -/
theorem protectionRadius_pos
    {p q : CoefficientPolynomial} (coprime :
      CoprimeCertificate p q)
    (pAmbient : Box) : 0 < protectionRadius coprime pAmbient :=
      by
  exact Purelib.Data.Rat.Fraction.Order.Basic.lt_min (by decide) (Purelib.Data.Rat.Fraction.Order.Basic.lt_min
    (Fraction.Order.Field.div_pos_direct
      (Dense.Gaussian.Coprime.Bounds.Box.leftThreshold_pos coprime pAmbient)
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
        (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p pAmbient)))
    (Fraction.Order.Field.div_pos_direct
      (Dense.Gaussian.Coprime.Bounds.Box.rightMargin_pos coprime pAmbient)
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
        (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos q pAmbient))))

end Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Protection

section
namespace Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Protection

/-- The square of the protection radius is at most the radius.

The radius is positive and its defining minimum bounds it by one. -/
theorem protectionRadius_sq_le
    {p q : CoefficientPolynomial} (coprime :
      CoprimeCertificate p q)
    (pAmbient : Box) :
    protectionRadius coprime pAmbient ^ 2 ≤
      protectionRadius coprime pAmbient := by
  let radius := protectionRadius coprime pAmbient
  have radiusPositive : 0 < radius := protectionRadius_pos coprime pAmbient
  have radiusLeOne : radius ≤ 1 := Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _
  rw [pow_two]
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    radiusLeOne radiusPositive.le).trans_eq (_root_.one_mul radius)
end Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Protection
end

namespace Purelib.Polynomial.CoprimeBounds

end Purelib.Polynomial.CoprimeBounds

end
