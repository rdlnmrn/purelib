module
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Dense.Gaussian.Antiderivative
import Purelib.Polynomial.Dense.Gaussian.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite antiderivatives of dense Gaussian polynomials

Connect the existing low-to-high polynomial integrator to the dense
high-to-low polynomial algebra.  The derivative identity is proved by finite
Horner induction.  The existing finite Taylor estimate then bounds local
primitive increments, without analytic limits or infinite series.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Antiderivative.Bounds

/-- A primitive's increment has a quadratic Taylor remainder on every
displayed rational box.  This is the finite local estimate used by meshes. -/
theorem denseAntiderivative_increment (polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) {box : Geometry.Rational.Box}
    {start finish : Gaussian.Basic.Canonical} (startInside : box.Contains start) (finishInside : box.Contains finish) :
    Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Antiderivative.denseAntiderivative polynomial).eval finish -
      (Dense.Gaussian.Antiderivative.denseAntiderivative polynomial).eval start -
        polynomial.eval start * (finish - start)) <=
      Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound (Dense.Gaussian.Antiderivative.denseAntiderivative
        polynomial) box * Data.Gaussian.Norm.Basic.normSq (finish - start) ^ 2 := by
  have bound := Dense.Gaussian.Bounds.Box.Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
    (Dense.Gaussian.Antiderivative.denseAntiderivative polynomial) finishInside startInside
  rw [Dense.Gaussian.Antiderivative.denseAntiderivative_derivative] at bound
  exact bound

end Purelib.Polynomial.Dense.Gaussian.Antiderivative.Bounds

end
