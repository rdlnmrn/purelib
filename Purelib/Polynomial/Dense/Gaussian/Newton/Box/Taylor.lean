module
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Box.Taylor

/-- The executable Taylor scan bounds the finite Newton error program. -/
theorem normSq_newtonError_le
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) {ambient source : Box}
    (sourceRefines : source.Refines ambient) {z : Gaussian.Basic.Canonical}
    (inside : ambient.Contains z)
    (derivativeNonzero :
      (Dense.Gaussian.GCD.derivative p).eval source.anchor ≠ 0) :
    Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Newton.Box.Linearization.newtonError p source).eval z) ≤
      Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient *
        Data.Gaussian.Norm.Basic.normSq (z - source.anchor) ^ 2 := by
  have anchorInside : ambient.Contains source.anchor :=
    sourceRefines.contains source.contains_anchor
  have taylor :=
    Dense.Gaussian.Bounds.Box.Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
      p inside anchorInside
  have errorIdentity : (Dense.Gaussian.Newton.Box.Linearization.newtonError p source).eval z =
      p.eval z - p.eval source.anchor -
        (Dense.Gaussian.GCD.derivative p).eval source.anchor *
          (z - source.anchor) := by
    rw [Dense.Gaussian.Newton.Box.Linearization.newtonError, Dense.Basic.DensePolynomial.eval_sub,
      Dense.Basic.DensePolynomial.eval_normalize,
      Dense.Gaussian.Newton.Box.Linearization.newtonLinearization_eval p source z derivativeNonzero]
    apply Gaussian.Basic.ext
    · change (p.eval z).re -
          ((p.eval source.anchor).re +
            ((Dense.Gaussian.GCD.derivative p).eval source.anchor *
              (z - source.anchor)).re) =
        ((p.eval z).re - (p.eval source.anchor).re) -
          ((Dense.Gaussian.GCD.derivative p).eval source.anchor *
            (z - source.anchor)).re
      ring1
    · change (p.eval z).im -
          ((p.eval source.anchor).im +
            ((Dense.Gaussian.GCD.derivative p).eval source.anchor *
              (z - source.anchor)).im) =
        ((p.eval z).im - (p.eval source.anchor).im) -
          ((Dense.Gaussian.GCD.derivative p).eval source.anchor *
            (z - source.anchor)).im
      ring1
  rw [errorIdentity]
  exact taylor
end Purelib.Polynomial.Dense.Gaussian.Newton.Box.Taylor

end
