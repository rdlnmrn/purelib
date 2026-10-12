module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
public import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Clearance.Pair.Basic
public import Purelib.Polynomial.Clearance.Pair.Dominance
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

namespace Purelib.Polynomial.Clearance.Box.Dominance.Path

/-- Geometric boundary dominance directly supplies quantitative clearance
for the sum path on one displayed increasing side. -/
def sumCertificate_of_boundaryNormDominance
    (p q : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Box)
    (dominance : Clearance.Box.Dominance.Basic.BoundaryNormDominance p q box)
    (origin direction : Gaussian.Basic.Canonical) {a b : Fraction.Rational}
    (valid : a ≤ b)
    (onBoundary : ∀ t : Fraction.Rational,
      Data.Rat.Interval.Bounds.Contains ⟨a, b, valid⟩ t →
        Box.Boundary.OnBoxBoundary box
          (Affine.line origin direction t)) :
    Clearance.Pair.Basic.Certificate
      (Dense.Gaussian.Path.Components.pathReal (p + q) origin direction)
      (Dense.Gaussian.Path.Components.pathImag (p + q) origin direction) ⟨a, b, valid⟩ := by
  apply Clearance.Pair.Dominance.sumCertificate_of_normDominance
    (A := Dense.Gaussian.Path.Components.pathReal p origin direction)
    (B := Dense.Gaussian.Path.Components.pathImag p origin direction)
    (C := Dense.Gaussian.Path.Components.pathReal q origin direction)
    (D := Dense.Gaussian.Path.Components.pathImag q origin direction)
    dominance.margin dominance.positive
  · intro t inside
    have lower := dominance.lower (Affine.line origin direction t)
      (onBoundary t inside)
    rw [Dense.Gaussian.Path.Components.eval_pathReal, Dense.Gaussian.Path.Components.eval_pathImag,
      Dense.Gaussian.Path.Components.eval_pathReal, Dense.Gaussian.Path.Components.eval_pathImag]
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, Data.Gaussian.Norm.Basic.normSq,
      Gaussian.Basic.Canonical.normSq, pow_two] using lower
  · intro t
    rw [Dense.Gaussian.Path.Components.eval_pathReal, Dense.Gaussian.Path.Components.eval_pathReal,
      Dense.Gaussian.Path.Components.eval_pathReal, Dense.Basic.DensePolynomial.eval_add]
    rfl
  · intro t
    rw [Dense.Gaussian.Path.Components.eval_pathImag, Dense.Gaussian.Path.Components.eval_pathImag,
      Dense.Gaussian.Path.Components.eval_pathImag, Dense.Basic.DensePolynomial.eval_add]
    rfl

/-- Exact rational bound stored by one boundary-dominance path certificate.
Exposing the finite Horner majorant separately lets downstream transport
proofs compare one side at a time instead of reducing a complete four-side
boundary certificate. -/
@[simp] theorem sumCertificate_of_boundaryNormDominance_bound
    (p q : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Box)
    (dominance : Clearance.Box.Dominance.Basic.BoundaryNormDominance p q box)
    (origin direction : Gaussian.Basic.Canonical) {a b : Fraction.Rational}
    (valid : a ≤ b)
    (onBoundary : ∀ t : Fraction.Rational,
      Data.Rat.Interval.Bounds.Contains ⟨a, b, valid⟩ t →
        Box.Boundary.OnBoxBoundary box
          (Affine.line origin direction t)) :
    (sumCertificate_of_boundaryNormDominance p q box dominance
      origin direction valid onBoundary).bound =
      dominance.margin ^ 2 /
        (4 * max 1
          (Dense.Rational.Bounds.Horner.evalSqBound
              (Dense.Gaussian.Path.Components.pathReal p origin direction) ⟨a, b, valid⟩ +
            Dense.Rational.Bounds.Horner.evalSqBound
              (Dense.Gaussian.Path.Components.pathImag p origin direction) ⟨a, b, valid⟩)) := by
  rfl
end Purelib.Polynomial.Clearance.Box.Dominance.Path

end
