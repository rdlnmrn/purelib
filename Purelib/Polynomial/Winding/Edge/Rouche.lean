module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
public import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Components
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Comparison.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Comparison.Dominance
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic

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

namespace Purelib.Polynomial.Winding.Edge.Rouche

/-- Finite Cauchy-index comparison data for a polynomial and its perturbation along one affine path.

The two coordinate pairs are evaluated on the same origin, direction and parameter interval. -/
abbrev PolynomialLineData
    (p q : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
      Gaussian.Basic.Canonical)
    (a b : Fraction.Rational) :=
  Dense.Rational.CauchyIndex.Comparison.Basic.LineData (Dense.Gaussian.Path.Components.pathReal p origin direction)
    (Dense.Gaussian.Path.Components.pathImag p origin direction)
    (Dense.Gaussian.Path.Components.pathReal (p + q) origin direction)
    (Dense.Gaussian.Path.Components.pathImag (p + q) origin direction) a b

/-- Convert geometric boundary dominance and two path clearances into the
finite Rouché data for one increasing affine side. -/
theorem lineData_of_boundaryNormDominance
    (p q : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Box)
    (dominance : Clearance.Box.Dominance.Basic.BoundaryNormDominance p q box)
    (origin direction : Gaussian.Basic.Canonical) {a b : Fraction.Rational}
    (proper : a < b)
    (left : Clearance.Pair.Basic.Certificate
      (Dense.Gaussian.Path.Components.pathReal p origin direction) (Dense.Gaussian.Path.Components.pathImag p origin
        direction)
      ⟨a, b, proper.le⟩)
    (onBoundary : ∀ t : Fraction.Rational,
      Data.Rat.Interval.Bounds.Contains ⟨a, b, proper.le⟩ t →
        Box.Boundary.OnBoxBoundary box
          (Affine.line origin direction t)) :
    PolynomialLineData p q origin direction a b := by
  apply Dense.Rational.CauchyIndex.Comparison.Dominance.lineData_of_normDominance
    (C := Dense.Gaussian.Path.Components.pathReal q origin direction)
    (D := Dense.Gaussian.Path.Components.pathImag q origin direction)
    proper left
    dominance.margin dominance.positive
  · intro t inside
    have lower := dominance.lower (Affine.line origin direction t)
      (onBoundary t inside)
    rw [Dense.Gaussian.Path.Components.eval_pathReal, Dense.Gaussian.Path.Components.eval_pathImag,
      Dense.Gaussian.Path.Components.eval_pathReal, Dense.Gaussian.Path.Components.eval_pathImag]
    simpa only [Gaussian.Basic.Canonical.normSq, pow_two] using lower
  · intro t
    rw [Dense.Gaussian.Path.Components.eval_pathReal, Dense.Gaussian.Path.Components.eval_pathReal,
      Dense.Gaussian.Path.Components.eval_pathReal, Dense.Basic.DensePolynomial.eval_add]
    rfl
  · intro t
    rw [Dense.Gaussian.Path.Components.eval_pathImag, Dense.Gaussian.Path.Components.eval_pathImag,
      Dense.Gaussian.Path.Components.eval_pathImag, Dense.Basic.DensePolynomial.eval_add]
    rfl
end Purelib.Polynomial.Winding.Edge.Rouche

end
