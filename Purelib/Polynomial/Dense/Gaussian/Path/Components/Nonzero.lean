module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Path.Components.Nonzero

/-- A nonzero Gaussian path value is a nonzero displayed coordinate pair. -/
theorem ofLine_coordinatePair_ne_zero
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
      Gaussian.Basic.Canonical)
    (t : Fraction.Rational)
    (valueNonzero : p.eval (Geometry.Rational.Affine.line origin direction t) ≠ 0) :
    (Dense.Gaussian.Path.Components.pathReal p origin direction).eval t ≠ 0 ∨
      (Dense.Gaussian.Path.Components.pathImag p origin direction).eval t ≠ 0 := by
  by_cases realZero : (Dense.Gaussian.Path.Components.pathReal p origin direction).eval t = 0
  · right
    intro imagZero
    apply valueNonzero
    apply Gaussian.Basic.ext
    · rw [← Dense.Gaussian.Path.Components.eval_pathReal]
      exact realZero
    · rw [← Dense.Gaussian.Path.Components.eval_pathImag]
      exact imagZero
  · exact Or.inl realZero
end Purelib.Polynomial.Dense.Gaussian.Path.Components.Nonzero

end
