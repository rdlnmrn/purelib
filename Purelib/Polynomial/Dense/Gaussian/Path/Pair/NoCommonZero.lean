module
import Purelib.Data.Rat.Fraction
public import Purelib.Polynomial.Dense.Rational.Pair.Path.NoCommonZero
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Components
public import Purelib.Polynomial.Dense.Gaussian.Path.Pair

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.Rational.Pair.Path.Basic (PolynomialEdge)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

namespace Purelib.Polynomial.Dense.Rational.Pair.Path.Basic.PolynomialEdge

/-- Pointwise nonvanishing of an affine polynomial path gives the displayed
coordinate coprimality used by the constructive Sturm chain. -/
theorem ofLine_coprime_of_eval_ne_zero
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
      Gaussian.Basic.Canonical)
    (start stop : Fraction.Rational)
    (nonzero : ∀ t : Fraction.Rational, p.eval (Affine.line origin direction t) ≠ 0) :
    (PolynomialEdge.ofLine p origin direction start stop).Coprime := by
  intro t
  by_cases realZero :
      (PolynomialEdge.ofLine p origin direction start stop).realPart.eval t = 0
  · right
    intro imaginaryZero
    apply nonzero t
    apply Gaussian.Basic.ext
    · rw [← Dense.Gaussian.Path.Components.eval_pathReal]
      exact realZero
    · rw [← Dense.Gaussian.Path.Components.eval_pathImag]
      exact imaginaryZero
  · exact Or.inl realZero

/-- Conversely, displayed coordinate coprimality certifies pointwise
nonvanishing of the represented affine Gaussian path. -/
theorem eval_ne_zero_of_ofLine_coprime
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
      Gaussian.Basic.Canonical)
    (start stop t : Fraction.Rational)
    (coprime : (PolynomialEdge.ofLine p origin direction start stop).Coprime) :
    p.eval (Affine.line origin direction t) ≠ 0 := by
  intro zero
  rcases coprime t with realNonzero | imaginaryNonzero
  · apply realNonzero
    change (Dense.Gaussian.Path.Components.pathReal p origin direction).eval t = 0
    rw [Dense.Gaussian.Path.Components.eval_pathReal]
    exact congrArg (fun z : Gaussian.Basic.Canonical => z.re) zero
  · apply imaginaryNonzero
    change (Dense.Gaussian.Path.Components.pathImag p origin direction).eval t = 0
    rw [Dense.Gaussian.Path.Components.eval_pathImag]
    exact congrArg (fun z : Gaussian.Basic.Canonical => z.im) zero
end Purelib.Polynomial.Dense.Rational.Pair.Path.Basic.PolynomialEdge

end
