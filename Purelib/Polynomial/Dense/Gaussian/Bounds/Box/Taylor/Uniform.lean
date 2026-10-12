module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.List.NormBounds
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor.Uniform
import all Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor.Uniform

import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Bounds.Horner
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor.Uniform
open Purelib.Data.Gaussian

/-- The box Horner norm scan and Taylor scan have identical slope bounds.

Both scans use the same coefficient list and ambient squared-norm ceiling with zero initial accumulators. -/
theorem denseHornerNormTaylor_slope
    (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Box) :
    (Dense.Gaussian.Bounds.Box.denseHornerNormBounds polynomial box).slope =
      (Dense.Gaussian.Bounds.Box.Taylor.denseHornerTaylorNormBounds polynomial box).slope :=
  (Dense.Gaussian.Bounds.Taylor.Uniform.denseHornerNormTaylor_fields polynomial.coeffs box.normSqBound
    ⟨0, 0⟩ ⟨0, 0, 0⟩ rfl rfl).2

end Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor.Uniform

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor.Uniform
open Purelib.Data.Gaussian

/-- Uniform coefficient bounds dominate all three box Taylor bounds.

A nonnegative squared-norm ceiling on each coefficient bounds the value, slope and remainder components computed by the
exact Horner scan. -/
theorem denseHornerTaylor_le_uniform
    (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Box)
    {coefficientBound : Fraction.Rational}
    (bounded : Gaussian.List.NormBounds.CoefficientsNormLe polynomial.coeffs coefficientBound)
    (coefficientNonnegative : 0 ≤ coefficientBound) :
    let actual := Dense.Gaussian.Bounds.Box.Taylor.denseHornerTaylorNormBounds
      polynomial box
    let uniform := Dense.Gaussian.Bounds.Taylor.Uniform.uniformTaylorBounds polynomial.coeffs.length
      coefficientBound box.normSqBound
    actual.value ≤ uniform.value ∧ actual.slope ≤ uniform.slope ∧
      actual.remainder ≤ uniform.remainder := by
  simpa only [Dense.Gaussian.Bounds.Box.Taylor.denseHornerTaylorNormBounds,
    Dense.Gaussian.Bounds.Taylor.Uniform.uniformTaylorBounds] using
    Dense.Gaussian.Bounds.Taylor.Uniform.denseTaylorFold_le_uniform polynomial.coeffs ⟨0, 0, 0⟩ ⟨0, 0, 0⟩
      bounded coefficientNonnegative box.normSqBound_nonneg le_rfl le_rfl
      le_rfl le_rfl le_rfl le_rfl
end Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor.Uniform

end
