module

import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Antiderivative
public import Purelib.Polynomial.Dense.Gaussian.Antiderivative.Bounds
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

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

namespace Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate

set_option genInjectivity false in
/-- A retained dense primitive with its exact derivative and quadratic remainder ceiling.

The original polynomial and box index the derivative readback and every contained endpoint increment; the ceiling is
nonnegative and bounds the same cached primitive. -/
structure DensePrimitive (polynomial :
  CoefficientPolynomial) (box : Box) where
  /-- The retained finite dense primitive polynomial. -/ value :
    CoefficientPolynomial
  /-- Derivative evaluation of the retained primitive equals the original polynomial at every displayed point. -/
    derivative_eq : forall point, (Dense.Gaussian.GCD.derivative value).eval point = polynomial.eval point
  /-- The retained uniform quadratic-remainder ceiling on the original box. -/ remainderBound : Fraction.Rational
  /-- The retained remainder ceiling is nonnegative. -/ remainderBound_nonnegative : 0 ≤ remainderBound
  /-- The primitive increment minus its first-order term is bounded in quadrance by the retained ceiling times the
    squared displacement quadrance. -/ increment_bound : ∀ {start finish : Gaussian.Basic.Canonical}, box.Contains start
    → box.Contains finish →
    Data.Gaussian.Norm.Basic.normSq (value.eval finish - value.eval start - polynomial.eval start * (finish -
      start)) ≤
      remainderBound * Data.Gaussian.Norm.Basic.normSq (finish - start) ^ 2

constructive_injectivity DensePrimitive

namespace DensePrimitive

/-- Compute the finite dense antiderivative and retain its exact derivative law and coefficient-computed box remainder
ceiling. -/
def ofPolynomial (polynomial :
  CoefficientPolynomial) (box : Box) :
    DensePrimitive
  polynomial box :=
  let value := Dense.Gaussian.Antiderivative.denseAntiderivative polynomial
  { value := value
    derivative_eq := Dense.Gaussian.Antiderivative.denseAntiderivative_derivative polynomial
    remainderBound := Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound value box
    remainderBound_nonnegative := (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound_pos _ _).le
    increment_bound := fun startInside finishInside =>
      Dense.Gaussian.Antiderivative.Bounds.denseAntiderivative_increment polynomial startInside finishInside }

end DensePrimitive

end Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate

end

section
@[expose] public section

/-!
# Primitive Taylor control from a coefficient derivative bound

Two finite segment estimates turn any checked derivative ceiling into a
quadratic remainder bound. The intermediate Horner remainder is used only
in the erased proof, not as the requested executable ceiling.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate

/-- Regard the displayed polynomial as a primitive of its finite derivative.
This auxiliary package occurs only in proofs of the following estimates. -/
public def derivativePrimitive (polynomial :
  CoefficientPolynomial) (box : Box) :
    DensePrimitive (Dense.Gaussian.GCD.derivative polynomial) box :=
  ⟨polynomial, fun _ => rfl, Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound polynomial box,
    (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound_pos _ _).le,
    fun firstInside lastInside =>
      Dense.Gaussian.Bounds.Box.Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
      polynomial lastInside firstInside⟩

end Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate

end
