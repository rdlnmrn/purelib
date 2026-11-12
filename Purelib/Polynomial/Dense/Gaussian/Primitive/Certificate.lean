module

import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Antiderivative
public import Purelib.Polynomial.Dense.Gaussian.Antiderivative.Bounds
public import Purelib.Calculus.Jet.Quadratic.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
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

open Purelib.Calculus.Jet

/-- Compute the finite dense antiderivative and retain its exact derivative law and coefficient-computed box remainder
ceiling. -/
def ofPolynomial (polynomial :
  CoefficientPolynomial) (box : Box) :
    DensePrimitive
  polynomial box :=
  let value := Dense.Gaussian.Antiderivative.denseAntiderivative polynomial
  { value := value
    derivative_eq := Dense.Gaussian.Antiderivative.denseAntiderivative_derivative polynomial
    remainderBound := Bounds.Box.Taylor.denseTaylorRemainderBound value box
    remainderBound_nonnegative := (Bounds.Box.Taylor.denseTaylorRemainderBound_pos _ _).le
    increment_bound := fun startInside finishInside =>
      Dense.Gaussian.Antiderivative.Bounds.denseAntiderivative_increment polynomial startInside finishInside }

/-- Read the original quadratic certificate directly from the same retained primitive and box ceiling.

The displayed endpoint evaluations and the original coefficient evaluation
supply the base, output and slope. The original cached remainder ceiling is
retained literally, without repeating its coefficient fold.
-/
def quadraticCertificate {polynomial : CoefficientPolynomial} {box : Box}
    (primitive : DensePrimitive polynomial box) (start finish : Gaussian.Basic.Canonical)
    (startInside : box.Contains start) (finishInside : box.Contains finish) :
    Quadratic.Basic.Certificate (finish - start) :=
  { base := primitive.value.eval start
    slope := polynomial.eval start
    output := primitive.value.eval finish
    remainder := primitive.value.eval finish - primitive.value.eval start -
      (finish - start) * polynomial.eval start
    expansion := rfl
    factor := primitive.remainderBound
    factor_nonneg := primitive.remainderBound_nonnegative
    remainder_le := by
      rewrite [← Gaussian.Norm.Basic.normSq_eq_canonical, ← Gaussian.Norm.Basic.normSq_eq_canonical,
        Gaussian.Basic.mul_comm (finish - start)]
      exact primitive.increment_bound startInside finishInside }

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
  ⟨polynomial, fun _ => rfl, Bounds.Box.Taylor.denseTaylorRemainderBound polynomial box,
    (Bounds.Box.Taylor.denseTaylorRemainderBound_pos _ _).le,
    fun firstInside lastInside =>
      Bounds.Box.Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
      polynomial lastInside firstInside⟩

end Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate

end

public section

namespace Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate.DensePrimitive

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- Certify the same retained primitive on another box using its finite coefficient Taylor bound.

The original value polynomial and complete derivative law are passed through
literally. Only the box-dependent remainder ceiling is recomputed; no primitive
integration, root preparation or coefficient normalization is repeated.
-/
@[expose] def onBox {polynomial : CoefficientPolynomial} {box : Box}
    (primitive : DensePrimitive polynomial box) (target : Box) : DensePrimitive polynomial target :=
  { value := primitive.value
    derivative_eq := primitive.derivative_eq
    remainderBound := Bounds.Box.Taylor.denseTaylorRemainderBound primitive.value target
    remainderBound_nonnegative :=
      (Bounds.Box.Taylor.denseTaylorRemainderBound_pos primitive.value target).le
    increment_bound := fun firstInside lastInside => by
      have bound := Bounds.Box.Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
        primitive.value lastInside firstInside
      rewrite [primitive.derivative_eq] at bound
      exact bound }

/-- Changing the certified box retains the identical complete original primitive polynomial. -/
theorem onBox_value {polynomial : CoefficientPolynomial} {box : Box}
    (primitive : DensePrimitive polynomial box) (target : Box) :
    (primitive.onBox target).value = primitive.value := rfl

/-- A finite primitive increment follows a displayed tangent with its actual displacement and tangent-error bounds.

The two squared-error contributions remain separate: the primitive's retained
Taylor ceiling multiplies squared displacement quadrance, while the coefficient
quadrance multiplies the actual geometric tangent remainder.
-/
theorem increment_bound_with_tangent {polynomial : CoefficientPolynomial} {box : Box}
    (primitive : DensePrimitive polynomial box) {start finish step direction : Basic.Canonical}
    (startInside : box.Contains start) (finishInside : box.Contains finish)
    {movement tangentRemainder : Fraction.Rational}
    (movementBound : Norm.Basic.normSq (finish - start) ≤ movement)
    (tangentBound : Norm.Basic.normSq (finish - start - step * direction) ≤ tangentRemainder) :
    Norm.Basic.normSq (primitive.value.eval finish - primitive.value.eval start -
      step * (polynomial.eval start * direction)) ≤
        2 * (primitive.remainderBound * movement ^ 2 +
          Norm.Basic.normSq (polynomial.eval start) * tangentRemainder) := by
  have decomposition : primitive.value.eval finish - primitive.value.eval start -
      step * (polynomial.eval start * direction) =
        (primitive.value.eval finish - primitive.value.eval start - polynomial.eval start * (finish - start)) +
          polynomial.eval start * (finish - start - step * direction) := by ring1
  rewrite [decomposition]
  apply (Norm.Bounds.normSq_add_le_two _ _).trans
  apply Arithmetic.mul_le_mul_of_nonneg_left_direct _ (by decide +kernel)
  apply Arithmetic.add_le_add_direct
  · exact (primitive.increment_bound startInside finishInside).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg _) movementBound 2)
        primitive.remainderBound_nonnegative)
  · rewrite [Norm.Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_of_nonneg_left_direct tangentBound (Norm.Basic.normSq_nonneg _)

end Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate.DensePrimitive
