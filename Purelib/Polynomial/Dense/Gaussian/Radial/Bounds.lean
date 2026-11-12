module
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
public import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Affine.UnitSegment
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Bounds
import Purelib.Polynomial.Dense.Gaussian.Radial
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Primitive.Parity

public section

/-!
# Finite radial bounds for a primitive factor

Integrate the finite polynomial u G(w u^e) on the displayed unit segment,
where e is one or two. The existing finite subdivision estimate gives a
bound for G(w) from its Euler differential expression. The auxiliary
polynomial is used only in the proof; executable callers retain their
original factor and a refinement-independent numerical ceiling.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Radial.Bounds

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial

open Purelib.Polynomial.Dense.Gaussian.Primitive.Parity (degree)

/-- A ceiling for a scaled radial derivative bounds the same scaled factor at its retained point.

The finite polynomial is multiplier times s times factor(point times s to
its selected degree). Its primitive certificate retains that exact value;
finite subdivision removes its Taylor remainder on the rational unit segment.
-/
theorem scaled_factor_bound (multiplier : Gaussian.Basic.Canonical)
    (factor : Basic.CanonicalCoefficients.CoefficientPolynomial) (point : Gaussian.Basic.Canonical)
    (ramified : Bool) (bound : Fraction.Rational)
    (controlled : ∀ parameter : Fraction.Rational, 0 ≤ parameter ∧ parameter ≤ 1 →
      Gaussian.Norm.Basic.normSq (multiplier *
        (factor.eval (point * (Gaussian.Cast.Path.ofCoordinate parameter) ^ degree ramified) +
          (degree ramified : Gaussian.Basic.Canonical) *
            (point * (Gaussian.Cast.Path.ofCoordinate parameter) ^ degree ramified) *
              (Derivative.derivative factor).eval
                (point * (Gaussian.Cast.Path.ofCoordinate parameter) ^ degree ramified))) ≤ bound) :
    Gaussian.Norm.Basic.normSq (multiplier * factor.eval point) ≤ 2 * bound := open Purelib in open
      Purelib.Geometry.Rational in by
  let value := Dense.Basic.DensePolynomial.scale multiplier (radial factor point ramified)
  let primitive : Primitive.Certificate.DensePrimitive (Derivative.derivative value)
      Affine.UnitSegment.unitBox :=
    Primitive.Certificate.derivativePrimitive value Affine.UnitSegment.unitBox
  let interval : Interval.Bounds := ⟨0, 1, by decide⟩
  have inside (parameter : Fraction.Rational) (contained : interval.Contains parameter) :
      Affine.UnitSegment.unitBox.Contains (Affine.line 0 1 parameter) := by
    rw [Affine.UnitSegment.unit_line]
    exact ⟨contained.1, contained.2, (Fraction.Order.Basic.le_refl _), (Fraction.Order.Basic.le_refl _)⟩
  have coefficientBound (parameter : Fraction.Rational) (contained : interval.Contains parameter) :
      Gaussian.Norm.Basic.normSq ((Derivative.derivative value).eval (Affine.line 0 1 parameter)) ≤ bound := by
    rw [Affine.UnitSegment.unit_line]
    change Gaussian.Norm.Basic.normSq
      ((Derivative.derivative (Dense.Basic.DensePolynomial.scale multiplier
        (radial factor point ramified))).eval (Gaussian.Cast.Path.ofCoordinate parameter)) ≤ bound
    rw [Derivative.eval_derivative_scale, radial_derivative]
    exact controlled parameter contained
  have estimate := Primitive.Segment.Bounds.DensePrimitive.segment_increment_le primitive 0 1 interval
    inside bound coefficientBound
    (first := 1) (last := 0) ⟨by decide, (Fraction.Order.Basic.le_refl _)⟩ ⟨(Fraction.Order.Basic.le_refl _), by decide⟩
  change Gaussian.Norm.Basic.normSq
    (value.eval (Affine.line 0 1 1) - value.eval (Affine.line 0 1 0)) ≤ _ at estimate
  rw [Affine.UnitSegment.unit_line, Affine.UnitSegment.unit_line] at estimate
  change Gaussian.Norm.Basic.normSq
    ((Dense.Basic.DensePolynomial.scale multiplier (radial factor point ramified)).eval 1 -
      (Dense.Basic.DensePolynomial.scale multiplier (radial factor point ramified)).eval 0) ≤ _ at estimate
  simpa only [Dense.Basic.DensePolynomial.eval_scale, radial_one, radial_zero,
    Gaussian.Basic.mul_zero, Gaussian.Basic.sub_zero, Gaussian.Norm.Basic.normSq_one,
    show (1 : Fraction.Rational) - 0 = 1 by decide, _root_.one_pow,
    Fraction.Field.mul_one_direct] using estimate

open Purelib.Polynomial.Dense.Gaussian.Primitive.Parity in
open _root_.Purelib.Polynomial.Dense.Gaussian.Primitive.Parity renaming CanonicalScalar -> Gaussian in
open _root_.Purelib.Polynomial.Dense.Gaussian.Primitive.Parity renaming CoefficientPolynomial -> Dense in
/-- A uniform ceiling on the factor's Euler expression bounds its value at the retained point.

For selected degree one or two, the supplied ceiling holds at every real unit-interval parameter. Finite polynomial
integration gives twice that ceiling for the squared norm at the point. -/
theorem factor_bound (factor : Basic.CanonicalCoefficients.CoefficientPolynomial) (point : Gaussian.Basic.Canonical)
  (ramified : Bool)
  (bound : Fraction.Rational)
    (controlled : ∀ parameter : Fraction.Rational, 0 ≤ parameter ∧ parameter ≤ 1 →
      Gaussian.Norm.Basic.normSq (factor.eval (point * (Gaussian.Cast.Path.ofCoordinate parameter) ^ degree
        ramified) + (degree ramified : Gaussian.Basic.Canonical) *
        (point * (Gaussian.Cast.Path.ofCoordinate parameter) ^ degree ramified) *
          (Derivative.derivative factor).eval (point * (Gaussian.Cast.Path.ofCoordinate parameter) ^ degree
            ramified)) ≤ bound) :
    Gaussian.Norm.Basic.normSq (factor.eval point) ≤ 2 * bound := open Purelib in open
      Purelib.Geometry.Rational in by
  have estimate := scaled_factor_bound 1 factor point ramified bound (by
    intro parameter contained
    rw [Gaussian.Basic.one_mul]
    exact controlled parameter contained)
  simpa only [Gaussian.Basic.one_mul] using estimate

end Purelib.Polynomial.Dense.Gaussian.Radial.Bounds
