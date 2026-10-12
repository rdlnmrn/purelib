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
      Data.Gaussian.Norm.Basic.normSq (factor.eval (point * (Gaussian.Cast.Path.ofCoordinate parameter) ^ degree
        ramified) + (degree ramified : Gaussian.Basic.Canonical) *
        (point * (Gaussian.Cast.Path.ofCoordinate parameter) ^ degree ramified) *
          (Dense.Derivative.derivative factor).eval (point * (Gaussian.Cast.Path.ofCoordinate parameter) ^ degree
            ramified)) ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq (factor.eval point) ≤ 2 * bound := open Purelib in open
      Purelib.Geometry.Rational in by
  let value := Dense.Gaussian.Radial.radial factor point ramified
  let primitive : Dense.Gaussian.Primitive.Certificate.DensePrimitive (Dense.Derivative.derivative value)
    Affine.UnitSegment.unitBox :=
    { value := value
      derivative_eq := fun _ => rfl
      remainderBound := Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound value
        Affine.UnitSegment.unitBox
      remainderBound_nonnegative := (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound_pos _ _).le
      increment_bound := fun firstInside lastInside =>
        Dense.Gaussian.Bounds.Box.Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound value lastInside
          firstInside }
  let interval : Data.Rat.Interval.Bounds := ⟨0, 1, by decide⟩
  have inside (parameter : Fraction.Rational) (contained : interval.Contains parameter) :
      Affine.UnitSegment.unitBox.Contains (Affine.line 0 1 parameter) := by
    rw [Affine.UnitSegment.unit_line]
    exact ⟨contained.1, contained.2, le_rfl, le_rfl⟩
  have coefficientBound (parameter : Fraction.Rational) (contained : interval.Contains parameter) :
      Data.Gaussian.Norm.Basic.normSq ((Dense.Derivative.derivative value).eval (Affine.line 0 1 parameter)) ≤ bound
        := by
    rw [Affine.UnitSegment.unit_line]
    change Data.Gaussian.Norm.Basic.normSq ((Dense.Derivative.derivative (Dense.Gaussian.Radial.radial factor point
      ramified)).eval (Gaussian.Cast.Path.ofCoordinate parameter)) ≤ bound
    rw [Dense.Gaussian.Radial.radial_derivative]
    exact controlled parameter contained
  have estimate := Dense.Gaussian.Primitive.Segment.Bounds.DensePrimitive.segment_increment_le primitive 0 1 interval
    inside bound coefficientBound
    (first := 1) (last := 0) (by exact ⟨by decide, le_rfl⟩) (by exact ⟨le_rfl, by decide⟩)
  change Data.Gaussian.Norm.Basic.normSq (value.eval (Affine.line 0 1 1) - value.eval (Affine.line 0 1 0)) ≤ _
    at estimate
  rw [Affine.UnitSegment.unit_line, Affine.UnitSegment.unit_line] at estimate
  change Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Radial.radial factor point ramified).eval 1 -
    (Dense.Gaussian.Radial.radial factor point ramified).eval 0) ≤ _ at estimate
  simpa only [Dense.Gaussian.Radial.radial_one, Dense.Gaussian.Radial.radial_zero, Gaussian.Basic.sub_zero,
    Gaussian.Norm.Basic.normSq_one,
    show (1 : Fraction.Rational) - 0 = 1 by decide, _root_.one_pow,
    Fraction.Field.mul_one_direct] using estimate

end Purelib.Polynomial.Dense.Gaussian.Radial.Bounds
