module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
public import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Bounds
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

public section

/-!
# Primitive Taylor control from a coefficient derivative bound

Two finite segment estimates turn any checked derivative ceiling into a
quadratic remainder bound. The intermediate Horner remainder is used only
in the erased proof, not as the requested executable ceiling.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Derivative.Bounds

/-- Bound the evaluation increment by a derivative ceiling on a rational box.

For two points inside the box, the squared norm of the polynomial increment is at most twice the derivative ceiling
times their squared distance. The segment remains inside the same box. -/
theorem eval_sub_eval_le_of_derivative_bound (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) {box :
  Box}
    {start finish : Gaussian.Basic.Canonical} (startInside : box.Contains start) (finishInside : box.Contains finish)
    (bound : Fraction.Rational) (bounded : ∀ point, box.Contains point →
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.GCD.derivative polynomial).eval point) ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq (polynomial.eval finish - polynomial.eval start) ≤ 2 * bound *
      Data.Gaussian.Norm.Basic.normSq (finish - start) := open Purelib in by
  have estimate := Dense.Gaussian.Primitive.Segment.Bounds.DensePrimitive.segment_increment_le
    (Dense.Gaussian.Primitive.Certificate.derivativePrimitive polynomial box) start (finish - start)
    (⟨0, 1, by decide⟩ : Data.Rat.Interval.Bounds) (fun _ inside =>
      Box.contains_line startInside finishInside inside)
    bound (fun point inside => bounded _ (Box.contains_line startInside finishInside inside))
    (first := 1) (last := 0) ⟨by decide, le_rfl⟩ ⟨le_rfl, by decide⟩
  rw [Affine.line_zero, Affine.line_one] at estimate
  dsimp only [Dense.Gaussian.Primitive.Certificate.derivativePrimitive] at estimate
  have unitWidth : (1 : Fraction.Rational) - 0 = 1 := by decide
  simpa only [unitWidth, _root_.one_pow, Fraction.Field.mul_one_direct] using estimate

end Purelib.Polynomial.Dense.Gaussian.Derivative.Bounds
