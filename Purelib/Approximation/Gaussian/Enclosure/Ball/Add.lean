module
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite squared-error enclosures for constructive CCL arithmetic

The standalone CCL word remains a list of bits.  Arithmetic uses a proof
sidecar: a rational centre and a rational squared Euclidean error.  The
operations below transport these finite certificates directly.  They do not
name completed limits or collections of compatible points.
-/

namespace Purelib.Approximation.Gaussian.Enclosure.Ball
section Ball

/-- Negate a ball's centre while retaining its exact squared-error allowance. -/
def neg (ball : Ball) : Ball :=
  { center := -ball.center
    radiusSq := ball.radiusSq
    radiusSq_nonneg := ball.radiusSq_nonneg }

/-- Negation sends every admitted reading to an admitted reading of the negated ball. -/
theorem contains_neg {ball : Ball} {value :
  Data.Gaussian.Basic.Canonical}
    (inside : ball.Contains value) : ball.neg.Contains (-value) := by
  unfold Contains at inside ⊢
  change Data.Gaussian.Norm.Basic.normSq (-value - -ball.center) ≤ ball.radiusSq
  have difference : -value - -ball.center = -(value - ball.center) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.neg_re,
        Data.Gaussian.Basic.neg_im] <;> ring1
  rw [difference, Data.Gaussian.Norm.Basic.normSq_neg]
  exact inside

/-- Addition requires no magnitude bound. The factor two is the rational square-root-free triangle estimate. -/
def add (left right : Ball) : Ball
  :=
  { center := left.center + right.center
    radiusSq := 2 * (left.radiusSq + right.radiusSq)
    radiusSq_nonneg :=
      Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg left.radiusSq_nonneg right.radiusSq_nonneg) }

/-- The sum ball admits sums of readings admitted by its two original balls. -/
theorem contains_add {left right : Ball} {x y
  : Data.Gaussian.Basic.Canonical}
    (xInside : left.Contains x) (yInside : right.Contains y) :
    (left.add right).Contains (x + y) := by
  have difference :
      x + y - (left.center + right.center) =
        (x - left.center) + (y - right.center) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im] <;> ring1
  unfold Contains add
  rw [difference]
  calc
    Data.Gaussian.Norm.Basic.normSq ((x - left.center) + (y - right.center)) ≤
        2 * (Data.Gaussian.Norm.Basic.normSq (x - left.center) + Data.Gaussian.Norm.Basic.normSq (y -
          right.center)) :=
      Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * (left.radiusSq + right.radiusSq) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add xInside yInside) (by decide)

/-- Subtract balls by adding the left ball to the negated right ball. -/
def sub (left right : Ball) : Ball
  := left.add right.neg

/-- The difference ball admits differences of readings admitted by its two original balls. -/
theorem contains_sub {left right : Ball} {x y
  : Data.Gaussian.Basic.Canonical}
    (xInside : left.Contains x) (yInside : right.Contains y) :
    (left.sub right).Contains (x - y) := by
  have negInside := contains_neg yInside
  have sumInside := contains_add xInside negInside
  have valueIdentity : x + -y = x - y := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im] <;> ring1
  simpa only [sub, valueIdentity] using sumInside
end Ball

end Purelib.Approximation.Gaussian.Enclosure.Ball

end
