module
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Field
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Geometry.Rational.Affine
import Purelib.Tactic.Ring

/-!
# Quantitative chords for variable-radicand square-root traces

A sufficiently short chord between two readings on the same sheet stays
away from zero.  Its square stays close to the radicand path when the initial
residual and radicand movement are small.  The estimates are homogeneous in
the root norm; there is no unit-norm restriction on the parameter.
-/

namespace Purelib.Riemann.RootContinuation.SquareRootTraceBounds

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Algebra

/-- The quadrance of a Gaussian sum is at most twice the sum of the quadrances.

The original two Gaussian readings retain their canonical coordinate norm.
The finite coordinate-square estimate controls their actual sum. -/
private theorem trace_normSq_add_le_two (left right : Basic.Canonical) :
    Basic.Canonical.normSq (left + right) ≤ 2 * (Basic.Canonical.normSq left + Basic.Canonical.normSq right) := by
  simpa only [Norm.Basic.normSq_eq_canonical] using
    Norm.Bounds.normSq_add_le_two left right
/-- The quadrance of a Gaussian difference is at most twice the sum of the quadrances.

Both original readings retain their canonical norm, and the same finite
coordinate-square estimate bounds their actual ordered difference. -/
private theorem trace_normSq_sub_le_two (left right : Basic.Canonical) :
    Basic.Canonical.normSq (left - right) ≤ 2 * (Basic.Canonical.normSq left + Basic.Canonical.normSq right) := by
  simpa only [Norm.Basic.normSq_eq_canonical] using
    Norm.Bounds.normSq_sub_le_two left right

/-- The rational scalar type for chord parameters and error bounds. -/
public abbrev Coordinate := Fraction.Rational
/-- The executable Gaussian rational type for root and radicand readings. -/
public abbrev Gaussian := Basic.Canonical

/-- A unit-interval chord point moves from its start by no more quadrance than the full edge.

The same rational parameter lies between zero and one. Its squared factor
contracts the original endpoint displacement, without selecting a new point. -/
private theorem chord_movement (start finish : Basic.Canonical) {time : Fraction.Rational}
    (inside : 0 ≤ time ∧ time ≤ 1) :
    Basic.Canonical.normSq (Rational.Affine.line start (finish - start) time - start) ≤ Basic.Canonical.normSq (finish -
      start) := by
  have squareLe : time ^ 2 ≤ 1 := by
    simpa only [one_pow] using Fraction.Order.Arithmetic.pow_le_pow_direct inside.1 inside.2 2
  have coordinateNorm : Basic.Canonical.normSq (Cast.Path.ofCoordinate time) = time ^ 2 := by
    simp only [Cast.Path.ofCoordinate, Basic.Canonical.normSq]
    ring1
  have displacement : Rational.Affine.line start (finish - start) time - start =
      Cast.Path.ofCoordinate time * (finish - start) := by
    rewrite [Rational.Affine.line]
    ring1
  rewrite [displacement, Basic.Canonical.normSq_mul, coordinateNorm]
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct squareLe (Basic.Canonical.normSq_nonneg
    _)).trans_eq (by ring1)

/-- A short chord retains between one quarter and four times the starting quadrance.

The endpoint difference has quadrance at most the starting quadrance divided by 1024, and the interpolation parameter
lies between zero and one. -/
public theorem chord_norm_bounds {start finish : Basic.Canonical} {time : Fraction.Rational}
    (distance : Basic.Canonical.normSq (finish - start) ≤ Basic.Canonical.normSq start / 1024)
    (inside : 0 ≤ time ∧ time ≤ 1) :
    Basic.Canonical.normSq start / 4 ≤ Basic.Canonical.normSq (Rational.Affine.line start (finish - start) time) ∧
    Basic.Canonical.normSq (Rational.Affine.line start (finish - start) time) ≤ 4 * Basic.Canonical.normSq start := by
  let point := Rational.Affine.line start (finish - start) time
  have movement := (chord_movement start finish inside).trans distance
  have quarter : Basic.Canonical.normSq (point - start) ≤ Basic.Canonical.normSq start / 4 := movement.trans
    (Fraction.Order.Field.div_le_div_of_nonneg_left_direct (Basic.Canonical.normSq_nonneg start)
      (by decide : (0 : Fraction.Rational) < 4) (by decide +kernel : (4 : Fraction.Rational) ≤ 1024))
  have whole : Basic.Canonical.normSq (point - start) ≤ Basic.Canonical.normSq start := movement.trans
    ((Fraction.Order.Field.div_le_div_of_nonneg_left_direct (Basic.Canonical.normSq_nonneg start)
      (by decide : (0 : Fraction.Rational) < 1) (by decide +kernel : (1 : Fraction.Rational) ≤ 1024)).trans_eq (by
        simp only [Field.ExplicitField.div_eq_mul_inv,
          show (1 : Fraction.Rational)⁻¹ = 1 from by decide]
        ring1))
  have upper : Basic.Canonical.normSq point ≤ 4 * Basic.Canonical.normSq start := by
    calc
      _ = Basic.Canonical.normSq (start + (point - start)) := by congr 1; ring1
      _ ≤ 2 * (Basic.Canonical.normSq start + Basic.Canonical.normSq (point - start)) := by
        simpa only [Norm.Basic.normSq_eq_canonical] using
          trace_normSq_add_le_two _ _
      _ ≤ 2 * (Basic.Canonical.normSq start + Basic.Canonical.normSq start) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) whole) (by
              decide : (0 : Fraction.Rational) ≤ 2)
      _ = _ := by ring1
  have reverse : Basic.Canonical.normSq start ≤ 2 * (Basic.Canonical.normSq point + Basic.Canonical.normSq start / 4) :=
    by
    calc
      _ = Basic.Canonical.normSq (point - (point - start)) := by congr 1; ring1
      _ ≤ 2 * (Basic.Canonical.normSq point + Basic.Canonical.normSq (point - start)) := trace_normSq_sub_le_two _ _
      _ ≤ _ := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) quarter) (by
            decide : (0 : Fraction.Rational) ≤ 2)
  refine ⟨?_, upper⟩
  apply (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : Fraction.Rational) < 4)).mpr
  have doubled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct reverse (by
      decide : (0 : Fraction.Rational) ≤ 2)
  calc
    _ = 2 * Basic.Canonical.normSq start - Basic.Canonical.normSq start := by ring1
    _ ≤ 2 * (2 * (Basic.Canonical.normSq point + Basic.Canonical.normSq start / 4)) - Basic.Canonical.normSq start :=
      Fraction.Order.Arithmetic.sub_le_sub_right_direct doubled _
    _ = 4 * Basic.Canonical.normSq point + (Basic.Canonical.normSq start / 4) * 4 - Basic.Canonical.normSq start := by
      ring1
    _ = _ := by
      rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide : (4 : Fraction.Rational) ≠ 0)]
      ring1

/-- Squaring a short root chord gives a uniform finite variation bound.

The squared endpoint displacement is at most the initial quadrance divided by 1024. Every unit-interval chord point's
squared-value difference is bounded by ten times that allowance times the initial quadrance. -/
public theorem chord_square_variation {start finish : Basic.Canonical} {time : Fraction.Rational}
    (distance : Basic.Canonical.normSq (finish - start) ≤ Basic.Canonical.normSq start / 1024)
    (inside : 0 ≤ time ∧ time ≤ 1) :
    Basic.Canonical.normSq ((Rational.Affine.line start (finish - start) time) ^ 2 - start ^ 2) ≤ 10 *
      Basic.Canonical.normSq start * (Basic.Canonical.normSq start / 1024) := by
  let point := Rational.Affine.line start (finish - start) time
  have bounds := chord_norm_bounds distance inside
  have movement := (chord_movement start finish inside).trans distance
  have sumBound : Basic.Canonical.normSq (point + start) ≤ 10 * Basic.Canonical.normSq start := by
    calc
      _ ≤ 2 * (Basic.Canonical.normSq point + Basic.Canonical.normSq start) := by
        simpa only [Norm.Basic.normSq_eq_canonical] using
          trace_normSq_add_le_two _ _
      _ ≤ 2 * (4 * Basic.Canonical.normSq start + Basic.Canonical.normSq start) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.add_le_add_right_direct bounds.2 (Basic.Canonical.normSq start)) (by
              decide : (0 : Fraction.Rational) ≤ 2)
      _ = _ := by ring1
  have identity : point ^ 2 - start ^ 2 = (point - start) * (point + start) := by ring1
  rw [identity, Basic.Canonical.normSq_mul]
  have product := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct movement (Basic.Canonical.normSq_nonneg
    (point + start))).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound
      (Fraction.Order.Field.div_nonneg_direct (Basic.Canonical.normSq_nonneg start) (by
          decide +kernel : (0 : Fraction.Rational) ≤ 1024)))
  exact product.trans_eq (by ring1)

/-- A short root chord's square remains within the displayed radicand error.

Root movement, initial residual and radicand movement obey their respective 1/1024 bounds relative to the initial
quadrance. The resulting squared residual is at most the initial quadrance squared divided by 32. -/
public theorem chord_square_residual {start finish parameterStart parameter : Basic.Canonical} {time :
  Fraction.Rational}
    (distance : Basic.Canonical.normSq (finish - start) ≤ Basic.Canonical.normSq start / 1024)
    (residual : Basic.Canonical.normSq (start ^ 2 - parameterStart) ≤ Basic.Canonical.normSq start ^ 2 / 1024)
    (parameterMovement : Basic.Canonical.normSq (parameter - parameterStart) ≤ Basic.Canonical.normSq start ^ 2 / 1024)
    (inside : 0 ≤ time ∧ time ≤ 1) :
    Basic.Canonical.normSq ((Rational.Affine.line start (finish - start) time) ^ 2 - parameter) ≤ Basic.Canonical.normSq
      start ^ 2 / 32 := by
  let point := Rational.Affine.line start (finish - start) time
  have moved := chord_square_variation distance inside
  have opposite : Basic.Canonical.normSq (parameterStart - parameter) = Basic.Canonical.normSq (parameter -
    parameterStart) := by
    have reversed : parameterStart - parameter = -(parameter - parameterStart) := by
      apply Basic.ext <;>
        simp only [Basic.sub_re, Basic.sub_im,
          Basic.neg_re, Basic.neg_im] <;> ring1
    rw [reversed, Basic.Canonical.normSq_neg]
  have tail : Basic.Canonical.normSq ((start ^ 2 - parameterStart) + (parameterStart - parameter)) ≤
      2 * (Basic.Canonical.normSq start ^ 2 / 1024 + Basic.Canonical.normSq start ^ 2 / 1024) := by
    apply (trace_normSq_add_le_two _ _).trans
    apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _ (by decide : (0 : Fraction.Rational) ≤ 2)
    rw [opposite]
    exact Fraction.Order.Arithmetic.add_le_add_direct residual parameterMovement
  calc
    _ = Basic.Canonical.normSq ((point ^ 2 - start ^ 2) + ((start ^ 2 - parameterStart) + (parameterStart - parameter)))
      := by congr 1; ring1
    _ ≤ 2 * (Basic.Canonical.normSq (point ^ 2 - start ^ 2) + Basic.Canonical.normSq ((start ^ 2 - parameterStart) +
      (parameterStart - parameter))) := by
        simpa only [Norm.Basic.normSq_eq_canonical] using
          trace_normSq_add_le_two _ _
    _ ≤ 2 * (10 * Basic.Canonical.normSq start * (Basic.Canonical.normSq start / 1024) +
        2 * (Basic.Canonical.normSq start ^ 2 / 1024 + Basic.Canonical.normSq start ^ 2 / 1024)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct moved
        tail) (by decide : (0 : Fraction.Rational) ≤ 2)
    _ = (28 / 1024 : Fraction.Rational) * Basic.Canonical.normSq start ^ 2 := by
      simp only [Field.ExplicitField.div_eq_mul_inv]
      ring1
    _ = (7 / 256 : Fraction.Rational) * Basic.Canonical.normSq start ^ 2 := by
      rw [show (28 / 1024 : Fraction.Rational) = 7 / 256 from by decide +kernel]
    _ ≤ (1 / 32 : Fraction.Rational) * Basic.Canonical.normSq start ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
          decide +kernel : (7 / 256 : Fraction.Rational) ≤ 1 / 32)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    _ = _ := by simp only [Field.ExplicitField.div_eq_mul_inv]; ring1

end Purelib.Riemann.RootContinuation.SquareRootTraceBounds
