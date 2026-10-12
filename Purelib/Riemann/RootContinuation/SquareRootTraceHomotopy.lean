module
import Purelib.Polynomial.Dense.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Affine.Segment
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Path.Components
public import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Comparison.Dominance
public import Purelib.Polynomial.Winding.Edge.Product
public import Purelib.Polynomial.Winding.Polygon.Comparison

import Purelib.Riemann.RootContinuation.SquareRootTraceBounds
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Finite winding comparison for short square-root traces

The homogeneous root-chord estimates construct path clearances and finite
Rouché formulas for any Gaussian polynomial along a base segment.  Neither
an exact square root nor a unit-norm radicand is required.  These are local
ingredients for a returned-owner trace, not an assertion that arbitrary
independently selected endpoint readings lie on the same sheet.
-/

namespace Purelib.Riemann.RootContinuation.SquareRootTraceHomotopy

open Purelib.Riemann.RootContinuation.SquareRootTraceBounds
  (chord_norm_bounds chord_square_variation chord_square_residual)

section
open Purelib.Riemann
/-- The rational scalar type used by the finite root-chord estimates. -/
private abbrev Coordinate := RootContinuation.SquareRootTraceBounds.Coordinate
/-- The executable Gaussian rational root and base-point type. -/
private abbrev Gaussian := RootContinuation.SquareRootTraceBounds.Gaussian

end

open Purelib.Polynomial in
/-- The dense Gaussian polynomial type for the compared base path. -/
abbrev GaussianPolynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Path

open Purelib.Data in
/-- The retained closed rational parameter interval from zero to one. -/
abbrev parameterInterval : Data.Rat.Interval.Bounds :=
  ⟨0, 1, by decide⟩

open Purelib.Data in
open Purelib.Polynomial in
/-- Construct positive finite clearance along a short root chord.

The starting root is nonzero and the endpoint displacement quadrance is at most its quadrance divided by 1024; one
quarter of the starting quadrance bounds the whole chord. -/
def chordClearance {start finish : Gaussian.Basic.Canonical} (nonzero : start ≠ 0)
    (distance : normSq (finish - start) ≤ normSq start / 1024) :
    Clearance.Pair.Basic.Certificate
      (Dense.Gaussian.Path.Components.pathReal Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial start (finish -
        start))
      (Dense.Gaussian.Path.Components.pathImag Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial start (finish -
        start))
      parameterInterval where
  bound := normSq start / 4
  positive := Rat.Fraction.Order.Field.div_pos_direct (show 0 < Gaussian.Basic.Canonical.normSq start from by
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using Gaussian.Norm.Basic.normSq_pos nonzero) (by decide)
  lower := by
    intro time inside
    have scalarBound := (chord_norm_bounds distance inside).1
    simpa only [Dense.Gaussian.Path.Components.eval_pathReal, Dense.Gaussian.Path.Components.eval_pathImag,
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial_eval, normSq, pow_two] using scalarBound

open Purelib.Data in
open Purelib.Geometry in
/-- Every point on the certified short root chord is nonzero. -/
theorem chord_nonzero {start finish : Gaussian.Basic.Canonical} (nonzero : start ≠ 0)
    (distance : normSq (finish - start) ≤ normSq start / 1024)
    {time : Rat.Fraction.Rational} (inside : parameterInterval.Contains time) :
    Rational.Affine.line start (finish - start) time ≠ 0 := by
  intro zero
  have bound := (chord_norm_bounds distance inside).1
  rw [zero, Gaussian.Basic.Canonical.normSq_zero] at bound
  exact (not_lt_of_ge bound) (chordClearance nonzero distance).positive

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Geometry in
/-- The squared short chord has quadrance at least the initial quadrance squared divided by sixteen. -/
theorem chord_square_lower {start finish : Gaussian.Basic.Canonical} {time : Rat.Fraction.Rational}
    (distance : normSq (finish - start) ≤ normSq start / 1024)
    (inside : parameterInterval.Contains time) :
    normSq start ^ 2 / 16 ≤ normSq ((Rational.Affine.line start (finish - start) time) ^ 2) := by
  have lower := Rat.Fraction.Order.Arithmetic.pow_le_pow_direct
    (Rat.Fraction.Order.Field.div_nonneg_direct (Gaussian.Basic.Canonical.normSq_nonneg start)
      (by decide : (0 : Rat.Fraction.Rational) ≤ 4))
    (chord_norm_bounds distance inside).1 2
  have quarterSquare : (normSq start / 4) ^ 2 = normSq start ^ 2 / 16 := by
    calc
      _ = normSq start ^ 2 * ((4 : Rat.Fraction.Rational)⁻¹) ^ 2 := by
        simp only [Field.ExplicitField.div_eq_mul_inv]
        ring1
      _ = _ := by
        rw [show ((4 : Rat.Fraction.Rational)⁻¹) ^ 2 = 16⁻¹ from by decide]
        rfl
  rw [quarterSquare] at lower
  have powerNorm : normSq ((Rational.Affine.line start (finish - start) time) ^ 2) =
      normSq (Rational.Affine.line start (finish - start) time) ^ 2 := by
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
      Gaussian.Power.normSq_pow
        (Rational.Affine.line start (finish - start) time) 2
  rw [powerNorm]
  exact lower

section
open Purelib.Data
open Purelib.Polynomial
open Purelib.Geometry
/-- Construct positive finite clearance for the square polynomial on the retained root chord. -/
def squaredChordClearance {start finish : Gaussian.Basic.Canonical} (nonzero : start ≠ 0)
    (distance : normSq (finish - start) ≤ normSq start / 1024) :
    Clearance.Pair.Basic.Certificate
      (Dense.Gaussian.Path.Components.pathReal (Dense.Gaussian.Power.Coordinate.coordinatePositivePower 1) start (finish
        - start))
      (Dense.Gaussian.Path.Components.pathImag (Dense.Gaussian.Power.Coordinate.coordinatePositivePower 1) start (finish
        - start))
      parameterInterval where
  bound := normSq start ^ 2 / 16
  positive := Rat.Fraction.Order.Field.div_pos_direct
    (Rat.Fraction.Order.Arithmetic.pow_pos_direct (show 0 < Gaussian.Basic.Canonical.normSq start from by
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using Gaussian.Norm.Basic.normSq_pos nonzero) 2) (by decide)
  lower := by
    intro time inside
    have scalarBound := chord_square_lower distance inside
    simp only [Dense.Gaussian.Path.Components.eval_pathReal,
      Dense.Gaussian.Path.Components.eval_pathImag,
      Dense.Gaussian.Power.Coordinate.coordinatePositivePower_eval]
    change normSq start ^ 2 / 16 ≤
      ((Rational.Affine.line start (finish - start) time) ^ 2).re ^ 2 +
        ((Rational.Affine.line start (finish - start) time) ^ 2).im ^ 2
    simpa only [normSq, pow_two] using scalarBound

/-- The checked root-chord clearance supplies the finite winding product formula for its square. -/
theorem chord_product_formula {start finish : Gaussian.Basic.Canonical} (nonzero : start ≠ 0)
    (distance : normSq (finish - start) ≤ normSq start / 1024) :
    Winding.Edge.Product.LineProductFormula
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
      start (finish - start) 0 1 := by
  have atZero : Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial.eval
      (Rational.Affine.line start (finish - start) 0) ≠ 0 := by
    simpa only [Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial_eval] using
      chord_nonzero nonzero distance (time := 0) ⟨le_rfl, by decide⟩
  have atOne : Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial.eval
      (Rational.Affine.line start (finish - start) 1) ≠ 0 := by
    simpa only [Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial_eval] using
      chord_nonzero nonzero distance (time := 1) ⟨by decide, le_rfl⟩
  exact Winding.Edge.Product.lineProductFormula_of_clearances _ _ _ _ (by decide)
    (chordClearance nonzero distance) (chordClearance nonzero distance)
    atZero atZero atOne atOne

end

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
/-- Construct the finite Rouché comparison between a squared root chord and a polynomial base segment.

The nonzero starting root, chord displacement, initial polynomial residual and pointwise base-segment movement obey the
displayed homogeneous bounds, yielding the same finite winding formula. -/
theorem segmentHomotopy (polynomial : GaussianPolynomial)
    {start finish baseStart baseFinish : Gaussian.Basic.Canonical} (nonzero : start ≠ 0)
    (distance : normSq (finish - start) ≤ normSq start / 1024)
    (residual : normSq (start ^ 2 - polynomial.eval baseStart) ≤ normSq start ^ 2 / 1024)
    (movement : ∀ time : Rat.Fraction.Rational, parameterInterval.Contains time →
      normSq (polynomial.eval (Rational.Affine.line baseStart (baseFinish - baseStart) time) -
        polynomial.eval baseStart) ≤ normSq start ^ 2 / 1024) :
    Winding.Polygon.Comparison.SegmentHomotopyFormula
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower 1) polynomial
      start finish baseStart baseFinish := by
  let power := Dense.Gaussian.Power.Coordinate.coordinatePositivePower 1
  let A := Dense.Gaussian.Path.Components.pathReal power start (finish - start)
  let B := Dense.Gaussian.Path.Components.pathImag power start (finish - start)
  let U := Dense.Gaussian.Path.Components.pathReal polynomial baseStart (baseFinish - baseStart)
  let V := Dense.Gaussian.Path.Components.pathImag polynomial baseStart (baseFinish - baseStart)
  let C := U - A
  let D := V - B
  have startNonzero : power.eval start ≠ 0 := by
    rw [Dense.Gaussian.Power.Coordinate.coordinatePositivePower_eval]
    exact Gaussian.Power.pow_ne_zero_direct _ nonzero _
  have finishNonzero : power.eval finish ≠ 0 := by
    have finishRoot := chord_nonzero nonzero distance (time := 1) ⟨by decide, le_rfl⟩
    rw [Rational.Affine.Segment.line_segment_one] at finishRoot
    rw [Dense.Gaussian.Power.Coordinate.coordinatePositivePower_eval]
    exact Gaussian.Power.pow_ne_zero_direct _ finishRoot _
  refine ⟨startNonzero, finishNonzero, ?_⟩
  apply Dense.Rational.CauchyIndex.Comparison.Dominance.lineData_of_normDominance
    (A := A) (B := B) (C := C) (D := D) (U := U) (V := V)
    (root := parameterInterval) (by decide) (squaredChordClearance nonzero distance)
    (normSq start ^ 2 / 32)
    (Rat.Fraction.Order.Field.div_pos_direct
      (Rat.Fraction.Order.Arithmetic.pow_pos_direct (show 0 < Gaussian.Basic.Canonical.normSq start from by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using Gaussian.Norm.Basic.normSq_pos nonzero)
        2) (by decide +kernel))
  · intro time inside
    have powerLower : normSq start ^ 2 / 16 ≤ A.eval time ^ 2 + B.eval time ^ 2 :=
      (squaredChordClearance nonzero distance).lower time inside
    have errorUpper : C.eval time ^ 2 + D.eval time ^ 2 ≤ normSq start ^ 2 / 32 := by
      calc
        _ = normSq ((Rational.Affine.line start (finish - start) time) ^ 2 -
            polynomial.eval (Rational.Affine.line baseStart (baseFinish - baseStart) time)) := by
          simp only [C, D, U, V, A, B, power, Dense.Basic.DensePolynomial.eval_sub,
            Dense.Gaussian.Path.Components.eval_pathReal,
            Dense.Gaussian.Path.Components.eval_pathImag, Dense.Gaussian.Power.Coordinate.coordinatePositivePower_eval,
            normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
          ring1
        _ ≤ _ := chord_square_residual distance residual (movement time inside) inside
    calc
      _ = normSq start ^ 2 / 16 - normSq start ^ 2 / 32 := by
        have fractions : (16 : Rat.Fraction.Rational)⁻¹ = 2 * (32 : Rat.Fraction.Rational)⁻¹ := by decide
        simp only [Field.ExplicitField.div_eq_mul_inv, fractions]
        ring1
      _ ≤ _ := Rat.Fraction.Order.Arithmetic.sub_le_sub_direct powerLower errorUpper
  · intro time
    simp only [C, Dense.Basic.DensePolynomial.eval_sub]
    ring1
  · intro time
    simp only [D, Dense.Basic.DensePolynomial.eval_sub]
    ring1

end Purelib.Riemann.RootContinuation.SquareRootTraceHomotopy
