module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Bounds.Abs
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Power.Gaussian
public import Purelib.RootIsolation.Power.Isolation.Track
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Apart
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
public import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
public import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box

public import Purelib.Riemann.RootContinuation.CoherentRoot
public import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

/-!
# Two constructive coherent square-root sheets

For a displayed nonzero Gaussian rational `w`, the finite power-polynomial
isolator computes exactly two winding-one tracks for `Z^2 - w`.  This file
turns each track into an apart coherent CCL name and proves, by finite
operational comparison of its rational samples, that its square is `w`.
No completed algebraic root or choice of a field element is introduced.
-/

namespace Purelib.Riemann.Branches.SquareRootSheets

open Purelib.Data.Nat

section
open Purelib.Data
/-- The rational scalar type for square-root error and apartness bounds. -/
public abbrev Coordinate := Rat.Fraction.Rational
/-- The executable Gaussian rational radicand and sample type. -/
public abbrev Gaussian := Gaussian.Basic.Canonical
end

section
open Purelib.Approximation
/-- Finite Gaussian samples with executable refinement and error bounds. -/
public abbrev Approximation := Gaussian.Sequence.ApproximationData
/-- The coherent arithmetic CCL name type for each retained root. -/
public abbrev CoherentNamed := Gaussian.Name.Coherent.CoherentNamed
/-- Operational equivalence between persistent Gaussian names. -/
public abbrev NamedEquivalent := Gaussian.Equivalence.NamedEquivalent

end

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.RootContinuation.SquareRootDegree

section
open Purelib.RootIsolation
/-- The accelerated winding-one track for one explicitly indexed square-root owner.

Finite degree-two isolation supplies the original owner and initial state. Later refinement uses the checked quadratic
accelerator with its total fallback. -/
@[expose] public def track {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (sheet : Fin 2) :=
  SquareRoot.Clearance.QuadraticLineClearance.Owner.accelerateTrack parameter
    (Power.Isolation.Track.isolatedTrack parameterNonzero degreeTwo
      degreeTwo_atLeastTwo sheet)

/-- The accelerated sheet track retains the isolated owner's exact initial state. -/
@[simp] public theorem track_initial {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (sheet : Fin 2) :
    (track parameterNonzero sheet).initial =
      (Power.Isolation.Track.isolatedTrack parameterNonzero degreeTwo degreeTwo_atLeastTwo sheet).initial := by
  exact SquareRoot.Clearance.QuadraticLineClearance.Owner.accelerateTrack_initial _ _

end

/-- Clamp every sample index to a retained finite base index.

The approximation reuses the original samples, bounds and refinement procedure through max, preserving an executable
total state type. -/
@[expose] public def tail (source : Approximation) (base : Nat) : Approximation where
  sample index := source.sample (max base index)
  radiusSq index := source.radiusSq (max base index)
  radiusSq_nonneg index := source.radiusSq_nonneg (max base index)
  later_close := by
    intro earlier later order
    apply source.later_close
    rewrite [Order.max_eq_natMax, Order.max_eq_natMax]
    exact Order.max_le_max (Nat.le_refl base) order
  refineIndex current target positive :=
    source.refineIndex (max base current) target positive
  refineIndex_ge := by
    intro current target positive
    apply Nat.le_trans _ (source.refineIndex_ge (max base current) target positive)
    rewrite [Order.max_eq_natMax]
    exact Order.le_max_right base current
  refineIndex_accurate := by
    intro current target positive
    have baseLe : base ≤ source.refineIndex (max base current) target positive :=
      Nat.le_trans
        ((Order.max_eq_natMax base current).symm ▸ Order.le_max_left base current)
        (source.refineIndex_ge (max base current) target positive)
    have maximumReadback :
        max base (source.refineIndex (max base current) target positive) =
          source.refineIndex (max base current) target positive := by
      change (if base ≤ source.refineIndex (max base current) target positive then
          source.refineIndex (max base current) target positive else base) = _
      exact if_pos baseLe
    rewrite [maximumReadback]
    exact source.refineIndex_accurate (max base current) target positive
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded index := source.sample_bounded (max base index)

/-- A tailed approximation reads the original sample at the maximum of base and requested index. -/
@[simp] public theorem tail_sample (source : Approximation) (base index : Nat) :
    (tail source base).sample index = source.sample (max base index) := rfl

/-- One quarter of the radicand quadrance, used as the square-residual threshold. -/
@[expose] public def residualTarget (parameter : Gaussian) : Coordinate :=
  normSq parameter / 4

section
open Purelib.Data
/-- A nonzero radicand gives a strictly positive residual threshold. -/
public theorem residualTarget_positive {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) : 0 < residualTarget parameter := by
  have scalar := Gaussian.Norm.Basic.normSq_pos parameterNonzero
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
  exact Rat.Fraction.Order.Field.div_pos_direct scalar (by decide)

/-- The larger retained absolute rational coordinate of a Gaussian value.

Both coordinates use the original decidable cross-product order and canonical
negation. Their displayed maximum retains the larger absolute coordinate. -/
@[expose] public def coordinateNormLower (parameter : Gaussian) : Coordinate :=
  max (Rat.Fraction.abs parameter.re) (Rat.Fraction.abs parameter.im)

/-- The dominant absolute coordinate squared is at most the Gaussian quadrance.

The original ordered maximum selects one retained absolute coordinate. Its square equals that coordinate square and the
remaining square is nonnegative. -/
public theorem coordinateNormLower_sq_le_normSq (parameter : Gaussian) :
    coordinateNormLower parameter ^ 2 ≤ normSq parameter := by
  unfold coordinateNormLower
  simp only [Gaussian.Basic.Canonical.normSq, ← pow_two]
  change max (Rat.Fraction.abs parameter.re) (Rat.Fraction.abs parameter.im) ^ 2 ≤
    parameter.re ^ 2 + parameter.im ^ 2
  by_cases order : (Rat.Fraction.abs parameter.re) ≤ (Rat.Fraction.abs parameter.im)
  · rw [Rat.Fraction.Order.Basic.max_eq_right order, Rat.Bounds.Abs.abs_sq_direct]
    exact le_add_of_nonneg_left
      (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct parameter.re)
  · have reverse : (Rat.Fraction.abs parameter.im) ≤ (Rat.Fraction.abs parameter.re) :=
      le_of_not_ge order
    rw [Rat.Fraction.Order.Basic.max_eq_left reverse, Rat.Bounds.Abs.abs_sq_direct]
    exact le_add_of_nonneg_right
      (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct parameter.im)

/-- Gaussian quadrance is at most twice the dominant absolute coordinate squared.

Both original coordinate squares are bounded by the square of the retained maximum. Adding the two scalar bounds gives
the displayed factor-two estimate. -/
public theorem normSq_le_two_coordinateNormLower_sq (parameter : Gaussian) :
    normSq parameter <= 2 * coordinateNormLower parameter ^ 2 := by
  unfold coordinateNormLower normSq
  simp only [← pow_two]
  by_cases order : (Rat.Fraction.abs parameter.re) <= (Rat.Fraction.abs parameter.im)
  · rw [Rat.Fraction.Order.Basic.max_eq_right order, Rat.Bounds.Abs.abs_sq_direct]
    have reSqLe : parameter.re ^ 2 <= parameter.im ^ 2 := by
      rw [← Rat.Bounds.Abs.abs_sq_direct parameter.re, ← Rat.Bounds.Abs.abs_sq_direct parameter.im]
      exact Rat.Fraction.Order.Arithmetic.pow_le_pow_direct
        (Rat.Fraction.Order.Arithmetic.abs_nonneg_direct parameter.re) order 2
    calc
      parameter.re ^ 2 + parameter.im ^ 2 <=
          parameter.im ^ 2 + parameter.im ^ 2 := add_le_add reSqLe le_rfl
      _ = 2 * parameter.im ^ 2 := by ring1
  · have reverse : (Rat.Fraction.abs parameter.im) <= (Rat.Fraction.abs parameter.re) := le_of_not_ge order
    rw [Rat.Fraction.Order.Basic.max_eq_left reverse, Rat.Bounds.Abs.abs_sq_direct]
    have imSqLe : parameter.im ^ 2 <= parameter.re ^ 2 := by
      rw [← Rat.Bounds.Abs.abs_sq_direct parameter.im, ← Rat.Bounds.Abs.abs_sq_direct parameter.re]
      exact Rat.Fraction.Order.Arithmetic.pow_le_pow_direct
        (Rat.Fraction.Order.Arithmetic.abs_nonneg_direct parameter.im) reverse 2
    calc
      parameter.re ^ 2 + parameter.im ^ 2 <=
          parameter.re ^ 2 + parameter.re ^ 2 := add_le_add le_rfl imSqLe
      _ = 2 * parameter.re ^ 2 := by ring1

end

open Purelib.Approximation in
open Purelib.Data in
/-- A positive quadrance lower bound gives a finite dyadic lower bound for the dominant coordinate.

Apply the executable square-radius construction to half the retained lower bound; the result is at most the radicand's
dominant absolute coordinate. -/
public theorem dyadicSquareRadius_half_le_coordinateNormLower
    {parameter : Gaussian} {lower : Coordinate} (positive : 0 < lower)
    (lowerLe : lower <= normSq parameter) :
    Rational.SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius (lower / 2) <=
      coordinateNormLower parameter := by
  have halfPositive : 0 < lower / 2 :=
    Rat.Fraction.Order.Field.div_pos_direct positive (by decide)
  have normHalfLe : normSq parameter / 2 <=
      coordinateNormLower parameter ^ 2 := by
    apply (Rat.Fraction.Order.Field.div_le_iff_pos
      (show (0 : Coordinate) < 2 by decide)).2
    simpa only [Rat.Fraction.Field.mul_comm] using
      normSq_le_two_coordinateNormLower_sq parameter
  have lowerHalfLe : lower / 2 <= normSq parameter / 2 := by
    rw [Rat.Fraction.Field.div_eq_mul_inv_direct,
      Rat.Fraction.Field.div_eq_mul_inv_direct]
    exact Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct lowerLe
      (by decide)
  have squareLe :
      Rational.SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius (lower / 2) ^ 2 <=
        coordinateNormLower parameter ^ 2 :=
    (Rational.SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_sq_lt halfPositive).le.trans
      (lowerHalfLe.trans normHalfLe)
  exact Rat.Fraction.Order.Arithmetic.le_of_sq_le_sq_direct
    (by
      unfold coordinateNormLower
      exact
        (Rat.Fraction.Order.Arithmetic.abs_nonneg_direct parameter.re).trans
          (Rat.Fraction.Order.Basic.le_max_left _ _))
    squareLe

/-- The explicit lower bound used for retained square-root sample quadrances.

Take the larger of the residual bound clipped at one and half the radicand's dominant absolute coordinate. Both terms
are directly executable rationals. -/
@[expose] public def sampleNormLower (parameter : Gaussian) : Coordinate :=
  max (min 1 (residualTarget parameter))
    (coordinateNormLower parameter / 2)

section
open Purelib.Data
/-- Twice a rational quarter equals its half. -/
private theorem twice_quarter_eq_half (value : Coordinate) :
    2 * (value / 4) = value / 2 := by
  apply Rat.Fraction.Field.mul_right_cancel_of_ne
    (show (4 : Coordinate) ≠ 0 by decide)
  calc
    (2 * (value / 4)) * 4 = 2 * ((value / 4) * 4) := by ring1
    _ = 2 * value := by
      rw [show (value / 4) * 4 = value from
        Rat.Fraction.Field.div_mul_cancel_of_ne value 4 (by decide)]
    _ = value * 2 := by ring1
    _ = ((value / 2) * 2) * 2 := by
      rw [show (value / 2) * 2 = value from
        Rat.Fraction.Field.div_mul_cancel_of_ne value 2 (by decide)]
    _ = (value / 2) * 4 := by ring1

/-- Two rational halves sum to the original value. -/
private theorem half_add_half (value : Coordinate) :
    value / 2 + value / 2 = value := by
  apply Rat.Fraction.Field.mul_right_cancel_of_ne
    (show (2 : Coordinate) ≠ 0 by decide)
  calc
    (value / 2 + value / 2) * 2 =
        (value / 2) * 2 + (value / 2) * 2 := by rw [add_mul]
    _ = value + value := by
      rw [show (value / 2) * 2 = value from
        Rat.Fraction.Field.div_mul_cancel_of_ne value 2 (by decide)]
    _ = value * 2 := by ring1

end

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Polynomial in
/-- Compute the first root-track index whose geometric residual bound is below the radicand threshold.

The same nonzero radicand and retained sheet track determine the geometric residual scale. The finite search compares
that scale with the positive quarter-quadrance threshold. -/
@[expose] public def baseIndex {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (sheet : Fin 2) : Nat :=
  Rational.Geometric.Search.firstQuarterBelow
    (RootContinuation.CoherentRoot.residualScale
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo))
      (track parameterNonzero sheet))
    0 (residualTarget parameter)

open Purelib.Riemann in
/-- Clamp the coherent root-track approximation at its computed apartness base index.

Every retained sample is drawn from the same deterministic sheet track at or after the certified residual threshold. -/
@[expose] public def approximation {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (sheet : Fin 2) : Approximation :=
  tail (RootContinuation.CoherentRoot.approximation
    (track parameterNonzero sheet)) (baseIndex parameterNonzero sheet)

section
open Purelib.Riemann
open Purelib.Approximation
open Purelib.Data
open Purelib.Polynomial
/-- Every retained sample's square residual satisfies the displayed quarter-geometric bound. -/
public theorem sample_residual_le {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (sheet : Fin 2) (index : Nat) :
    normSq
        ((approximation parameterNonzero sheet).sample index *
            (approximation parameterNonzero sheet).sample index - parameter) <=
      Rational.Geometric.Basic.quarterRadius
        (RootContinuation.CoherentRoot.residualScale
          (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo)
          (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
            (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo))
          (track parameterNonzero sheet)) index := by
  let source := RootContinuation.CoherentRoot.approximation
    (track parameterNonzero sheet)
  let selected := max (baseIndex parameterNonzero sheet) index
  have raw := RootContinuation.CoherentRoot.sample_residual_le
    (track parameterNonzero sheet) (by
      rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
      exact degreeTwo.positive) selected
  rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval] at raw
  have selectedBound := quarterRadius_antitone
    (RootContinuation.CoherentRoot.residualScale_nonneg
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo))
      (track parameterNonzero sheet))
    ((Order.max_eq_natMax (baseIndex parameterNonzero sheet) index).symm ▸ Order.le_max_right (baseIndex
      parameterNonzero sheet) index)
  simpa only [approximation, tail_sample, source, selected, degreeTwo_value,
    pow_two, Gaussian.Norm.Basic.normSq_eq_canonical] using raw.trans selectedBound

/-- Every retained sample's square residual is strictly below the radicand threshold. -/
public theorem sample_residual_lt_target {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (sheet : Fin 2) (index : Nat) :
    normSq
        ((approximation parameterNonzero sheet).sample index *
            (approximation parameterNonzero sheet).sample index - parameter) <
      residualTarget parameter := by
  let scale := RootContinuation.CoherentRoot.residualScale
    (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo)
    (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo))
    (track parameterNonzero sheet)
  have baseSmall : Rational.Geometric.Basic.quarterRadius scale
      (baseIndex parameterNonzero sheet) < residualTarget parameter := by
    exact Rational.Geometric.Search.firstQuarterBelow_accurate scale
      (RootContinuation.CoherentRoot.residualScale_nonneg
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo)
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
          (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo))
        (track parameterNonzero sheet))
      0 (residualTarget parameter) (residualTarget_positive parameterNonzero)
  let selected := max (baseIndex parameterNonzero sheet) index
  have baseSelected : baseIndex parameterNonzero sheet ≤ selected := by
    change baseIndex parameterNonzero sheet ≤ max (baseIndex parameterNonzero sheet) index
    rewrite [Order.max_eq_natMax]
    exact Order.le_max_left _ _
  have raw := RootContinuation.CoherentRoot.sample_residual_le
    (track parameterNonzero sheet) (by
      rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
      exact degreeTwo.positive) selected
  rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval] at raw
  have selectedSmall : Rational.Geometric.Basic.quarterRadius scale selected <
      residualTarget parameter :=
    (quarterRadius_antitone
      (RootContinuation.CoherentRoot.residualScale_nonneg
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo)
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
          (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo))
        (track parameterNonzero sheet))
      baseSelected).trans_lt
        baseSmall
  simpa only [approximation, tail_sample, selected, degreeTwo_value,
    pow_two, Gaussian.Norm.Basic.normSq_eq_canonical] using raw.trans_lt selectedSmall

end

open Purelib.Data in
/-- A sufficiently small square residual gives the explicit sample quadrance lower bound.

The residual quadrance is at most one quarter of the radicand quadrance. The conclusion retains both the clipped
residual lower bound and the dominant-coordinate lower bound. -/
public theorem normSq_lower_of_square_residual
    {parameter value : Gaussian}
    (residual : normSq (value * value - parameter) <=
      residualTarget parameter) :
    sampleNormLower parameter <= normSq value := by
  let parameterNorm := normSq parameter
  let valueNorm := normSq value
  have parameterIdentity :
      parameter = (parameter - value * value) + value * value := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
        Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1
  have reversedResidual :
      normSq (parameter - value * value) <= parameterNorm / 4 := by
    have negativeIdentity :
        parameter - value * value = -(value * value - parameter) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.neg_re, Gaussian.Basic.neg_im,
          Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1
    rw [negativeIdentity, Gaussian.Basic.Canonical.normSq_neg]
    exact residual
  have parameterUpper :
      parameterNorm <= parameterNorm / 2 + 2 * valueNorm ^ 2 := by
    have triangle := Gaussian.Norm.Bounds.normSq_add_le_two
      (parameter - value * value) (value * value)
    rw [Gaussian.Norm.Basic.normSq_mul] at triangle
    calc
      parameterNorm =
          normSq ((parameter - value * value) + value * value) := by
        rw [← parameterIdentity]
      _ <= 2 * (normSq (parameter - value * value) + valueNorm ^ 2) := by
        simpa only [valueNorm, pow_two, Gaussian.Norm.Basic.normSq_eq_canonical] using triangle
      _ <= 2 * (parameterNorm / 4 + valueNorm ^ 2) :=
        Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add reversedResidual (le_refl _)) (by decide)
      _ = parameterNorm / 2 + 2 * valueNorm ^ 2 := by
        rw [show 2 * (parameterNorm / 4 + valueNorm ^ 2) =
            2 * (parameterNorm / 4) + 2 * valueNorm ^ 2 by ring1,
          twice_quarter_eq_half]
  have quarterLeSquare : parameterNorm / 4 <= valueNorm ^ 2 := by
    apply Rat.Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := (4 : Coordinate)) _ (by decide)
    have halfLe : parameterNorm / 2 <= 2 * valueNorm ^ 2 := by
      apply Rat.Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
        (c := parameterNorm / 2)
      calc
        parameterNorm / 2 + parameterNorm / 2 = parameterNorm :=
          half_add_half parameterNorm
        _ <= parameterNorm / 2 + 2 * valueNorm ^ 2 := parameterUpper
        _ = 2 * valueNorm ^ 2 + parameterNorm / 2 := by ring1
    calc
      (parameterNorm / 4) * 4 = parameterNorm :=
        Rat.Fraction.Field.div_mul_cancel_of_ne _ 4 (by decide)
      _ = (parameterNorm / 2) * 2 := by
        exact (Rat.Fraction.Field.div_mul_cancel_of_ne
          parameterNorm 2 (by decide)).symm
      _ <= (2 * valueNorm ^ 2) * 2 :=
        Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          halfLe (by decide)
      _ = valueNorm ^ 2 * 4 := by ring1
  have residualLower : min 1 (residualTarget parameter) <= valueNorm := by
    apply le_of_not_gt
    intro tooSmall
    have valueLtOne : valueNorm < 1 :=
      tooSmall.trans_le (Rat.Fraction.Order.Basic.min_le_left _ _)
    have valueLtTarget : valueNorm < parameterNorm / 4 :=
      tooSmall.trans_le (Rat.Fraction.Order.Basic.min_le_right _ _)
    have valueSquareLeValue : valueNorm ^ 2 <= valueNorm := by
      rw [pow_two]
      calc
        valueNorm * valueNorm <= 1 * valueNorm :=
          Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            valueLtOne.le (Gaussian.Basic.Canonical.normSq_nonneg value)
        _ = valueNorm := by ring1
    exact (not_lt_of_ge quarterLeSquare)
      (valueSquareLeValue.trans_lt valueLtTarget)
  have coordinateQuarter :
      (coordinateNormLower parameter / 2) ^ 2 <= parameterNorm / 4 := by
    calc
      (coordinateNormLower parameter / 2) ^ 2 =
          coordinateNormLower parameter ^ 2 / 4 := by
        apply Rat.Fraction.Field.mul_right_cancel_of_ne
          (show (4 : Coordinate) ≠ 0 by decide)
        calc
          (coordinateNormLower parameter / 2) ^ 2 * 4 =
              ((coordinateNormLower parameter / 2) * 2) ^ 2 := by ring1
          _ = coordinateNormLower parameter ^ 2 := by
            rw [Rat.Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)]
          _ = (coordinateNormLower parameter ^ 2 / 4) * 4 := by
            rw [Rat.Fraction.Field.div_mul_cancel_of_ne _ 4 (by decide)]
      _ <= parameterNorm / 4 := by
        rw [Rat.Fraction.Field.div_eq_mul_inv_direct,
          Rat.Fraction.Field.div_eq_mul_inv_direct]
        exact Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (coordinateNormLower_sq_le_normSq parameter) (by decide)
  have coordinateLower : coordinateNormLower parameter / 2 <= valueNorm :=
    Rat.Fraction.Order.Arithmetic.le_of_sq_le_sq_direct (Gaussian.Basic.Canonical.normSq_nonneg value)
      (coordinateQuarter.trans quarterLeSquare)
  exact Rat.Fraction.Order.Basic.max_le residualLower coordinateLower

/-- Every retained sheet sample satisfies the same explicit quadrance lower bound. -/
public theorem sample_norm_lower {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (sheet : Fin 2) (index : Nat) :
    sampleNormLower parameter <=
      normSq ((approximation parameterNonzero sheet).sample index) :=
  normSq_lower_of_square_residual
    (sample_residual_lt_target parameterNonzero sheet index).le

open Purelib.Data in
/-- The retained sample quadrance lower bound is positive for a nonzero radicand.

The clipped residual threshold is positive for the same nonzero radicand. Its contribution to the retained maximum gives
the stated positive lower bound. -/
public theorem sampleLower_positive {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) :
    0 < sampleNormLower parameter :=
  (Rat.Fraction.Order.Basic.lt_min (by decide) (residualTarget_positive parameterNonzero)).trans_le
    (Rat.Fraction.Order.Basic.le_max_left _ _)

open Purelib.Approximation in
open Purelib.Data in
/-- Certify uniform candidate apartness of the retained tailed approximation.

Every possible later sample satisfies the same positive lower quadrance before whole-ball denominator preparation. -/
@[expose] public def possibleApart {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (sheet : Fin 2) :
    Gaussian.Process.Apart.Possible.PossibleApart
      (approximation parameterNonzero sheet).toProcess where
  lowerSq := sampleNormLower parameter
  positive := sampleLower_positive parameterNonzero
  lower := by
    intro state value possible
    change (approximation parameterNonzero sheet).Possible state value at possible
    rcases possible with ⟨later, _order, rfl⟩
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using sample_norm_lower parameterNonzero sheet later

section
open Purelib.Approximation
/-- The coherent sheet name before whole-ball denominator preparation.

The original retained sheet approximation supplies both the persistent name and coherence certificate. Its sample
indices and refinement data are passed unchanged to the named conversion. -/
@[expose] public def rawRoot {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (sheet : Fin 2) : CoherentNamed :=
  Gaussian.Name.Coherent.CoherentNamed.ofApproximation
    (approximation parameterNonzero sheet)

/-- Prepare the coherent sheet name for division using its retained candidate apartness certificate.

The same raw root and retained candidate-apart certificate determine the prepared persistent name. Whole-ball
preparation preserves both the original operational value and its coherent refinement data. -/
@[expose] public def root {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (sheet : Fin 2) : CoherentNamed :=
  Gaussian.Name.Coherent.CoherentNamed.apartify
    (rawRoot parameterNonzero sheet)
    (possibleApart parameterNonzero sheet)

/-- The prepared root name carries uniform whole-ball apartness.

The certificate belongs to the actual prepared name produced from the same candidate-apart evidence. The retained
preparation state and process determine its whole-ball apartness fields. -/
@[expose] public def rootApart {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (sheet : Fin 2) : Gaussian.Name.Basic.Named.Apart
      (root parameterNonzero sheet).name where
  certificate := Gaussian.Process.Apart.Preparation.apartifyApart
    (possibleApart parameterNonzero sheet)

end

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- Construct the finite approximation obtained by squaring each retained sheet sample.

The original sample bound and geometric root-error scale give an explicit squared-sample modulus, refinement search and
center bound. -/
@[expose] public def squareApproximation {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (sheet : Fin 2) : Approximation :=
  let source := approximation parameterNonzero sheet
  let scale := 4 * source.centerBound *
    RootContinuation.CoherentRoot.scale (track parameterNonzero sheet)
  { sample := fun index => source.sample index * source.sample index
    radiusSq := Rational.Geometric.Basic.quarterRadius scale
    radiusSq_nonneg := Rational.Geometric.Basic.quarterRadius_nonneg
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
        (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          source.centerBound_nonneg)
        (RootContinuation.CoherentRoot.scale_positive
          (track parameterNonzero sheet)).le)
    later_close := by
      intro earlier later order
      have movement := source.later_close order
      have sourceRadiusLe : source.radiusSq earlier <=
          Rational.Geometric.Basic.quarterRadius
            (RootContinuation.CoherentRoot.scale
              (track parameterNonzero sheet)) earlier :=
        quarterRadius_antitone
          (RootContinuation.CoherentRoot.scale_positive
            (track parameterNonzero sheet)).le
          ((Order.max_eq_natMax (baseIndex parameterNonzero sheet) earlier).symm ▸ Order.le_max_right (baseIndex
            parameterNonzero sheet) earlier)
      have firstTerm :
          Data.Gaussian.Norm.Basic.normSq ((source.sample later - source.sample earlier) *
              source.sample later) <=
            Rational.Geometric.Basic.quarterRadius
                (RootContinuation.CoherentRoot.scale
                  (track parameterNonzero sheet)) earlier *
              source.centerBound := by
        rw [Gaussian.Norm.Basic.normSq_mul]
        exact Rat.Fraction.Order.Arithmetic.mul_le_mul_direct
          (movement.trans sourceRadiusLe) (source.sample_bounded later)
          (Gaussian.Norm.Basic.normSq_nonneg _) (Rational.Geometric.Basic.quarterRadius_nonneg
            (RootContinuation.CoherentRoot.scale_positive
              (track parameterNonzero sheet)).le earlier)
      have secondTerm :
          Data.Gaussian.Norm.Basic.normSq (source.sample earlier *
              (source.sample later - source.sample earlier)) <=
            source.centerBound *
              Rational.Geometric.Basic.quarterRadius
                (RootContinuation.CoherentRoot.scale
                  (track parameterNonzero sheet)) earlier := by
        rw [Gaussian.Norm.Basic.normSq_mul]
        exact Rat.Fraction.Order.Arithmetic.mul_le_mul_direct
          (source.sample_bounded earlier) (movement.trans sourceRadiusLe)
          (Gaussian.Norm.Basic.normSq_nonneg _) source.centerBound_nonneg
      have identity :
          source.sample later * source.sample later -
              source.sample earlier * source.sample earlier =
            (source.sample later - source.sample earlier) *
                source.sample later +
              source.sample earlier *
                (source.sample later - source.sample earlier) := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
            Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1
      rw [identity]
      calc
        Data.Gaussian.Norm.Basic.normSq
            ((source.sample later - source.sample earlier) *
                source.sample later +
              source.sample earlier *
                (source.sample later - source.sample earlier)) <=
          2 *
            (Data.Gaussian.Norm.Basic.normSq ((source.sample later - source.sample earlier) *
                source.sample later) +
              Data.Gaussian.Norm.Basic.normSq (source.sample earlier *
                (source.sample later - source.sample earlier))) :=
          Gaussian.Norm.Bounds.normSq_add_le_two _ _
        _ <= 2 *
            (Rational.Geometric.Basic.quarterRadius
                (RootContinuation.CoherentRoot.scale
                  (track parameterNonzero sheet)) earlier *
                source.centerBound +
              source.centerBound *
                Rational.Geometric.Basic.quarterRadius
                  (RootContinuation.CoherentRoot.scale
                    (track parameterNonzero sheet)) earlier) :=
          Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (add_le_add firstTerm secondTerm) (by decide)
        _ = Rational.Geometric.Basic.quarterRadius scale earlier := by
          rw [Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
            Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
          dsimp only [scale]
          ring1
    refineIndex current target _ :=
      Rational.Geometric.Search.firstQuarterBelow scale current target
    refineIndex_ge current target _ :=
      Rational.Geometric.Search.firstQuarterBelow_ge scale current target
    refineIndex_accurate :=
      Rational.Geometric.Search.firstQuarterBelow_accurate scale
        (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
          (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            source.centerBound_nonneg)
          (RootContinuation.CoherentRoot.scale_positive
            (track parameterNonzero sheet)).le)
    centerBound := source.centerBound * source.centerBound
    centerBound_nonneg := Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
      source.centerBound_nonneg source.centerBound_nonneg
    sample_bounded := by
      intro index
      rw [Gaussian.Norm.Basic.normSq_mul]
      exact Rat.Fraction.Order.Arithmetic.mul_le_mul_direct
        (source.sample_bounded index) (source.sample_bounded index)
        (Gaussian.Norm.Basic.normSq_nonneg _) source.centerBound_nonneg }

/-- Each squared-approximation sample is the product of the corresponding retained root sample with itself.

The retained squared approximation stores the original tailed sample multiplied by itself. Reducing that scalar field
gives the displayed readback without changing any refinement data. -/
@[simp] public theorem squareApproximation_sample {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (sheet : Fin 2) (index : Nat) :
    (squareApproximation parameterNonzero sheet).sample index =
      (approximation parameterNonzero sheet).sample index *
        (approximation parameterNonzero sheet).sample index := by
  change (approximation parameterNonzero sheet).sample index *
      (approximation parameterNonzero sheet).sample index = _
  exact Eq.refl _

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
open Purelib.Polynomial in
/-- The sampled squares are operationally equivalent to the exact radicand approximation.

A finite quarter-radius search supplies comparison indices beyond both requested starts, and the residual estimate
controls every later pair of samples. -/
@[expose] public def squareApproximation_equivalent_parameter {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (sheet : Fin 2) :
    Gaussian.Equivalence.Equivalent
      (squareApproximation parameterNonzero sheet)
      (Gaussian.Sequence.Constant.constantApproximation parameter) where
  compare := by
    intro leftStart rightStart target positive
    let start := max leftStart rightStart
    let scale := RootContinuation.CoherentRoot.residualScale
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo))
      (track parameterNonzero sheet)
    let index := Rational.Geometric.Search.firstQuarterBelow scale start target
    have radiusSmall : Rational.Geometric.Basic.quarterRadius scale index < target :=
      Rational.Geometric.Search.firstQuarterBelow_accurate scale
        (RootContinuation.CoherentRoot.residualScale_nonneg
          (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo)
          (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
            (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo))
          (track parameterNonzero sheet)) start target positive
    exact
      { leftIndex := index
        rightIndex := index
        left_ge := by
          apply Nat.le_trans _ (Rational.Geometric.Search.firstQuarterBelow_ge scale start target)
          change leftStart ≤ max leftStart rightStart
          rewrite [Order.max_eq_natMax]
          exact Order.le_max_left leftStart rightStart
        right_ge := by
          apply Nat.le_trans _ (Rational.Geometric.Search.firstQuarterBelow_ge scale start target)
          change rightStart ≤ max leftStart rightStart
          rewrite [Order.max_eq_natMax]
          exact Order.le_max_right leftStart rightStart
        close := by
          intro leftLater rightLater leftOrder _rightOrder
          have residualBound := sample_residual_le parameterNonzero sheet
            leftLater
          have radiusLater := quarterRadius_antitone
            (RootContinuation.CoherentRoot.residualScale_nonneg
              (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo)
              (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
                (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo))
              (track parameterNonzero sheet)) leftOrder
          simpa only [squareApproximation_sample,
            Gaussian.Sequence.Constant.constantApproximation, Gaussian.Norm.Basic.normSq_eq_canonical] using
              residualBound.trans_lt (radiusLater.trans_lt radiusSmall) }

section
open Purelib.Approximation
/-- Multiplying the unprepared coherent root by itself is operationally equivalent to the exact radicand.

The multiplication readback is compared with the retained squared approximation and then its constant radicand
approximation. -/
@[expose] public def rawRoot_square {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (sheet : Fin 2) :
    NamedEquivalent
      (Gaussian.Name.Coherent.CoherentNamed.mul
        (rawRoot parameterNonzero sheet)
        (rawRoot parameterNonzero sheet)).name
      (Gaussian.Name.Basic.Named.exact parameter) := by
  let source := approximation parameterNonzero sheet
  let product := squareApproximation parameterNonzero sheet
  have actualToProduct : NamedEquivalent
      (Gaussian.Name.Basic.Named.mul source.toNamed source.toNamed)
      product.toNamed :=
    Gaussian.Sequence.Arithmetic.Multiplication.Bridge.mulToNamed_equivalent_pointwise
      source source product (by intro index; rfl)
  have productToConstant : NamedEquivalent product.toNamed
      (Gaussian.Sequence.Constant.constantApproximation parameter).toNamed :=
    Gaussian.Sequence.Name.Equivalence.approximationEquivalent_toNamed
      (squareApproximation_equivalent_parameter parameterNonzero sheet)
  exact Gaussian.Equivalence.NamedEquivalent.trans
    (by simpa only [rawRoot,
      Gaussian.Name.Coherent.CoherentNamed.mul,
      Gaussian.Name.Coherent.CoherentNamed.ofApproximation, source, product]
      using actualToProduct)
    (Gaussian.Equivalence.NamedEquivalent.trans productToConstant
      (Gaussian.Equivalence.NamedEquivalent.symm
        (Gaussian.Sequence.Name.Exact.exact_toConstantNamed parameter)))

/-- The division-ready root still squares operationally to the exact radicand.

Apartness preparation preserves the original name's equivalence, and multiplication congruence transports the raw-root
square certificate. -/
@[expose] public def root_square {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (sheet : Fin 2) :
    NamedEquivalent
      (Gaussian.Name.Coherent.CoherentNamed.mul
        (root parameterNonzero sheet)
        (root parameterNonzero sheet)).name
      (Gaussian.Name.Basic.Named.exact parameter) := by
  let raw := rawRoot parameterNonzero sheet
  let prepared := root parameterNonzero sheet
  have preparedToRaw : NamedEquivalent prepared.name raw.name :=
    Gaussian.Equivalence.NamedEquivalent.symm
      (Gaussian.Name.Coherent.CoherentNamed.apartifyEquivalent raw
        (possibleApart parameterNonzero sheet))
  have products : NamedEquivalent
      (Gaussian.Name.Coherent.CoherentNamed.mul prepared prepared).name
      (Gaussian.Name.Coherent.CoherentNamed.mul raw raw).name :=
    Gaussian.Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
      prepared raw prepared raw preparedToRaw preparedToRaw
  exact Gaussian.Equivalence.NamedEquivalent.trans products
    (rawRoot_square parameterNonzero sheet)

end

open Purelib.Approximation in
set_option genInjectivity false in
/-- One explicitly indexed coherent square-root sheet with apartness and square certificates.

The retained persistent name is safe for division and its actual multiplication is operationally equivalent to the
displayed exact radicand. -/
public structure Sheet (parameter : Gaussian) where
  /-- The retained finite index of this square-root sheet. -/ index : Fin 2
  /-- The retained coherent persistent root name. -/ value : CoherentNamed
  /-- The retained name carries whole-ball apartness for safe division. -/ apart : Gaussian.Name.Basic.Named.Apart
    value.name
  /-- The actual product of the retained root with itself is operationally the exact radicand. -/ square :
    NamedEquivalent
    (Gaussian.Name.Coherent.CoherentNamed.mul value value).name
    (Gaussian.Name.Basic.Named.exact parameter)

constructive_injectivity Sheet

/-- Construct the certified division-ready root sheet at the supplied finite index.

The supplied finite index selects the retained prepared name. Its apartness and square certificates refer to that same
name and original radicand. -/
@[expose] public def sheet {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (index : Fin 2) : Sheet parameter where
  index := index
  value := root parameterNonzero index
  apart := rootApart parameterNonzero index
  square := root_square parameterNonzero index

/-- Construct the complete finite family of both explicitly indexed root sheets. -/
@[expose] public def family {parameter : Gaussian} (parameterNonzero : parameter ≠ 0) :
    Fin 2 -> Sheet parameter :=
  sheet parameterNonzero

end Purelib.Riemann.Branches.SquareRootSheets
