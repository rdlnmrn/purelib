module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Flatten
import Purelib.Data.Nat.Subtraction
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Power.Gaussian
import Purelib.Algebra.Field.ExplicitField
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
public import Purelib.Polynomial.Geometry.ClearPath

public import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Quantitative square-root continuation on a clear segment

The dense Horner bound controls the change of `f(x)` between two rational
samples of a certified clear segment.  If that computed change fits inside
the current owner's Rouché clearance, this file advances the owner without a
fresh sheet choice.  It is the local step used by a finite adaptive
subdivision.
-/

namespace Purelib.Riemann.Branches.ClearSheetContinuation

open Purelib.Data.List
open Purelib.Data.Nat

open Purelib.Data.Rat in
/-- The exact rational parameter carrier. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
abbrev Gaussian := Basic.Canonical
open Purelib.Polynomial.Dense.Gaussian in
/-- Dense Gaussian polynomials over exact rational coordinates. -/
abbrev GaussianPolynomial :=
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The original rational box type with coordinate bounds. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The original square-root owner indexed by its exact radicand. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
/-- A radicand paired with its original dependent square-root owner. -/
abbrev PackedOwner :=
  Purelib.Riemann.Topology.SquareRootContinuationChain.PackedOwner
/-- A finite square-root continuation chain indexed by its starting owner. -/
abbrev Chain := Purelib.Riemann.Topology.SquareRootContinuationChain.Chain

/-- The degenerate Gaussian box representing the real unit parameter interval. -/
@[expose] def parameterAmbient : Box where
  xLower := 0
  xUpper := 1
  yLower := 0
  yUpper := 0
  x_valid := by decide
  y_valid := by decide

open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- The exact box Lipschitz bound for five displayed coefficients is a weighted sum of the first four coefficient
quadrances, floored at one.

The retained parameter-ambient box has squared-radius bound two; the constant coefficient does not enter the slope
bound. -/
theorem parameterAmbient_denseLipschitzBound_fiveCoeffs
    (a b c d e : Gaussian) :
    Dense.Gaussian.Bounds.Box.denseLipschitzBound
        (⟨[a, b, c, d, e]⟩ : GaussianPolynomial)
        parameterAmbient =
      max 1
        (1024 * Data.Gaussian.Norm.Basic.normSq a +
          192 * Data.Gaussian.Norm.Basic.normSq b +
          32 * Data.Gaussian.Norm.Basic.normSq c +
          4 * Data.Gaussian.Norm.Basic.normSq d) := by
  have parameterNormSqBound :
      parameterAmbient.normSqBound =
        (2 : Fraction.Rational) := by
    with_unfolding_all decide
  unfold Dense.Gaussian.Bounds.Box.denseLipschitzBound
    Dense.Gaussian.Bounds.Box.denseEvalNormLipschitzBound
    Dense.Gaussian.Bounds.Box.denseHornerNormBounds
  simp only [List.foldl_cons, List.foldl_nil]
  rw [parameterNormSqBound]
  unfold Dense.Gaussian.Bounds.Horner.step
  dsimp only
  apply congrArg (max 1)
  ring1

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Substitute the original segment's affine parameterization into its polynomial. -/
@[expose] def segmentPolynomial {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (_segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    GaussianPolynomial :=
  Substitution.Affine.composeLine polynomial start (finish - start)

open Purelib.Data.Gaussian in
/-- Every real parameter between zero and one lies in the retained parameter box. -/
theorem parameterAmbient_contains (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    parameterAmbient.Contains (Cast.Path.ofCoordinate parameter) :=
  ⟨inside.1, inside.2, le_rfl, le_rfl⟩

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Evaluating the substituted polynomial equals evaluation at the original segment point. -/
theorem segmentPolynomial_eval
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) :
    (segmentPolynomial segment).eval
        (Cast.Path.ofCoordinate parameter) =
      polynomial.eval (segment.pointAt parameter) := by
  rw [segmentPolynomial, Substitution.Affine.eval_composeLine]
  congr 1
  apply Basic.ext <;>
    simp only [Affine.line, Geometry.ClearPath.ClearSegment.pointAt,
      Cast.ofCoordinate_re,
      Cast.ofCoordinate_im,
      Scale.scale_re, Scale.scale_im,
      Basic.add_re,
      Basic.add_im,
      Basic.sub_re,
      Basic.sub_im,
      Basic.mul_re,
      Basic.mul_im] <;>
    ring1

section
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
/-- The segment polynomial's squared Lipschitz bound times the squared parameter displacement.

The bound uses the exact polynomial after affine substitution and the retained unit parameter box. -/
@[expose, irreducible] def variationBound {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Coordinate) : Coordinate :=
  Bounds.Box.denseLipschitzBound
      (segmentPolynomial segment) parameterAmbient *
    (left - right) ^ 2

/-- Read the retained variation bound as its exact squared-Lipschitz formula. -/
theorem variationBound_eq_denseLipschitz
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Coordinate) :
    variationBound segment left right =
      Bounds.Box.denseLipschitzBound
          (segmentPolynomial segment) parameterAmbient *
        (left - right) ^ 2 := by
  unfold variationBound
  rfl

end

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- The retained variation bound is nonnegative for every pair of parameters. -/
theorem variationBound_nonneg {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Coordinate) :
    0 <= variationBound segment left right := by
  unfold variationBound
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (Bounds.Box.denseLipschitzBound_pos
      (segmentPolynomial segment) parameterAmbient).le
    (Fraction.Order.Arithmetic.sq_nonneg_direct (left - right))

open Purelib.Polynomial in
/-- One quarter of the original segment's squared clearance bound. -/
@[expose] def squareRootDerivativeThreshold {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  segment.clearanceBound / 4

open Purelib.Approximation.Rational in
open Purelib.Polynomial in
/-- Four times the positive dyadic square radius of the derivative threshold. -/
@[expose] def squareRootDerivativeMargin {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  4 * SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius
    (squareRootDerivativeThreshold segment)

open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- The square-root residual threshold is strictly positive. -/
theorem squareRootDerivativeThreshold_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    0 < squareRootDerivativeThreshold segment :=
  Fraction.Order.Field.div_pos_direct segment.clearanceBound_positive
    (by decide)

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- The square-root derivative margin is strictly positive. -/
theorem squareRootDerivativeMargin_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    0 < squareRootDerivativeMargin segment :=
  Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_positive _)

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
/-- Certify derivative separation for the square-root polynomial at an interior segment parameter.

The original segment clearance bounds the radicand away from zero. A residual below one quarter of that clearance gives
the retained dyadic lower bound for the squared derivative norm. -/
@[expose] def squareRootDerivativeSeparation
    {polynomial : GaussianPolynomial} {ambient rootAmbient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1) :
    Derivative.Separation.Basic.Certificate
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial
        (polynomial.eval (segment.pointAt parameter))
        SquareRootDegree.degreeTwo) rootAmbient where
  threshold := squareRootDerivativeThreshold segment
  threshold_pos := squareRootDerivativeThreshold_positive segment
  margin := squareRootDerivativeMargin segment
  margin_pos := squareRootDerivativeMargin_positive segment
  lower := by
    intro root _rootInside residualSmall
    let base := polynomial.eval (segment.pointAt parameter)
    let rootPolynomial := Purelib.Polynomial.Power.Gaussian.rootPolynomial base
      SquareRootDegree.degreeTwo
    let baseClearance := segment.clearanceBound
    let threshold := squareRootDerivativeThreshold segment
    let rootNorm :=
      Data.Gaussian.Norm.Basic.normSq root
    have baseLower : baseClearance ≤
        Data.Gaussian.Norm.Basic.normSq base := by
      exact segment.clearanceBound_le_eval_normSq
        (segment.pointAt_onCertifiedLine parameter inside)
    have baseIdentity : base = root ^ 2 - rootPolynomial.eval root := by
      rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval]
      change base = root ^ 2 - (root ^ 2 - base)
      apply Basic.ext <;>
        simp only [Basic.sub_re,
          Basic.sub_im] <;> ring1
    have baseUpper :
        Data.Gaussian.Norm.Basic.normSq base ≤
          2 * (rootNorm ^ 2 + threshold) := by
      calc
        Data.Gaussian.Norm.Basic.normSq base =
            Data.Gaussian.Norm.Basic.normSq
              (root ^ 2 - rootPolynomial.eval root) := by rw [baseIdentity]
        _ ≤ 2 *
            (Data.Gaussian.Norm.Basic.normSq (root ^ 2) +
              Data.Gaussian.Norm.Basic.normSq
                (rootPolynomial.eval root)) :=
          Norm.Bounds.normSq_sub_le_two _ _
        _ = 2 * (rootNorm ^ 2 +
              Data.Gaussian.Norm.Basic.normSq
                (rootPolynomial.eval root)) := by
          rw [Power.normSq_pow]
        _ ≤ 2 * (rootNorm ^ 2 + threshold) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (by
              calc
                rootNorm ^ 2 +
                    Data.Gaussian.Norm.Basic.normSq
                      (rootPolynomial.eval root) =
                    Data.Gaussian.Norm.Basic.normSq
                        (rootPolynomial.eval root) + rootNorm ^ 2 := by ring1
                _ ≤ threshold + rootNorm ^ 2 :=
                  Fraction.Order.Arithmetic.add_le_add_right_direct
                    residualSmall (rootNorm ^ 2)
                _ = rootNorm ^ 2 + threshold := by ring1)
            (by decide)
    have clearanceToSquare : baseClearance / 4 ≤ rootNorm ^ 2 := by
      apply (Fraction.Order.Field.div_le_iff_pos
        (show (0 : Coordinate) < 4 by decide)).2
      have halfAddHalf :
          baseClearance / 2 + baseClearance / 2 = baseClearance := by
        apply Fraction.Field.mul_right_cancel_of_ne
          (show (2 : Coordinate) ≠ 0 by decide)
        calc
          (baseClearance / 2 + baseClearance / 2) * 2 =
              (baseClearance / 2) * 2 +
                (baseClearance / 2) * 2 := by rw [add_mul]
          _ = baseClearance + baseClearance := by
            rw [Fraction.Field.div_mul_cancel_of_ne _ 2
                (by decide)]
          _ = baseClearance * 2 := by ring1
      have twiceThreshold : 2 * threshold = baseClearance / 2 := by
        dsimp only [threshold, squareRootDerivativeThreshold,
          baseClearance]
        apply Fraction.Field.mul_right_cancel_of_ne
          (show (2 : Coordinate) ≠ 0 by decide)
        calc
          (2 * (segment.clearanceBound / 4)) * 2 =
              (segment.clearanceBound / 4) * 4 := by ring1
          _ = segment.clearanceBound :=
            Fraction.Field.div_mul_cancel_of_ne _ 4 (by decide)
          _ = (segment.clearanceBound / 2) * 2 :=
            (Fraction.Field.div_mul_cancel_of_ne _ 2
              (by decide)).symm
      have reduced : baseClearance / 2 ≤ 2 * rootNorm ^ 2 := by
        apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
          (c := baseClearance / 2)
        calc
          baseClearance / 2 + baseClearance / 2 = baseClearance := halfAddHalf
          _ ≤ 2 * (rootNorm ^ 2 + threshold) := baseLower.trans baseUpper
          _ = 2 * rootNorm ^ 2 + baseClearance / 2 := by
            rw [mul_add, twiceThreshold]
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct reduced
          (show (0 : Coordinate) ≤ 2 by decide)
      have scaledClearance :
          baseClearance ≤ (2 * rootNorm ^ 2) * 2 := by
        rwa [Fraction.Field.div_mul_cancel_of_ne _ 2
          (by decide)] at scaled
      calc
        baseClearance ≤ (2 * rootNorm ^ 2) * 2 := scaledClearance
        _ = rootNorm ^ 2 * 4 := by ring1
    let dyadicRoot := SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius threshold
    have dyadicSquareLe : dyadicRoot ^ 2 ≤ rootNorm ^ 2 :=
      (SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_sq_lt
        (squareRootDerivativeThreshold_positive segment)).le.trans
          (by
            simpa only [threshold, squareRootDerivativeThreshold] using
              clearanceToSquare)
    have dyadicLeRoot : dyadicRoot ≤ rootNorm :=
      Fraction.Order.Arithmetic.le_of_sq_le_sq_direct
        (Norm.Basic.normSq_nonneg root)
        dyadicSquareLe
    rw [Gaussian.derivative_eval,
      Norm.Basic.normSq_mul,
      Power.normSq_pow,
      SquareRootDegree.degreeTwo_value]
    have normSqTwo :
        Data.Gaussian.Norm.Basic.normSq
            ((2 : Nat) : Gaussian) = 4 := by
      simp only [Data.Gaussian.Norm.Basic.normSq,
        Cast.natCast_re,
        Cast.natCast_im]
      ring1
    rw [normSqTwo]
    simp only [Nat.reduceSub, pow_one]
    change squareRootDerivativeMargin segment ≤ 4 * rootNorm
    unfold squareRootDerivativeMargin
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      dyadicLeRoot (by decide)

section
open Purelib.Polynomial
/-- The separation certificate retains the exact segment threshold. -/
@[simp] theorem squareRootDerivativeSeparation_threshold
    {polynomial : GaussianPolynomial} {ambient rootAmbient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1) :
    (squareRootDerivativeSeparation (rootAmbient := rootAmbient)
      segment parameter inside).threshold =
        squareRootDerivativeThreshold segment := rfl

/-- The separation certificate retains the exact segment derivative margin. -/
@[simp] theorem squareRootDerivativeSeparation_margin
    {polynomial : GaussianPolynomial} {ambient rootAmbient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1) :
    (squareRootDerivativeSeparation (rootAmbient := rootAmbient)
      segment parameter inside).margin =
        squareRootDerivativeMargin segment := rfl

end

/-- The rational arithmetic midpoint of two parameters. -/
@[expose] def midpoint (left right : Coordinate) : Coordinate := (left + right) / 2

section
open Purelib.Data.Rat
/-- For ordered parameters, the left endpoint is at most their midpoint. -/
theorem left_le_midpoint {left right : Coordinate} (ordered : left <= right) :
    left <= midpoint left right := by
  apply (Fraction.Order.Field.le_div_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    left * 2 = left + left := by ring1
    _ <= left + right := add_le_add (le_refl _) ordered

/-- For ordered parameters, the midpoint is at most the right endpoint. -/
theorem midpoint_le_right {left right : Coordinate} (ordered : left <= right) :
    midpoint left right <= right := by
  apply (Fraction.Order.Field.div_le_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    left + right <= right + right := add_le_add ordered (le_refl _)
    _ = right * 2 := by ring1

/-- For strictly ordered parameters, the left endpoint is strictly below the midpoint. -/
theorem left_lt_midpoint {left right : Coordinate} (ordered : left < right) :
    left < midpoint left right := by
  apply (Fraction.Order.Field.lt_div_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    left * 2 = left + left := by ring1
    _ < left + right :=
      Fraction.Order.Arithmetic.add_lt_add_left_direct ordered left

/-- For strictly ordered parameters, the midpoint is strictly below the right endpoint. -/
theorem midpoint_lt_right {left right : Coordinate} (ordered : left < right) :
    midpoint left right < right := by
  apply (Fraction.Order.Field.div_lt_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    left + right < right + right :=
      Fraction.Order.Arithmetic.add_lt_add_right_direct ordered right
    _ = right * 2 := by ring1

/-- The midpoint of two unit-interval parameters lies in the unit interval. -/
theorem midpoint_inside {left right : Coordinate}
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1) :
    (0 : Coordinate) <= midpoint left right ∧ midpoint left right <= 1 := by
  constructor
  · exact Fraction.Order.Field.div_nonneg_direct
      (add_nonneg leftInside.1 rightInside.1) (by decide)
  · apply (Fraction.Order.Field.div_le_iff_pos
      (show (0 : Coordinate) < 2 by decide)).2
    calc
      left + right <= 1 + 1 := add_le_add leftInside.2 rightInside.2
      _ = 1 * 2 := by ring1

/-- The displacement from the left endpoint to the midpoint is half the full signed displacement. -/
private theorem left_sub_midpoint (left right : Coordinate) :
    left - midpoint left right = (left - right) / 2 := by
  apply Fraction.Field.mul_right_cancel_of_ne
    (show (2 : Coordinate) ≠ 0 by decide)
  calc
    (left - midpoint left right) * 2 =
        left * 2 - midpoint left right * 2 := by ring1
    _ = left * 2 - (left + right) := by
      rw [midpoint,
        Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)]
    _ = left - right := by ring1
    _ = ((left - right) / 2) * 2 :=
      (Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)).symm

/-- The displacement from the midpoint to the right endpoint is half the full signed displacement. -/
private theorem midpoint_sub_right (left right : Coordinate) :
    midpoint left right - right = (left - right) / 2 := by
  apply Fraction.Field.mul_right_cancel_of_ne
    (show (2 : Coordinate) ≠ 0 by decide)
  calc
    (midpoint left right - right) * 2 =
        midpoint left right * 2 - right * 2 := by ring1
    _ = (left + right) - right * 2 := by
      rw [midpoint,
        Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)]
    _ = left - right := by ring1
    _ = ((left - right) / 2) * 2 :=
      (Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)).symm

open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
/-- The left half-segment has exactly one quarter of the original variation bound. -/
theorem variationBound_left_midpoint
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Coordinate) :
    variationBound segment left (midpoint left right) =
      variationBound segment left right / 4 := by
  unfold variationBound
  rw [left_sub_midpoint, pow_two,
    Fraction.Field.div_mul_div_direct,
    show (2 : Coordinate) * 2 = 4 by decide]
  rw [Fraction.Field.div_eq_mul_inv_direct
      ((left - right) * (left - right)) 4]
  simp only [pow_two]
  rw [Fraction.Field.div_eq_mul_inv_direct
      (Bounds.Box.denseLipschitzBound
        (segmentPolynomial segment) parameterAmbient *
          ((left - right) * (left - right))) 4]
  ring1

/-- The right half-segment has exactly one quarter of the original variation bound. -/
theorem variationBound_midpoint_right
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Coordinate) :
    variationBound segment (midpoint left right) right =
      variationBound segment left right / 4 := by
  unfold variationBound
  rw [midpoint_sub_right, pow_two,
    Fraction.Field.div_mul_div_direct,
    show (2 : Coordinate) * 2 = 4 by decide]
  rw [Fraction.Field.div_eq_mul_inv_direct
      ((left - right) * (left - right)) 4]
  simp only [pow_two]
  rw [Fraction.Field.div_eq_mul_inv_direct
      (Bounds.Box.denseLipschitzBound
        (segmentPolynomial segment) parameterAmbient *
          ((left - right) * (left - right))) 4]
  ring1

end

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- The polynomial's squared variation between two segment parameters is bounded by the retained formula.

Both parameters lie in the unit interval of the same cleared segment; affine substitution reduces the estimate to its
exact parameter-box Lipschitz bound. -/
theorem evaluation_variation_le {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (_within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1) :
    Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval (segment.pointAt left) -
          polynomial.eval (segment.pointAt right)) <=
      variationBound segment left right := by
  have variation :=
    Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound
      (segmentPolynomial segment)
      (parameterAmbient_contains left leftInside)
      (parameterAmbient_contains right rightInside)
  rw [segmentPolynomial_eval, segmentPolynomial_eval] at variation
  unfold variationBound
  change _ <= Bounds.Box.denseLipschitzBound
      (segmentPolynomial segment) parameterAmbient * (left - right) ^ 2
  exact variation.trans_eq (by
    congr 1
    unfold Data.Gaussian.Norm.Basic.normSq
    simp only [Basic.sub_re,
      Basic.sub_im,
      Cast.ofCoordinate_re,
      Cast.ofCoordinate_im]
    ring1)

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- The variation bound to an intermediate parameter is at most the full ordered-interval bound.

The retained order witnesses compare the two unsigned displacements from the
same left endpoint. Squaring and the nonnegative Lipschitz factor preserve that bound. -/
theorem variationBound_le_of_between
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {left parameter right : Coordinate}
    (leftParameter : left <= parameter)
    (parameterRight : parameter <= right) :
    variationBound segment left parameter <=
      variationBound segment left right := by
  have parameterDeltaNonnegative : (0 : Coordinate) <= parameter - left :=
    Fraction.Order.Arithmetic.sub_nonneg_direct leftParameter
  have deltaOrder : parameter - left <= right - left := by
    exact Fraction.Order.Arithmetic.sub_le_sub_right_direct parameterRight left
  have squareOrder : (parameter - left) ^ 2 <= (right - left) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      parameterDeltaNonnegative deltaOrder 2
  have signedSquareOrder : (left - parameter) ^ 2 <=
      (left - right) ^ 2 := by
    calc
      (left - parameter) ^ 2 = (parameter - left) ^ 2 := by ring1
      _ <= (right - left) ^ 2 := squareOrder
      _ = (left - right) ^ 2 := by ring1
  unfold variationBound
  apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
  · exact signedSquareOrder
  · exact
      (Bounds.Box.denseLipschitzBound_pos
        (segmentPolynomial segment) parameterAmbient).le

section
open Purelib.Polynomial
/-- Continue the original square-root owner between two parameters whose variation is below its clearance.

The cleared segment supplies target nonvanishing, while the same retained variation estimate certifies the continuation
displacement. -/
@[expose] def advance {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt left)))
    (small : variationBound segment left right <
      owner.track.initial.clearance.bound) :
    Owner (polynomial.eval (segment.pointAt right)) :=
  owner.advance
    (segment.pointAt_eval_ne_zero right rightInside)
    ((evaluation_variation_le segment within left right leftInside
      rightInside).trans_lt small)

/-- Attempt one continuation step using the exact retained variation and source-clearance comparison.

A successful result is the certified advanced owner. Failure reports only that this sufficient step bound was not small
enough. -/
@[expose] def tryAdvance {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt left))) :
    Option (Owner (polynomial.eval (segment.pointAt right))) :=
  if small : variationBound segment left right <
      owner.track.initial.clearance.bound then
    some (advance segment within left right leftInside rightInside owner small)
  else none

/-- A variation bound below the source clearance returns the exact certified advanced owner.

The supplied strict comparison selects the successful branch of the same
finite attempt and retains its exact advanced square-root owner. -/
theorem tryAdvance_eq_some_of_small
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt left)))
    (small : variationBound segment left right <
      owner.track.initial.clearance.bound) :
    tryAdvance segment within left right leftInside rightInside owner =
      some (advance segment within left right leftInside rightInside owner small) := by
  unfold tryAdvance
  exact dif_pos small

/-- A failed strict variation comparison makes the one-step attempt return no owner.

The supplied failure witness selects the unsuccessful branch of the same
attempt. It states only failure of this sufficient clearance comparison. -/
theorem tryAdvance_eq_none_of_not_small
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt left)))
    (notSmall : ¬ variationBound segment left right <
      owner.track.initial.clearance.bound) :
    tryAdvance segment within left right leftInside rightInside owner = none := by
  unfold tryAdvance
  exact dif_neg notSmall

end

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Topology in
/-- Build a seeded one-step chain from the selected independent sheet at the left parameter.

The supplied variation bound certifies the actual advanced owner at the right parameter, retaining the original sheet
index. -/
@[expose] def oneStep {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1)
    (sheet : Fin 2)
    (small : variationBound segment left right <
      (SquareRootContinuationChain.Owner.independent
        (segment.pointAt_eval_ne_zero left leftInside) sheet).track.initial.clearance.bound) :
    SquareRootContinuationChain.SeededChain
      (polynomial.eval (segment.pointAt left))
      (segment.pointAt_eval_ne_zero left leftInside) where
  sheet := sheet
  continuation := by
    let initial :=
      SquareRootContinuationChain.PackedOwner.independent
      (segment.pointAt_eval_ne_zero left leftInside) sheet
    let target := polynomial.eval (segment.pointAt right)
    have targetNonzero := segment.pointAt_eval_ne_zero right rightInside
    have moveSmall :
        Data.Gaussian.Norm.Basic.normSq
            (initial.parameter - target) <
          initial.owner.track.initial.clearance.bound := by
      exact (evaluation_variation_le segment within left right leftInside
        rightInside).trans_lt small
    exact SquareRootContinuationChain.Chain.single
      initial target targetNonzero moveSmall

open Purelib.Polynomial in
open Purelib.Riemann.Topology in
/-- The seeded one-step chain ends at the polynomial value of the right segment parameter. -/
@[simp] theorem oneStep_endpoint_parameter
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1)
    (sheet : Fin 2)
    (small : variationBound segment left right <
      (SquareRootContinuationChain.Owner.independent
        (segment.pointAt_eval_ne_zero left leftInside) sheet).track.initial.clearance.bound) :
    (oneStep segment within left right leftInside rightInside sheet small).endpoint.parameter =
      polynomial.eval (segment.pointAt right) := rfl

open Purelib.Polynomial in
set_option genInjectivity false in
/-- A finite sequence of certified parameter steps retaining each exact advanced square-root owner.

Every endpoint stays in the unit interval, and each tail begins at the owner produced by its own retained variation
witness. -/
inductive Subdivision {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) :
    (left : Coordinate) →
      (leftInside : (0 : Coordinate) <= left ∧ left <= 1) →
      Owner (polynomial.eval (segment.pointAt left)) → Type
  /-- Stop at the exact current unit-interval parameter and its retained square-root owner. -/ | stop (left :
    Coordinate)
      (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
      (owner : Owner (polynomial.eval (segment.pointAt left))) :
      Subdivision segment within left leftInside owner
  /-- Retain one certified parameter step and the subdivision starting at its actual advanced owner. -/ | next (left :
    Coordinate)
      (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
      (owner : Owner (polynomial.eval (segment.pointAt left)))
      (right : Coordinate)
      (rightInside : (0 : Coordinate) <= right ∧ right <= 1)
      (small : variationBound segment left right <
        owner.track.initial.clearance.bound)
      (remaining : Subdivision segment within right rightInside
        (advance segment within left right leftInside rightInside owner small)) :
      Subdivision segment within left leftInside owner

constructive_injectivity Subdivision

namespace Subdivision

set_option genInjectivity false in
/-- A rational segment parameter retaining its membership in the unit interval.

The same rational value carries its lower and upper parameter bounds.
Subdivision endpoints use that retained value and certificate together. -/
structure Endpoint where
  /-- The retained rational segment parameter. -/ parameter : Coordinate
  /-- The retained parameter lies between zero and one. -/ inside : (0 : Coordinate) <= parameter ∧ parameter <= 1

constructive_injectivity Endpoint

section
open Purelib.Polynomial
/-- Read the exact terminal parameter of the certified subdivision. -/
@[expose] def endpoint {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))} :
    Subdivision segment within left leftInside owner → Endpoint
  | .stop left leftInside _ => ⟨left, leftInside⟩
  | .next _ _ _ _ _ _ remaining => remaining.endpoint

/-- Read the retained square-root owner indexed by the polynomial value at the terminal parameter. -/
@[expose] def terminalOwner {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))} :
    (subdivision : Subdivision segment within left leftInside owner) →
      Owner (polynomial.eval
        (segment.pointAt subdivision.endpoint.parameter))
  | .stop _ _ owner => owner
  | .next _ _ _ _ _ _ remaining => remaining.terminalOwner

/-- Count the certified continuation steps in the subdivision. -/
@[expose] def stepCount {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))} :
    Subdivision segment within left leftInside owner → Nat
  | .stop _ _ _ => 0
  | .next _ _ _ _ _ _ remaining => remaining.stepCount + 1

/-- Attempt continuation through an ordered list of retained parameter samples.

Each successful step reuses its exact advanced owner for the remaining samples. The attempt returns no subdivision if
any sufficient clearance comparison fails. -/
@[expose] def trySamples {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (current : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter))) :
    (remaining : List Endpoint) →
      Option (Subdivision segment within current.parameter current.inside owner)
  | [] => some (.stop current.parameter current.inside owner)
  | sample :: rest =>
      if small : variationBound segment current.parameter sample.parameter <
          owner.track.initial.clearance.bound then
        match trySamples segment within sample
            (advance segment within current.parameter sample.parameter
              current.inside sample.inside owner small) rest with
        | none => none
        | some tail => some (.next current.parameter current.inside owner
            sample.parameter sample.inside small tail)
      else none

/-- An empty sample list returns the stopped subdivision at the original current owner. -/
@[simp] theorem trySamples_nil {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter))) :
    trySamples segment within current owner [] =
      some (.stop current.parameter current.inside owner) := rfl

/-- A successful sample-list attempt has exactly as many steps as supplied samples. -/
theorem trySamples_stepCount {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter)))
    (remaining : List Endpoint)
    {subdivision : Subdivision segment within current.parameter
      current.inside owner}
    (success : trySamples segment within current owner remaining =
      some subdivision) :
    subdivision.stepCount = remaining.length := by
  induction remaining generalizing current owner subdivision with
  | nil =>
      simp only [trySamples] at success
      cases success
      rfl
  | cons sample rest inductionHypothesis =>
      simp only [trySamples] at success
      split at success
      next small =>
        split at success
        next recursiveFailure => contradiction
        next tail recursiveSuccess =>
          cases success
          simp only [stepCount, List.length_cons]
          exact congrArg Nat.succ
            (inductionHypothesis sample
              (advance segment within current.parameter sample.parameter
                current.inside sample.inside owner small)
              (subdivision := tail) recursiveSuccess)
      next notSmall => contradiction

end

/-- Read the last supplied endpoint, using the current endpoint when the list is empty. -/
@[expose] def finalTarget (current : Endpoint) : List Endpoint -> Endpoint
  | [] => current
  | sample :: remaining => finalTarget sample remaining

/-- Reading the final endpoint of concatenated samples composes the two endpoint readings. -/
theorem finalTarget_append (current : Endpoint)
    (first second : List Endpoint) :
    finalTarget current (first ++ second) =
      finalTarget (finalTarget current first) second := by
  induction first generalizing current with
  | nil => rfl
  | cons sample remaining inductionHypothesis =>
      exact inductionHypothesis sample

open Purelib.Polynomial in
/-- A successful sample-list attempt ends at the final supplied parameter. -/
theorem trySamples_endpoint_parameter
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter)))
    (remaining : List Endpoint)
    {subdivision : Subdivision segment within current.parameter
      current.inside owner}
    (success : trySamples segment within current owner remaining =
      some subdivision) :
    subdivision.endpoint.parameter =
      (finalTarget current remaining).parameter := by
  induction remaining generalizing current owner subdivision with
  | nil =>
      simp only [trySamples] at success
      cases success
      rfl
  | cons sample rest inductionHypothesis =>
      simp only [trySamples] at success
      split at success
      next small =>
        split at success
        next recursiveFailure => contradiction
        next tail recursiveSuccess =>
          cases success
          exact inductionHypothesis sample
            (advance segment within current.parameter sample.parameter
              current.inside sample.inside owner small)
            (subdivision := tail) recursiveSuccess
      next notSmall => contradiction

/-- Bisect the original parameter interval recursively and list its ordered right endpoints.

Depth zero retains only the original right endpoint; each successor concatenates the two exact midpoint subdivisions. -/
@[expose] def dyadicTargets : Nat -> Endpoint -> Endpoint -> List Endpoint
  | 0, _left, right => [right]
  | depth + 1, left, right =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter,
          midpoint_inside left.inside right.inside⟩
      dyadicTargets depth left middle ++
        dyadicTargets depth middle right

set_option genInjectivity false in
/-- An ordered pair of retained unit-interval endpoints.

Both endpoint records retain their own exact parameters and unit-interval
certificates. The displayed left-to-right order is the original list order. -/
structure ParameterEdge where
  /-- The retained left endpoint of the parameter edge. -/ left : Endpoint
  /-- The retained right endpoint of the parameter edge. -/ right : Endpoint

constructive_injectivity ParameterEdge

namespace ParameterEdge

/-- Equal left and right parameter values identify the retained parameter edge.

The endpoint records retain only those exact rational values and their
unit-interval certificates. Equality of both parameters therefore identifies
the complete edge, with its original endpoint ownership unchanged. -/
theorem eq_of_parameters (first second : ParameterEdge)
    (same : first.left.parameter = second.left.parameter ∧
      first.right.parameter = second.right.parameter) : first = second := by
  cases first with
  | mk left right =>
    cases second with
    | mk otherLeft otherRight =>
      cases left
      cases right
      cases otherLeft
      cases otherRight
      rcases same with ⟨leftEq, rightEq⟩
      dsimp only at leftEq rightEq
      subst_vars
      rfl

end ParameterEdge

/-- Form consecutive parameter edges from the current endpoint and the supplied sample list. -/
@[expose] def parameterEdgesFrom : Endpoint -> List Endpoint -> List ParameterEdge
  | _current, [] => []
  | current, endpoint :: remaining =>
      { left := current, right := endpoint } ::
        parameterEdgesFrom endpoint remaining

/-- Edges from concatenated samples split at the exact final endpoint of the first list. -/
theorem parameterEdgesFrom_append (current : Endpoint)
    (first second : List Endpoint) :
    parameterEdgesFrom current (first ++ second) =
      parameterEdgesFrom current first ++
        parameterEdgesFrom (finalTarget current first) second := by
  induction first generalizing current with
  | nil => rfl
  | cons endpoint remaining inductionHypothesis =>
      simp only [List.cons_append, parameterEdgesFrom, finalTarget]
      exact congrArg (List.cons { left := current, right := endpoint })
        (inductionHypothesis endpoint)

/-- Recursively bisect a parameter interval into its ordered list of dyadic edges. -/
@[expose] def dyadicEdges : Nat -> Endpoint -> Endpoint -> List ParameterEdge
  | 0, left, right => [{ left := left, right := right }]
  | depth + 1, left, right =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter,
          midpoint_inside left.inside right.inside⟩
      dyadicEdges depth left middle ++ dyadicEdges depth middle right

/-- The right endpoints of the dyadic edge list are exactly the retained dyadic targets.

Each midpoint split uses the same two retained endpoint lists. Mapping the
right projection preserves their concatenation and recursive ordering. -/
theorem dyadicEdges_rights (depth : Nat) (left right : Endpoint) :
    (dyadicEdges depth left right).map (fun edge => edge.right) =
      dyadicTargets depth left right := by
  induction depth generalizing left right with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp only [dyadicEdges, dyadicTargets, Map.map_append]
      rw [inductionHypothesis, inductionHypothesis]

/-- Replace each retained parameter edge by its dyadic refinement at the additional depth. -/
@[expose] def refineDyadicEdges (additionalDepth : Nat)
    (edges : List ParameterEdge) : List ParameterEdge :=
  edges.flatMap fun edge =>
    dyadicEdges additionalDepth edge.left edge.right

/-- Subdivision at a sum of depths equals refinement of every original coarse dyadic edge.

The additional depth refines each original coarse edge in order. Structural
concatenation preserves its endpoints, midpoint splits and multiplicities. -/
theorem dyadicEdges_add (earlier additional : Nat)
    (left right : Endpoint) :
    dyadicEdges (earlier + additional) left right =
      refineDyadicEdges additional (dyadicEdges earlier left right) := by
  induction earlier generalizing left right with
  | zero =>
      rw [Nat.zero_add]
      change dyadicEdges additional left right = dyadicEdges additional left right ++ []
      exact (Append.append_nil _).symm
  | succ earlier inductionHypothesis =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter,
          midpoint_inside left.inside right.inside⟩
      rw [Nat.succ_add]
      change dyadicEdges (earlier + additional) left middle ++
          dyadicEdges (earlier + additional) middle right =
        (dyadicEdges earlier left middle ++ dyadicEdges earlier middle right).flatMap
          (fun edge => dyadicEdges additional edge.left edge.right)
      rw [Flatten.flatMap_append]
      exact congrArg₂ (fun first second : List ParameterEdge => first ++ second)
        (inductionHypothesis left middle) (inductionHypothesis middle right)

/-- Depth-d dyadic subdivision has exactly two to the power d edges.

Each successor depth concatenates the two retained midpoint subdivisions.
Their original lengths add to the displayed binary power. -/
@[simp] theorem dyadicEdges_length (depth : Nat)
    (left right : Endpoint) :
    (dyadicEdges depth left right).length = 2 ^ depth := by
  induction depth generalizing left right with
  | zero => rfl
  | succ depth inductionHypothesis =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter,
          midpoint_inside left.inside right.inside⟩
      calc
        (dyadicEdges (depth + 1) left right).length =
            (dyadicEdges depth left middle).length +
              (dyadicEdges depth middle right).length :=
          Append.length_append _ _
        _ = 2 ^ depth + 2 ^ depth :=
          congrArg₂ Nat.add (inductionHypothesis left middle)
            (inductionHypothesis middle right)
        _ = 2 ^ (depth + 1) := by rw [pow_succ, Nat.mul_two]

/-- Compute one dyadic parameter edge directly from its bounded index.

The index chooses the left or right midpoint interval recursively; the retained bound certifies the adjusted index in
the selected half. -/
@[expose] def dyadicEdgeAt : (depth : Nat) -> Endpoint -> Endpoint ->
    Fin (2 ^ depth) -> ParameterEdge
  | 0, left, right, _index => { left := left, right := right }
  | depth + 1, left, right, index =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter,
          midpoint_inside left.inside right.inside⟩
      if lower : index.val < 2 ^ depth then
        dyadicEdgeAt depth left middle ⟨index.val, lower⟩
      else
        dyadicEdgeAt depth middle right
          ⟨index.val - 2 ^ depth, by
            have total := index.isLt
            have total' : index.val < 2 ^ depth + 2 ^ depth := by
              have doubled : 2 ^ (depth + 1) = 2 ^ depth + 2 ^ depth := by
                rw [pow_succ, Nat.mul_two]
              exact (congrArg (fun bound : Nat => index.val < bound) doubled).mp total
            exact Subtraction.sub_lt_left_of_lt_add
              (Nat.le_of_not_lt lower) total'⟩

/-- Every indexed dyadic edge inherits weak ordering of the original endpoints. -/
theorem dyadicEdgeAt_ordered (depth : Nat) (left right : Endpoint)
    (index : Fin (2 ^ depth)) (ordered : left.parameter <= right.parameter) :
    (dyadicEdgeAt depth left right index).left.parameter <=
      (dyadicEdgeAt depth left right index).right.parameter := by
  induction depth generalizing left right with
  | zero => exact ordered
  | succ depth inductionHypothesis =>
      unfold dyadicEdgeAt
      dsimp only
      split
      · apply inductionHypothesis
        exact left_le_midpoint ordered
      · apply inductionHypothesis
        exact midpoint_le_right ordered

/-- Every indexed dyadic edge inherits strict ordering of the original endpoints. -/
theorem dyadicEdgeAt_strict (depth : Nat) (left right : Endpoint)
    (index : Fin (2 ^ depth)) (ordered : left.parameter < right.parameter) :
    (dyadicEdgeAt depth left right index).left.parameter <
      (dyadicEdgeAt depth left right index).right.parameter := by
  induction depth generalizing left right with
  | zero => exact ordered
  | succ depth inductionHypothesis =>
      unfold dyadicEdgeAt
      dsimp only
      split
      · apply inductionHypothesis
        exact left_lt_midpoint ordered
      · apply inductionHypothesis
        exact midpoint_lt_right ordered

/-- Divide the original variation bound by four at each retained depth. -/
@[expose] def quarterVariation : Nat -> Coordinate -> Coordinate
  | 0, bound => bound
  | depth + 1, bound => quarterVariation depth (bound / 4)

open Purelib.Data.Rat in
/-- Repeated division by four preserves ordering of the original bounds. -/
theorem quarterVariation_mono (depth : Nat) {left right : Coordinate}
    (lessEqual : left <= right) :
    quarterVariation depth left <= quarterVariation depth right := by
  induction depth generalizing left right with
  | zero => exact lessEqual
  | succ depth inductionHypothesis =>
      apply inductionHypothesis
      apply (Fraction.Order.Field.div_le_iff_pos (by decide)).2
      rw [Fraction.Field.div_mul_cancel_of_ne]
      · exact lessEqual
      · decide

open Purelib.Polynomial in
/-- Every indexed dyadic edge has the original variation bound divided by four per depth. -/
theorem variationBound_dyadicEdgeAt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (depth : Nat) (left right : Endpoint) (index : Fin (2 ^ depth)) :
    variationBound segment
        (dyadicEdgeAt depth left right index).left.parameter
        (dyadicEdgeAt depth left right index).right.parameter =
      quarterVariation depth
        (variationBound segment left.parameter right.parameter) := by
  induction depth generalizing left right with
  | zero => rfl
  | succ depth inductionHypothesis =>
      unfold dyadicEdgeAt
      dsimp only
      split
      · rw [inductionHypothesis, variationBound_left_midpoint]
        rfl
      · rw [inductionHypothesis, variationBound_midpoint_right]
        rfl

/-- Depth-d dyadic subdivision has exactly two to the power d target endpoints.

The two retained midpoint target lists contribute their original lengths at
each successor depth, preserving the exact binary count. -/
@[simp] theorem dyadicTargets_length (depth : Nat)
    (left right : Endpoint) :
    (dyadicTargets depth left right).length = 2 ^ depth := by
  induction depth generalizing left right with
  | zero => rfl
  | succ depth inductionHypothesis =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter,
          midpoint_inside left.inside right.inside⟩
      calc
        (dyadicTargets (depth + 1) left right).length =
            (dyadicTargets depth left middle).length +
              (dyadicTargets depth middle right).length :=
          Append.length_append _ _
        _ = 2 ^ depth + 2 ^ depth :=
          congrArg₂ Nat.add (inductionHypothesis left middle)
            (inductionHypothesis middle right)
        _ = 2 ^ (depth + 1) := by rw [pow_succ, Nat.mul_two]

/-- The final dyadic target is exactly the original right endpoint. -/
@[simp] theorem dyadicTargets_finalTarget (depth : Nat)
    (left right : Endpoint) :
    finalTarget left (dyadicTargets depth left right) = right := by
  induction depth generalizing left right with
  | zero => rfl
  | succ depth inductionHypothesis =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter,
          midpoint_inside left.inside right.inside⟩
      rw [dyadicTargets, finalTarget_append,
        inductionHypothesis left middle,
        inductionHypothesis middle right]

/-- Consecutive edges of the exact dyadic target list equal the retained dyadic edge list. -/
theorem parameterEdgesFrom_dyadicTargets (depth : Nat)
    (left right : Endpoint) :
    parameterEdgesFrom left (dyadicTargets depth left right) =
      dyadicEdges depth left right := by
  induction depth generalizing left right with
  | zero => rfl
  | succ depth inductionHypothesis =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter,
          midpoint_inside left.inside right.inside⟩
      rw [dyadicTargets, parameterEdgesFrom_append,
        dyadicTargets_finalTarget]
      change
        parameterEdgesFrom left (dyadicTargets depth left middle) ++
            parameterEdgesFrom middle (dyadicTargets depth middle right) =
          dyadicEdges depth left middle ++ dyadicEdges depth middle right
      rw [inductionHypothesis, inductionHypothesis]

open Purelib.Polynomial in
/-- Ordered successive parameters whose exact segment variation bounds share a common ceiling. -/
@[expose] def EdgeVariationBound {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (bound : Coordinate) : Endpoint -> List Endpoint -> Prop
  | _current, [] => True
  | current, endpoint :: remaining =>
      current.parameter <= endpoint.parameter /\
        variationBound segment current.parameter endpoint.parameter <= bound /\
          EdgeVariationBound segment bound endpoint remaining

namespace EdgeVariationBound

open Purelib.Polynomial in
/-- Concatenate two ordered variation-bounded sample lists meeting at the first list's final endpoint. -/
theorem append {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (bound : Coordinate) :
    forall (current : Endpoint) (first second : List Endpoint),
      EdgeVariationBound segment bound current first ->
        EdgeVariationBound segment bound (finalTarget current first) second ->
          EdgeVariationBound segment bound current (first ++ second)
  | _current, [], _second, _firstBound, secondBound => secondBound
  | _current, endpoint :: remaining, second, firstBound, secondBound =>
      ⟨firstBound.1, firstBound.2.1,
        append segment bound endpoint remaining second firstBound.2.2
          secondBound⟩

end EdgeVariationBound

open Purelib.Algebra in
open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- Dividing the original scale by four advances its quarter-radius index by one. -/
private theorem quarterRadius_div_four (scale : Coordinate) (index : Nat) :
    Geometric.Basic.quarterRadius (scale / 4) index =
      Geometric.Basic.quarterRadius scale (index + 1) := by
  have scaleDiv : scale / 4 = scale * (1 / 4 : Coordinate) := by
    rw [Field.ExplicitField.div_eq_mul_inv,
      Field.ExplicitField.div_eq_mul_inv,
      Fraction.Field.one_mul]
  rw [Geometric.Basic.quarterRadius_eq_mul_pow,
    Geometric.Basic.quarterRadius_eq_mul_pow, scaleDiv, pow_succ]
  ring1

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- Every ordered dyadic target step obeys the original interval's geometric quarter-radius bound.

Midpoint bisection quarters the exact variation estimate, and concatenation preserves the common depth-dependent
ceiling. -/
theorem dyadicTargets_edgeVariationBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (depth : Nat) (left right : Endpoint)
    (ordered : left.parameter <= right.parameter) :
    EdgeVariationBound segment
      (Geometric.Basic.quarterRadius
        (variationBound segment left.parameter right.parameter) depth)
      left (dyadicTargets depth left right) := by
  induction depth generalizing left right with
  | zero =>
      refine ⟨ordered, ?_, trivial⟩
      rw [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
          Fraction.Field.mul_one_direct]
  | succ depth inductionHypothesis =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter,
          midpoint_inside left.inside right.inside⟩
      have leftBound := inductionHypothesis left middle
        (left_le_midpoint ordered)
      have rightBound := inductionHypothesis middle right
        (midpoint_le_right ordered)
      have leftScale :
          Geometric.Basic.quarterRadius
              (variationBound segment left.parameter middle.parameter) depth =
            Geometric.Basic.quarterRadius
              (variationBound segment left.parameter right.parameter)
                (depth + 1) := by
        change Geometric.Basic.quarterRadius
            (variationBound segment left.parameter
              (midpoint left.parameter right.parameter)) depth = _
        rw [variationBound_left_midpoint]
        exact quarterRadius_div_four _ _
      have rightScale :
          Geometric.Basic.quarterRadius
              (variationBound segment middle.parameter right.parameter) depth =
            Geometric.Basic.quarterRadius
              (variationBound segment left.parameter right.parameter)
                (depth + 1) := by
        change Geometric.Basic.quarterRadius
            (variationBound segment
              (midpoint left.parameter right.parameter) right.parameter)
              depth = _
        rw [variationBound_midpoint_right]
        exact quarterRadius_div_four _ _
      rw [leftScale] at leftBound
      rw [rightScale] at rightBound
      change EdgeVariationBound segment _ left
        (dyadicTargets depth left middle ++
          dyadicTargets depth middle right)
      apply EdgeVariationBound.append segment _ left
        (dyadicTargets depth left middle)
          (dyadicTargets depth middle right) leftBound
      simpa only [dyadicTargets_finalTarget] using rightBound

section
open Purelib.Polynomial
/-- Restrict the original cleared segment along the exact consecutive sample parameters.

Every resulting path edge retains its original segment clearance and ambient owner, with endpoint indexed by the exact
final sample. -/
@[expose] def geometricPath {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint) :
    (remaining : List Endpoint) ->
      Polynomial.Geometry.ClearPath polynomial ambient (segment.pointAt current.parameter)
        (segment.pointAt (finalTarget current remaining).parameter)
  | [] => .nil _
  | endpoint :: rest =>
      .cons
        (segment.restrict within current.parameter endpoint.parameter
          current.inside endpoint.inside)
        (geometricPath segment within endpoint rest)

/-- The restricted geometric path has one segment for each supplied target sample. -/
@[simp] theorem geometricPath_segmentCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (remaining : List Endpoint) :
    (geometricPath segment within current remaining).segmentCount =
      remaining.length := by
  induction remaining generalizing current with
  | nil => rfl
  | cons endpoint rest inductionHypothesis =>
      simp only [geometricPath, Polynomial.Geometry.ClearPath.segmentCount, List.length_cons]
      exact congrArg Nat.succ (inductionHypothesis endpoint)

/-- Read the exact dyadic target list as a cleared path between the original interval endpoints. -/
@[expose] def dyadicPath {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (depth : Nat)
    (left right : Endpoint) :
    Polynomial.Geometry.ClearPath polynomial ambient (segment.pointAt left.parameter)
      (segment.pointAt right.parameter) :=
  (geometricPath segment within left (dyadicTargets depth left right)).castFinish
    (congrArg (fun endpoint : Endpoint => segment.pointAt endpoint.parameter)
      (dyadicTargets_finalTarget depth left right))

/-- The dyadic cleared path has exactly two to the subdivision depth segments.

The cleared path retains one segment per dyadic target. Transport of its
final endpoint preserves that segment count and the exact binary length. -/
@[simp] theorem dyadicPath_segmentCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (depth : Nat)
    (left right : Endpoint) :
    (dyadicPath segment within depth left right).segmentCount = 2 ^ depth := by
  rw [dyadicPath, Polynomial.Geometry.ClearPath.segmentCount_castFinish,
    geometricPath_segmentCount, dyadicTargets_length]

/-- Attempt certified continuation along the exact dyadic target list at the supplied depth. -/
@[expose] def tryDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left right : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) :
    Option (Subdivision segment within left.parameter left.inside owner) :=
  trySamples segment within left owner (dyadicTargets depth left right)

/-- A successful dyadic attempt contains exactly two to the supplied depth continuation steps. -/
theorem tryDyadic_stepCount {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left right : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat)
    {subdivision : Subdivision segment within left.parameter left.inside owner}
    (success : tryDyadic segment within left right owner depth =
      some subdivision) :
    subdivision.stepCount = 2 ^ depth := by
  exact (trySamples_stepCount segment within left owner
    (dyadicTargets depth left right) success).trans
      (dyadicTargets_length depth left right)

/-- A successful dyadic attempt ends at the original right parameter. -/
theorem tryDyadic_endpoint_parameter
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left right : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat)
    {subdivision : Subdivision segment within left.parameter left.inside owner}
    (success : tryDyadic segment within left right owner depth =
      some subdivision) :
    subdivision.endpoint.parameter = right.parameter := by
  have endpoint := trySamples_endpoint_parameter segment within left owner
    (dyadicTargets depth left right) success
  simpa only [dyadicTargets_finalTarget] using endpoint

/-- Read the certified subdivision as the original segment restricted to its retained parameter steps. -/
@[expose] def toClearPath {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))} :
    (subdivision : Subdivision segment within left leftInside owner) →
      Polynomial.Geometry.ClearPath polynomial ambient (segment.pointAt left)
        (segment.pointAt subdivision.endpoint.parameter)
  | .stop left _ _ => .nil (segment.pointAt left)
  | .next left leftInside _ right rightInside _ remaining =>
      .cons
        (segment.restrict within left right leftInside rightInside)
        remaining.toClearPath

/-- The geometric path read from the subdivision remains in the original ambient box. -/
theorem toClearPath_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))}
    (subdivision : Subdivision segment within left leftInside owner) :
    subdivision.toClearPath.WithinAmbient := by
  induction subdivision with
  | stop => exact .nil _
  | next left leftInside owner right rightInside small remaining
      inductionHypothesis =>
      exact .cons
        (segment.restrict_withinAmbient within left right leftInside rightInside)
        inductionHypothesis

/-- Reading a subdivision as a geometric path preserves its exact step count. -/
@[simp] theorem toClearPath_segmentCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))}
    (subdivision : Subdivision segment within left leftInside owner) :
    subdivision.toClearPath.segmentCount = subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next left leftInside owner right rightInside small remaining
      inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

end

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- Read the certified subdivision as a square-root owner continuation chain.

Each chain step uses the original variation witness to certify its polynomial-value displacement, retaining the same
advanced owner in the tail. -/
@[expose] def toChain {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))} :
    (subdivision : Subdivision segment within left leftInside owner) →
      Chain ⟨polynomial.eval (segment.pointAt left), owner⟩
  | .stop _ _ _ => .nil _
  | .next left leftInside owner right rightInside small remaining => by
      let target := polynomial.eval (segment.pointAt right)
      let targetNonzero := segment.pointAt_eval_ne_zero right rightInside
      let moveSmall :
          Data.Gaussian.Norm.Basic.normSq
              (polynomial.eval (segment.pointAt left) - target) <
            owner.track.initial.clearance.bound :=
        (evaluation_variation_le segment within left right leftInside
          rightInside).trans_lt small
      exact .step _ target targetNonzero moveSmall remaining.toChain

section
open Purelib.Polynomial
/-- The continuation chain ends at the polynomial value of the subdivision's exact terminal parameter. -/
@[simp] theorem toChain_endpoint_parameter
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))}
    (subdivision : Subdivision segment within left leftInside owner) :
    subdivision.toChain.endpoint.parameter =
      polynomial.eval (segment.pointAt subdivision.endpoint.parameter) := by
  induction subdivision with
  | stop => rfl
  | next left leftInside owner right rightInside small remaining
      inductionHypothesis =>
      exact inductionHypothesis

/-- Reading a subdivision as a continuation chain preserves its exact step count. -/
@[simp] theorem toChain_length {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))}
    (subdivision : Subdivision segment within left leftInside owner) :
    subdivision.toChain.length = subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next left leftInside owner right rightInside small remaining
      inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

end

open Purelib.Polynomial in
open Purelib.Riemann.Topology in
/-- Retain the original sheet choice while reading its certified subdivision as a seeded continuation chain. -/
@[expose] def seeded {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    (sheet : Fin 2)
    (subdivision : Subdivision segment within left leftInside
      (SquareRootContinuationChain.Owner.independent
        (segment.pointAt_eval_ne_zero left leftInside) sheet)) :
    SquareRootContinuationChain.SeededChain
      (polynomial.eval (segment.pointAt left))
      (segment.pointAt_eval_ne_zero left leftInside) where
  sheet := sheet
  continuation := subdivision.toChain

end Subdivision

end Purelib.Riemann.Branches.ClearSheetContinuation
