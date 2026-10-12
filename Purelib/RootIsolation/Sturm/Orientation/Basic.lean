module
import Purelib.Data.Rat.Bounds.Square
public import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Bounds.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Sign.Products
import Purelib.Geometry.Rational.Box.Interval
import Purelib.Polynomial.Clearance.Pair.Basic
public import Purelib.Polynomial.Clearance.Pair.Bezout
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
public import Purelib.Polynomial.Dense.Rational.Bounds.Taylor

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Interval (Bounds)
open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)
open Purelib.Polynomial.Dense.Rational.Bezout.Basic (CoprimeCertificate)

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

namespace Purelib.RootIsolation.Sturm.Orientation.Basic

/-- Construct a uniform polynomial/derivative clearance from a displayed squarefree Bézout certificate.

The certificate retains the original rational interval and a positive lower bound for the sum of the two squared
evaluations. -/
@[expose] def orientationClearance
    (p : CoordinatePolynomial)
    (squarefree : CoprimeCertificate p
      (Dense.Derivative.derivative p))
    (root : Bounds) : Clearance.Pair.Basic.Certificate
      p (Dense.Derivative.derivative p) root :=
  Clearance.Pair.Bezout.certificateOfCoprime squarefree root

/-- Add the Taylor remainder coefficient and derivative squared-Lipschitz coefficient on a fixed interval.

This sum bounds the two errors used to retain the orientation of a displayed squarefree root. -/
@[expose] def orientationCoefficient
    (p : CoordinatePolynomial) (root : Bounds) :
      Fraction.Rational :=
  Dense.Rational.Bounds.Taylor.taylorRemainderBound p root +
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound
      (Dense.Derivative.derivative p) root

/-- The combined Taylor and derivative-displacement coefficient is nonnegative. -/
theorem orientationCoefficient_nonneg
    (p : CoordinatePolynomial) (root : Bounds) :
    0 ≤ orientationCoefficient p root :=
  add_nonneg (Dense.Rational.Bounds.Taylor.taylorRemainderBound_pos p root).le
    (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg
      (Dense.Derivative.derivative p) root).2

/-- A positive coefficient-computed width at which both the Taylor error and
the derivative displacement are below the squarefree Bézout clearance.

The minimum retains the unit width and the ratio of the positive clearance to the nonnegative error coefficient plus
one. -/
@[expose] def rootOrientationWidth
    (p : CoordinatePolynomial)
    (squarefree : CoprimeCertificate p
      (Dense.Derivative.derivative p))
    (root : Bounds) : Fraction.Rational :=
  min 1 ((orientationClearance p squarefree root).bound /
    (orientationCoefficient p root + 1))

/-- The squarefree orientation width is strictly positive.

The positive clearance is divided by a strictly positive coefficient offset, and then bounded by one. -/
theorem rootOrientationWidth_pos
    (p : CoordinatePolynomial)
    (squarefree : CoprimeCertificate p
      (Dense.Derivative.derivative p))
    (root : Bounds) :
    0 < rootOrientationWidth p squarefree root := by
  apply Fraction.Order.Basic.lt_min (by decide)
  exact Fraction.Order.Field.div_pos_direct
    (orientationClearance p squarefree root).positive
    (by
      calc
        0 < 1 := by decide
        _ ≤ orientationCoefficient p root + 1 :=
          add_le_add (orientationCoefficient_nonneg p root) (le_refl 1))

/-- The root-orientation width pays simultaneously for the coordinate
Taylor remainder and for moving the derivative from the root to either
endpoint.

A proper cell narrower than the retained orientation width pays both error coefficients against the same positive
clearance. -/
theorem orientation_scaled_width_sq_lt
    (p : CoordinatePolynomial)
    (squarefree : CoprimeCertificate p
      (Dense.Derivative.derivative p))
    (root interval : Bounds)
    (proper : interval.lower < interval.upper)
    (widthSmall : interval.upper - interval.lower <
      rootOrientationWidth p squarefree root) :
    Dense.Rational.Bounds.Taylor.taylorRemainderBound p root *
          (interval.upper - interval.lower) ^ 2 <
        (orientationClearance p squarefree root).bound ∧
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound
          (Dense.Derivative.derivative p) root *
            (interval.upper - interval.lower) ^ 2 <
        (orientationClearance p squarefree root).bound := by
  let width := interval.upper - interval.lower
  let coefficient := orientationCoefficient p root
  let bound := (orientationClearance p squarefree root).bound
  have widthPositive : 0 < width :=
    Fraction.Order.Arithmetic.sub_pos_direct proper
  have widthBelowOne : width < 1 :=
    widthSmall.trans_le (Fraction.Order.Basic.min_le_left _ _)
  have widthBelowRatio : width < bound / (coefficient + 1) :=
    widthSmall.trans_le (Fraction.Order.Basic.min_le_right _ _)
  have widthSqBelowWidth : width ^ 2 < width := by
    have multiplied :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        widthBelowOne widthPositive
    rw [pow_two]
    exact multiplied.trans_eq (Fraction.Field.one_mul width)
  have coefficientNonnegative : 0 ≤ coefficient := by
    simpa only [coefficient] using orientationCoefficient_nonneg p root
  have coefficientWidthBelow : coefficient * width < bound :=
    Data.Rat.Bounds.Scale.coefficient_mul_lt_of_radius_lt_div_add_one
        coefficientNonnegative widthPositive.le widthBelowRatio
  have coefficientWidthSqBelow : coefficient * width ^ 2 < bound :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      widthSqBelowWidth.le coefficientNonnegative).trans_lt
        coefficientWidthBelow
  have taylorNonnegative : 0 ≤ Dense.Rational.Bounds.Taylor.taylorRemainderBound p root :=
    (Dense.Rational.Bounds.Taylor.taylorRemainderBound_pos p root).le
  have derivativeCoefficientNonnegative :
      0 ≤ Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound
        (Dense.Derivative.derivative p) root :=
    (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg
      (Dense.Derivative.derivative p) root).2
  have widthSqNonnegative : 0 ≤ width ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct width
  constructor
  · exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (show Dense.Rational.Bounds.Taylor.taylorRemainderBound p root ≤ coefficient by
        dsimp only [coefficient, orientationCoefficient]
        exact le_add_of_nonneg_right derivativeCoefficientNonnegative)
      widthSqNonnegative).trans_lt coefficientWidthSqBelow
  · exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (show Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound
          (Dense.Derivative.derivative p) root ≤ coefficient by
        dsimp only [coefficient, orientationCoefficient]
        exact le_add_of_nonneg_left taylorNonnegative)
      widthSqNonnegative).trans_lt coefficientWidthSqBelow

/-- At a displayed squarefree root, the finite Taylor linear term has the
same strict sign as every distinct point evaluation in the sufficiently
small cell.

The displayed root and each distinct point lie in the same proper refining cell, whose width controls the Taylor error.
-/
theorem eval_mul_root_linear_pos
    (p : CoordinatePolynomial)
    (squarefree : CoprimeCertificate p
      (Dense.Derivative.derivative p))
    {root interval : Bounds}
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (widthSmall : interval.upper - interval.lower <
      rootOrientationWidth p squarefree root)
    {parameter point : Fraction.Rational}
    (parameterInside : interval.Contains parameter)
    (pointInside : interval.Contains point)
    (rootZero : p.eval parameter = 0) (different : point ≠ parameter) :
    0 < p.eval point *
      ((Dense.Derivative.derivative p).eval parameter *
        (point - parameter)) := open Purelib.Geometry.Rational in by
  let derivativeValue :=
    (Dense.Derivative.derivative p).eval parameter
  let distance := point - parameter
  let width := interval.upper - interval.lower
  let clearance := orientationClearance p squarefree root
  let taylor := Dense.Rational.Bounds.Taylor.taylorRemainderBound p root
  let error := p.eval point - p.eval parameter - derivativeValue * distance
  have parameterRoot : root.Contains parameter :=
    ⟨refines.1.trans parameterInside.1,
      parameterInside.2.trans refines.2⟩
  have pointRoot : root.Contains point :=
    ⟨refines.1.trans pointInside.1, pointInside.2.trans refines.2⟩
  have derivativeLower : clearance.bound ≤ derivativeValue ^ 2 := by
    have lower := clearance.lower parameter parameterRoot
    dsimp only [clearance, orientationClearance, derivativeValue] at lower ⊢
    rw [rootZero] at lower
    have zeroSq : (0 : Fraction.Rational) ^ 2 = 0 := by ring1
    rw [zeroSq, Fraction.Field.zero_add] at lower
    exact lower
  have distanceNonzero : distance ≠ 0 := by
    intro distanceZero
    change point - parameter = 0 at distanceZero
    apply different
    calc
      point = (point - parameter) + parameter := by ring1
      _ = parameter := by rw [distanceZero]; ring1
  have distanceSqPositive : 0 < distance ^ 2 := by
    exact Fraction.Order.Arithmetic.exact_rational_sq_pos distanceNonzero
  have distanceSqLeWidthSq : distance ^ 2 ≤ width ^ 2 := by
    simpa only [distance, width] using
      Box.Interval.point_sub_center_sq_le_width_sq pointInside parameterInside
  have scaledBounds := orientation_scaled_width_sq_lt p squarefree
    root interval proper widthSmall
  have taylorDistanceBelowDerivative :
      taylor * distance ^ 2 < derivativeValue ^ 2 := by
    calc
      taylor * distance ^ 2 ≤ taylor * width ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          distanceSqLeWidthSq (Dense.Rational.Bounds.Taylor.taylorRemainderBound_pos p root).le
      _ < clearance.bound := by
        simpa only [taylor, width, clearance] using scaledBounds.1
      _ ≤ derivativeValue ^ 2 := derivativeLower
  have errorBound : error ^ 2 ≤ taylor * distance ^ 4 := by
    simpa only [error, taylor, derivativeValue, distance] using
      Dense.Rational.Bounds.Taylor.taylor_error_sq_le p pointRoot parameterRoot
  have errorStrict : error ^ 2 < (derivativeValue * distance) ^ 2 := by
    calc
      error ^ 2 ≤ taylor * distance ^ 4 := errorBound
      _ = (taylor * distance ^ 2) * distance ^ 2 := by ring1
      _ < derivativeValue ^ 2 * distance ^ 2 :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
          taylorDistanceBelowDerivative distanceSqPositive
      _ = (derivativeValue * distance) ^ 2 := by ring1
  have perturbation :=
    Data.Rat.Sign.Products.sub_mul_neg_of_sq_lt_sq
      (a := error) (b := -(derivativeValue * distance)) (by
        have negativeSquare : (-(derivativeValue * distance)) ^ 2 =
            (derivativeValue * distance) ^ 2 := by ring1
        rw [negativeSquare]
        exact errorStrict)
  have errorShift : error - -(derivativeValue * distance) = p.eval point := by
    dsimp only [error, derivativeValue, distance]
    rw [rootZero]
    ring1
  rw [errorShift] at perturbation
  have positiveNegation :
      0 < -(p.eval point * -(derivativeValue * distance)) :=
    by
      have reversed := Fraction.Order.Arithmetic.neg_lt_neg_direct perturbation
      have zeroNegation : -(0 : Fraction.Rational) = 0 := by ring1
      rw [zeroNegation] at reversed
      exact reversed
  simpa only [derivativeValue, distance] using (calc
    0 < -(p.eval point * -(derivativeValue * distance)) := positiveNegation
    _ = p.eval point * (derivativeValue * distance) := by ring1)

/-- The automatic derivative at every point of the small cell has the same
strict sign as its value at the displayed squarefree root. -/
theorem derivative_eval_mul_root_derivative_pos
    (p : CoordinatePolynomial)
    (squarefree : CoprimeCertificate p
      (Dense.Derivative.derivative p))
    {root interval : Bounds}
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (widthSmall : interval.upper - interval.lower <
      rootOrientationWidth p squarefree root)
    {parameter point : Fraction.Rational}
    (parameterInside : interval.Contains parameter)
    (pointInside : interval.Contains point)
    (rootZero : p.eval parameter = 0) :
    0 < (Dense.Derivative.derivative p).eval point *
      (Dense.Derivative.derivative p).eval parameter := open Purelib.Geometry.Rational in by
  let derivative := Dense.Derivative.derivative p
  let derivativeValue := derivative.eval parameter
  let width := interval.upper - interval.lower
  let clearance := orientationClearance p squarefree root
  let lipschitz :=
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound derivative root
  have parameterRoot : root.Contains parameter :=
    ⟨refines.1.trans parameterInside.1,
      parameterInside.2.trans refines.2⟩
  have pointRoot : root.Contains point :=
    ⟨refines.1.trans pointInside.1, pointInside.2.trans refines.2⟩
  have derivativeLower : clearance.bound ≤ derivativeValue ^ 2 := by
    have lower := clearance.lower parameter parameterRoot
    dsimp only [clearance, orientationClearance, derivativeValue, derivative]
      at lower ⊢
    rw [rootZero] at lower
    have zeroSq : (0 : Fraction.Rational) ^ 2 = 0 := by ring1
    rw [zeroSq, Fraction.Field.zero_add] at lower
    exact lower
  have distanceSqLeWidthSq : (point - parameter) ^ 2 ≤ width ^ 2 := by
    simpa only [width] using
      Box.Interval.point_sub_center_sq_le_width_sq pointInside parameterInside
  have scaledBounds := orientation_scaled_width_sq_lt p squarefree
    root interval proper widthSmall
  have displacement := Dense.Rational.Bounds.Lipschitz.eval_sub_sq_le
    derivative root pointRoot parameterRoot
  have displacementStrict :
      (derivative.eval point - derivativeValue) ^ 2 <
        derivativeValue ^ 2 := by
    calc
      (derivative.eval point - derivativeValue) ^ 2 ≤
          lipschitz * (point - parameter) ^ 2 := by
        simpa only [derivativeValue, lipschitz] using displacement
      _ ≤ lipschitz * width ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          distanceSqLeWidthSq
          (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg
            derivative root).2
      _ < clearance.bound := by
        simpa only [derivative, lipschitz, width, clearance] using
          scaledBounds.2
      _ ≤ derivativeValue ^ 2 := derivativeLower
  simpa only [derivative, derivativeValue] using
    Data.Rat.Sign.Products.mul_pos_of_sub_sq_lt_sq
      displacementStrict

/-- Endpoint orientation supplied by one displayed squarefree root.  A root
at a cell endpoint contributes a half-event; otherwise the lower endpoint is
opposite to its derivative and the upper endpoint is aligned with it.

Each endpoint retains either equality with the displayed root or the corresponding strict polynomial and derivative sign
relation. -/
structure RootEndpointOrientation
    (p : CoordinatePolynomial) (interval : Bounds)
    (parameter : Fraction.Rational) where
  /-- The lower endpoint is the root, or its polynomial and derivative evaluations have opposite strict signs. -/ lower
    : interval.lower = parameter ∨
    p.eval interval.lower *
      (Dense.Derivative.derivative p).eval interval.lower < 0
  /-- The upper endpoint is the root, or its polynomial and derivative evaluations have the same strict sign. -/ upper :
    interval.upper = parameter ∨
    0 < p.eval interval.upper *
      (Dense.Derivative.derivative p).eval interval.upper

/-- Orient both endpoints of a sufficiently narrow cell around a displayed squarefree root.

An endpoint equal to the root is retained explicitly; otherwise the polynomial and derivative have opposite signs at the
lower endpoint and equal signs at the upper endpoint. -/
theorem rootEndpointOrientation
    (p : CoordinatePolynomial)
    (squarefree : CoprimeCertificate p
      (Dense.Derivative.derivative p))
    {root interval : Bounds}
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (widthSmall : interval.upper - interval.lower <
      rootOrientationWidth p squarefree root)
    (parameter : Fraction.Rational) (parameterInside : interval.Contains parameter)
    (rootZero : p.eval parameter = 0) :
    RootEndpointOrientation p interval parameter := by
  let derivativeValue :=
    (Dense.Derivative.derivative p).eval parameter
  have lower : interval.lower = parameter ∨
      p.eval interval.lower *
        (Dense.Derivative.derivative p).eval interval.lower < 0 := by
    by_cases lowerRoot : interval.lower = parameter
    · exact Or.inl lowerRoot
    · right
      have lowerLinear := eval_mul_root_linear_pos p squarefree refines
        proper widthSmall parameterInside
          ⟨le_rfl, interval.valid⟩ rootZero lowerRoot
      have lowerSame := derivative_eval_mul_root_derivative_pos p squarefree
        refines proper widthSmall parameterInside
          ⟨le_rfl, interval.valid⟩ rootZero
      have lowerLt : interval.lower < parameter :=
        lt_of_le_of_ne parameterInside.1 lowerRoot
      have differenceNegative : interval.lower - parameter < 0 :=
        Fraction.Order.Arithmetic.sub_neg_direct lowerLt
      have factored : 0 <
          (p.eval interval.lower * derivativeValue) *
            (interval.lower - parameter) := by
        simpa only [derivativeValue] using (calc
          0 < p.eval interval.lower *
              (derivativeValue * (interval.lower - parameter)) := lowerLinear
          _ = (p.eval interval.lower * derivativeValue) *
              (interval.lower - parameter) := by ring1)
      have lowerOpposite : p.eval interval.lower * derivativeValue < 0 := by
        rcases lt_trichotomy
            (p.eval interval.lower * derivativeValue) 0 with
            productNegative | productZero | productPositive
        · exact productNegative
        · rw [productZero, Fraction.Field.zero_mul_direct] at factored
          exact (lt_irrefl 0 factored).elim
        · have productNegative :=
            Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct
              productPositive differenceNegative
          exact (lt_asymm factored productNegative).elim
      exact Purelib.Data.Rat.Sign.Products.product_neg_of_opposite_and_same lowerOpposite lowerSame
  have upper : interval.upper = parameter ∨
      0 < p.eval interval.upper *
        (Dense.Derivative.derivative p).eval interval.upper := by
    by_cases upperRoot : interval.upper = parameter
    · exact Or.inl upperRoot
    · right
      have upperLinear := eval_mul_root_linear_pos p squarefree refines
        proper widthSmall parameterInside
          ⟨interval.valid, le_rfl⟩ rootZero upperRoot
      have upperSame := derivative_eval_mul_root_derivative_pos p squarefree
        refines proper widthSmall parameterInside
          ⟨interval.valid, le_rfl⟩ rootZero
      have parameterLt : parameter < interval.upper :=
        lt_of_le_of_ne parameterInside.2 (Ne.symm upperRoot)
      have differencePositive : 0 < interval.upper - parameter :=
        Fraction.Order.Arithmetic.sub_pos_direct parameterLt
      have factored : 0 <
          (p.eval interval.upper * derivativeValue) *
            (interval.upper - parameter) := by
        simpa only [derivativeValue] using (calc
          0 < p.eval interval.upper *
              (derivativeValue * (interval.upper - parameter)) := upperLinear
          _ = (p.eval interval.upper * derivativeValue) *
              (interval.upper - parameter) := by ring1)
      have upperAligned : 0 < p.eval interval.upper * derivativeValue := by
        exact Fraction.Order.Arithmetic.pos_of_mul_pos_right_direct
          (left := interval.upper - parameter)
          (by simpa only [Fraction.Field.mul_comm] using factored)
          differencePositive.le
      exact Purelib.Data.Rat.Sign.Products.product_pos_of_two_same upperAligned upperSame
  exact ⟨lower, upper⟩
end Purelib.RootIsolation.Sturm.Orientation.Basic

end
