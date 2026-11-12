module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.Fin.Two
import Purelib.Data.Fin.Cases
public import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Interval.ConvexCombination
public import Purelib.Data.Rat.Interval.Gap
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Progressive.Braid.Projected.Frame
public import Purelib.RootIsolation.Progressive.Braid.Projected.Overlap
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap

import Purelib.Data.Rat.Fraction.Compatibility
meta import Purelib.Elab.Deriving.Repr
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Topology.Knot.Braid.Event
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Fin

open Purelib.Data.Fin.Bijection.Basic

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.RootIsolation.Owner

open Purelib.RootIsolation.Progressive.Braid.Projected

open Purelib.RootIsolation.Progressive.Braid.Projected.Overlap

open Purelib.RootIsolation.Progressive.Chamber

open Purelib.Topology.Knot

public section

/-!
# Certified finite paths in the Legendre parameter plane

The Legendre family is represented by the exact dense polynomial
`x * (x - 1) * (x - lambda)`.  Axis-aligned parameter segments carry finite
rational clearances from the singular parameters zero and one.  A certified
segment then adds the existing simple-root chamber overlap, an extracted
three-strand braid word, and a common lower bound for all bridge clearances.
-/

namespace Purelib.Curves.Legendre.Paths

open Purelib.Data.Gaussian

open Purelib.Topology.Knot.Braid
open Purelib.Data.Gaussian.Coordinates

/-- Exact rational coordinates in the Legendre parameter plane. -/
abbrev Coordinate := Fraction.Rational
/-- Exact Gaussian rational parameter values. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- Executable dense Gaussian polynomials for the Legendre family. -/
abbrev GaussianPolynomial := Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- A certified finite frame of isolated simple polynomial roots. -/
abbrev ChamberFrame := Frame.ChamberFrame
/-- A certified matching and bridge family between two root frames. -/
abbrev ChamberOverlap := Overlap.ChamberOverlap
/-- An executable finite bijection with inverse laws. -/
abbrev Bijection := Data.Fin.Bijection
/-- A root frame with a certified left-to-right projection order. -/
abbrev ProjectedFrame := Frame.ProjectedFrame
/-- An atomic projected overlap between the two retained ordered root frames. -/
abbrev ProjectedOverlap {strands : Nat}
    (start finish : ProjectedFrame strands) :=
  Overlap.ProjectedOverlap start finish

/-- Construct an exact parameter value from its real and imaginary coordinates. -/
@[expose] def gaussian (real imaginary : Coordinate) : Gaussian :=
  ⟨real, imaginary⟩

/-- Exact high-to-low coefficient representation of `x * (x - 1) * (x - lambda)`. -/
@[expose] def polynomial (lambda : Gaussian) : GaussianPolynomial :=
  ⟨[1, -(1 + lambda), lambda, 0]⟩

/-- The displayed Legendre polynomial is nonzero for every parameter. -/
@[simp] theorem polynomial_isZero (lambda : Gaussian) :
    (polynomial lambda).isZero = false := rfl

/-- The displayed Legendre polynomial has degree three. -/
@[simp] theorem polynomial_natDegree (lambda : Gaussian) :
    (polynomial lambda).natDegree = 3 := rfl

/-- The coefficient representation evaluates to x times x minus one times x minus lambda. -/
theorem polynomial_eval (lambda point : Gaussian) :
    (polynomial lambda).eval point =
      point * (point - 1) * (point - lambda) := by
  unfold polynomial DensePolynomial.eval
    DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- Zero is a root of the displayed Legendre polynomial. -/
@[simp] theorem polynomial_zero (lambda : Gaussian) :
    (polynomial lambda).eval 0 = 0 := by
  rw [polynomial_eval]
  ring1

/-- One is a root of the displayed Legendre polynomial. -/
@[simp] theorem polynomial_one (lambda : Gaussian) :
    (polynomial lambda).eval 1 = 0 := by
  rw [polynomial_eval]
  ring1

/-- The parameter itself is a root of the displayed Legendre polynomial. -/
@[simp] theorem polynomial_lambda (lambda : Gaussian) :
    (polynomial lambda).eval lambda = 0 := by
  rw [polynomial_eval]
  ring1

/-- Logical order of the finite branch points. At a real base parameter between zero and one this is their geometric
order `0, lambda, 1`. -/
@[expose] def branchPoint (lambda : Gaussian) (label : Fin 3) : Gaussian :=
  if label = 0 then 0 else if label = 1 then lambda else 1

/-- Logical branch label zero denotes the root zero. -/
@[simp] theorem branchPoint_zero (lambda : Gaussian) :
    branchPoint lambda 0 = 0 := rfl

/-- Logical branch label one denotes the parameter root. -/
@[simp] theorem branchPoint_one (lambda : Gaussian) :
    branchPoint lambda 1 = lambda := rfl

/-- Logical branch label two denotes the root one. -/
@[simp] theorem branchPoint_two (lambda : Gaussian) :
    branchPoint lambda 2 = 1 := rfl

/-- Select one of three rational rotation slopes for the displayed Legendre branch points.

Slope zero preserves an already separated real projection. The two remaining
directions resolve ties with zero or one, including the cases where slope one
would produce a new tie with the other fixed branch point. -/
@[expose] def projectionSlope (lambda : Gaussian) : Coordinate :=
  if lambda.re = 0 then
    if lambda.im = 1 then 2 else 1
  else if lambda.re = 1 then
    if lambda.im = -1 then 2 else 1
  else 0

/-- Intrinsic regularity makes the computed parameter projection distinct from both fixed branch projections. -/
theorem projectionSlope_separates (lambda : Gaussian) (nonzero : lambda ≠ 0) (notOne : lambda ≠ 1) :
    lambda.re + projectionSlope lambda * lambda.im ≠ 0 ∧
      lambda.re + projectionSlope lambda * lambda.im ≠ 1 := by
  by_cases realZero : lambda.re = 0
  · have imaginaryNonzero : lambda.im ≠ 0 := by
      intro imaginaryZero
      exact nonzero (Data.Gaussian.Basic.ext realZero imaginaryZero)
    by_cases imaginaryOne : lambda.im = 1
    · rewrite [projectionSlope, if_pos realZero, if_pos imaginaryOne, realZero, imaginaryOne]
      constructor <;> decide
    · rewrite [projectionSlope, if_pos realZero, if_neg imaginaryOne, realZero,
        Fraction.Field.one_mul, Fraction.Field.zero_add]
      exact ⟨imaginaryNonzero, imaginaryOne⟩
  · by_cases realOne : lambda.re = 1
    · have imaginaryNonzero : lambda.im ≠ 0 := by
        intro imaginaryZero
        exact notOne (Data.Gaussian.Basic.ext realOne imaginaryZero)
      by_cases imaginaryNegativeOne : lambda.im = -1
      · rewrite [projectionSlope, if_neg realZero, if_pos realOne, if_pos imaginaryNegativeOne,
          realOne, imaginaryNegativeOne]
        constructor <;> decide
      · rewrite [projectionSlope, if_neg realZero, if_pos realOne, if_neg imaginaryNegativeOne,
          realOne, Fraction.Field.one_mul]
        constructor
        · intro zero
          apply imaginaryNegativeOne
          calc
            lambda.im = (1 + lambda.im) - 1 := by ring1
            _ = 0 - 1 := congrArg (fun value : Coordinate => value - 1) zero
            _ = -1 := by ring1
        · intro one
          apply imaginaryNonzero
          calc
            lambda.im = (1 + lambda.im) - 1 := by ring1
            _ = 1 - 1 := congrArg (fun value : Coordinate => value - 1) one
            _ = 0 := by ring1
    · rewrite [projectionSlope, if_neg realZero, if_neg realOne, Fraction.Field.zero_mul_direct,
        show lambda.re + 0 = lambda.re by ring1]
      exact ⟨realZero, realOne⟩

/-- Read one original branch point in a retained rational projection chart.

The default direction is computed from the parameter. A supplied shared
direction reads the same original logical branch point. -/
@[expose] def branchProjection (lambda : Gaussian) (label : Fin 3)
    (slope : Coordinate := projectionSlope lambda) : Gaussian :=
  Rotation.rotate slope (branchPoint lambda label)

/-- Distinct branch labels have distinct real projections in one retained separating chart.

The three exact original branch points are rotated by one shared direction.
The two excluded parameter readings ensure separation from zero and one
in that same chart; logical labels and their original points remain fixed. -/
theorem branchProjection_real_distinct_of_separation (lambda : Gaussian) (slope : Coordinate)
    (parameterSeparated : lambda.re + slope * lambda.im ≠ 0 ∧
      lambda.re + slope * lambda.im ≠ 1)
    (left right : Fin 3) (different : left ≠ right) :
    (branchProjection lambda left slope).re ≠ (branchProjection lambda right slope).re := by
  have zeroProjection : (branchProjection lambda 0 slope).re = 0 := by
    rewrite [branchProjection, branchPoint_zero, Rotation.rotate_real]
    change 0 + slope * 0 = 0
    ring1
  have oneProjection : (branchProjection lambda 2 slope).re = 1 := by
    rewrite [branchProjection, branchPoint_two, Rotation.rotate_real]
    change 1 + slope * 0 = 1
    ring1
  have parameterProjection : (branchProjection lambda 1 slope).re =
      lambda.re + slope * lambda.im := by
    rewrite [branchProjection, branchPoint_one, Rotation.rotate_real]
    rfl
  rcases Data.Fin.Cases.three left with leftZero | leftOne | leftTwo <;>
    subst left <;>
    rcases Data.Fin.Cases.three right with rightZero | rightOne | rightTwo <;>
    subst right
  · exact (different rfl).elim
  · rewrite [zeroProjection, parameterProjection]
    exact fun equal => parameterSeparated.1 equal.symm
  · rewrite [zeroProjection, oneProjection]
    decide
  · rewrite [parameterProjection, zeroProjection]
    exact parameterSeparated.1
  · exact (different rfl).elim
  · rewrite [parameterProjection, oneProjection]
    exact parameterSeparated.2
  · rewrite [oneProjection, zeroProjection]
    decide
  · rewrite [oneProjection, parameterProjection]
    exact fun equal => parameterSeparated.2 equal.symm
  · exact (different rfl).elim

/-- Intrinsic regularity separates every pair of branches in the automatically selected chart. -/
theorem branchProjection_real_distinct (lambda : Gaussian) (nonzero : lambda ≠ 0) (notOne : lambda ≠ 1)
    (left right : Fin 3) (different : left ≠ right) :
    (branchProjection lambda left).re ≠ (branchProjection lambda right).re :=
  branchProjection_real_distinct_of_separation lambda (projectionSlope lambda)
    (projectionSlope_separates lambda nonzero notOne) left right different

/-! ## Exact axis-aligned parameter geometry -/

/-- An exact horizontal or vertical segment indexed by its Gaussian endpoints. -/
inductive AxisSegment : Gaussian -> Gaussian -> Type
  /-- A horizontal segment with fixed imaginary coordinate. -/ | horizontal (xStart xFinish y :
    Coordinate) :
      AxisSegment (gaussian xStart y)
        (gaussian xFinish y)
  /-- A vertical segment with fixed real coordinate. -/ | vertical (x yStart yFinish : Coordinate)
    :
      AxisSegment (gaussian x yStart)
        (gaussian x yFinish)

namespace AxisSegment

open Purelib.Data.Rat.Fraction.Order

/-- Evaluate the affine parametrization of the retained axis segment. -/
@[expose] def pointAt {start finish : Gaussian}
    (segment : AxisSegment start finish) (parameter : Coordinate) : Gaussian
      :=
  match segment with
  | .horizontal xStart xFinish y =>
      gaussian (xStart + (xFinish - xStart) * parameter) y
  | .vertical x yStart yFinish =>
      gaussian x (yStart + (yFinish - yStart) * parameter)

/-- The axis-segment parametrization starts at its first endpoint. -/
@[simp] theorem pointAt_zero {start finish : Gaussian}
    (segment : AxisSegment start finish) : segment.pointAt 0 = start := by
  cases segment with
  | horizontal xStart xFinish y =>
      apply Data.Gaussian.Basic.ext
      · change xStart + (xFinish - xStart) * 0 = xStart
        ring1
      · rfl
  | vertical x yStart yFinish =>
      apply Data.Gaussian.Basic.ext
      · rfl
      · change yStart + (yFinish - yStart) * 0 = yStart
        ring1

/-- The axis-segment parametrization ends at its second endpoint. -/
@[simp] theorem pointAt_one {start finish : Gaussian}
    (segment : AxisSegment start finish) : segment.pointAt 1 = finish := by
  cases segment with
  | horizontal xStart xFinish y =>
      apply Data.Gaussian.Basic.ext
      · change xStart + (xFinish - xStart) * 1 = xFinish
        ring1
      · rfl
  | vertical x yStart yFinish =>
      apply Data.Gaussian.Basic.ext
      · rfl
      · change yStart + (yFinish - yStart) * 1 = yFinish
        ring1

/-- Reverse an axis segment by exchanging its endpoints and preserving its fixed coordinate. -/
@[expose] def reverse {start finish : Gaussian}
    (segment : AxisSegment start finish) : AxisSegment finish start :=
  match segment with
  | .horizontal xStart xFinish y => .horizontal xFinish xStart y
  | .vertical x yStart yFinish => .vertical x yFinish yStart

/-- Reversing an axis segment twice restores the exact segment. -/
@[simp] theorem reverse_reverse {start finish : Gaussian}
    (segment : AxisSegment start finish) : segment.reverse.reverse = segment := by
  cases segment <;> rfl

/-- Squared fixed-coordinate gap from an excluded point. It is independent of the segment parameter and hence certifies
the entire segment. -/
@[expose] def fixedGapSq {start finish : Gaussian}
    (segment : AxisSegment start finish) (excluded : Gaussian) : Coordinate
      :=
  match segment with
  | .horizontal _ _ y => (y - excluded.im) ^ 2
  | .vertical x _ _ => (x - excluded.re) ^ 2

/-- Segment reversal preserves its fixed-coordinate squared gap. -/
@[simp] theorem fixedGapSq_reverse {start finish : Gaussian}
    (segment : AxisSegment start finish) (excluded : Gaussian) :
    segment.reverse.fixedGapSq excluded = segment.fixedGapSq excluded := by
  cases segment <;> rfl

/-- Reversal evaluates the original axis segment at the complementary parameter. -/
theorem pointAt_reverse {start finish : Gaussian} (segment : AxisSegment start finish)
    (parameter : Coordinate) : segment.reverse.pointAt parameter = segment.pointAt (1 - parameter) := by
  cases segment with
  | horizontal xStart xFinish y =>
      apply Data.Gaussian.Basic.ext
      · change xFinish + (xStart - xFinish) * parameter =
          xStart + (xFinish - xStart) * (1 - parameter)
        ring1
      · rfl
  | vertical x yStart yFinish =>
      apply Data.Gaussian.Basic.ext
      · rfl
      · change yFinish + (yStart - yFinish) * parameter =
          yStart + (yFinish - yStart) * (1 - parameter)
        ring1

/-- The fixed-coordinate squared gap bounds every point of the whole affine line. -/
theorem fixedGapSq_normSq_lower {start finish : Gaussian} (segment : AxisSegment start finish)
    (excluded : Gaussian) (parameter : Coordinate) :
    segment.fixedGapSq excluded ≤ Norm.Basic.normSq (segment.pointAt parameter - excluded) := by
  cases segment with
  | horizontal xStart xFinish y =>
      change (y - excluded.im) ^ 2 ≤
        (xStart + (xFinish - xStart) * parameter - excluded.re) ^ 2 + (y - excluded.im) ^ 2
      exact le_add_of_nonneg_left
        (Arithmetic.sq_nonneg_direct
          (xStart + (xFinish - xStart) * parameter - excluded.re))
  | vertical x yStart yFinish =>
      change (x - excluded.re) ^ 2 ≤
        (x - excluded.re) ^ 2 + (yStart + (yFinish - yStart) * parameter - excluded.im) ^ 2
      exact le_add_of_nonneg_right
        (Arithmetic.sq_nonneg_direct
          (yStart + (yFinish - yStart) * parameter - excluded.im))

/-- Retain the ordered interval of endpoint displacements in the segment's varying coordinate.

The minimum and maximum preserve both orientations and stationary endpoints.
The excluded point supplies the corresponding real or imaginary coordinate. -/
@[expose] def movingBounds {start finish : Gaussian} (segment : AxisSegment start finish)
    (excluded : Gaussian) : Data.Rat.Interval.Bounds :=
  match segment with
  | .horizontal first last _ =>
      ⟨min (first - excluded.re) (last - excluded.re),
        max (first - excluded.re) (last - excluded.re),
        (Fraction.Order.Basic.min_le_left _ _).trans (Fraction.Order.Basic.le_max_left _ _)⟩
  | .vertical _ first last =>
      ⟨min (first - excluded.im) (last - excluded.im),
        max (first - excluded.im) (last - excluded.im),
        (Fraction.Order.Basic.min_le_left _ _).trans (Fraction.Order.Basic.le_max_left _ _)⟩

/-- Read the displacement from the excluded point in the segment's varying coordinate. -/
@[expose] def movingCoordinate {start finish : Gaussian} (segment : AxisSegment start finish)
    (excluded : Gaussian) (parameter : Coordinate) : Coordinate :=
  match segment with
  | .horizontal first last _ => first + (last - first) * parameter - excluded.re
  | .vertical _ first last => first + (last - first) * parameter - excluded.im

/-- Every unit-interval parameter gives a displacement in the retained endpoint interval. -/
theorem movingCoordinate_contains {start finish : Gaussian} (segment : AxisSegment start finish)
    (excluded : Gaussian) (parameter : Coordinate) (nonnegative : 0 ≤ parameter) (atMostOne : parameter ≤ 1) :
    (segment.movingBounds excluded).Contains (segment.movingCoordinate excluded parameter) := by
  cases segment with
  | horizontal first last y =>
      change min (first - excluded.re) (last - excluded.re) ≤
        first + (last - first) * parameter - excluded.re ∧
        first + (last - first) * parameter - excluded.re ≤
          max (first - excluded.re) (last - excluded.re)
      rewrite [show first + (last - first) * parameter - excluded.re =
        (first - excluded.re) + parameter * ((last - excluded.re) - (first - excluded.re)) by ring1]
      exact Geometry.Rational.Box.coordinate_between
        ⟨Fraction.Order.Basic.min_le_left _ _, Fraction.Order.Basic.le_max_left _ _⟩
        ⟨Fraction.Order.Basic.min_le_right _ _, Fraction.Order.Basic.le_max_right _ _⟩
        ⟨nonnegative, atMostOne⟩
  | vertical x first last =>
      change min (first - excluded.im) (last - excluded.im) ≤
        first + (last - first) * parameter - excluded.im ∧
        first + (last - first) * parameter - excluded.im ≤
          max (first - excluded.im) (last - excluded.im)
      rewrite [show first + (last - first) * parameter - excluded.im =
        (first - excluded.im) + parameter * ((last - excluded.im) - (first - excluded.im)) by ring1]
      exact Geometry.Rational.Box.coordinate_between
        ⟨Fraction.Order.Basic.min_le_left _ _, Fraction.Order.Basic.le_max_left _ _⟩
        ⟨Fraction.Order.Basic.min_le_right _ _, Fraction.Order.Basic.le_max_right _ _⟩
        ⟨nonnegative, atMostOne⟩

/-- Compute a squared-distance lower bound from the fixed coordinate and the varying interval gap. -/
@[expose] def clearanceSq {start finish : Gaussian} (segment : AxisSegment start finish)
    (excluded : Gaussian) : Coordinate :=
  segment.fixedGapSq excluded + Data.Rat.Interval.Gap.gap (segment.movingBounds excluded) ^ 2

/-- The computed segment squared clearance is nonnegative. -/
theorem clearanceSq_nonnegative {start finish : Gaussian} (segment : AxisSegment start finish)
    (excluded : Gaussian) : 0 ≤ segment.clearanceSq excluded := by
  have fixedNonnegative : 0 ≤ segment.fixedGapSq excluded := by
    cases segment <;> exact Arithmetic.sq_nonneg_direct _
  exact add_nonneg fixedNonnegative (Arithmetic.sq_nonneg_direct _)

/-- The fixed-coordinate gap is bounded by the computed whole-segment squared clearance. -/
theorem fixedGapSq_le_clearanceSq {start finish : Gaussian} (segment : AxisSegment start finish)
    (excluded : Gaussian) : segment.fixedGapSq excluded ≤ segment.clearanceSq excluded :=
  le_add_of_nonneg_right (Arithmetic.sq_nonneg_direct _)

/-- The computed squared clearance bounds distance at every parameter in the whole unit interval.

The varying coordinate stays in its retained endpoint interval, whose gap
bounds its square. The fixed coordinate contributes its unchanged square. -/
theorem clearanceSq_normSq_lower {start finish : Gaussian} (segment : AxisSegment start finish)
    (excluded : Gaussian) (parameter : Coordinate) (nonnegative : 0 ≤ parameter) (atMostOne : parameter ≤ 1) :
    segment.clearanceSq excluded ≤ Norm.Basic.normSq (segment.pointAt parameter - excluded) := by
  have gapLower := Data.Rat.Interval.Gap.gap_sq_le (segment.movingBounds excluded)
    (segment.movingCoordinate_contains excluded parameter nonnegative atMostOne)
  cases segment with
  | horizontal first last y =>
      change (y - excluded.im) ^ 2 +
        Data.Rat.Interval.Gap.gap ((AxisSegment.horizontal first last y).movingBounds excluded) ^ 2 ≤
          (first + (last - first) * parameter - excluded.re) ^ 2 + (y - excluded.im) ^ 2
      calc
        _ ≤ (y - excluded.im) ^ 2 + (first + (last - first) * parameter - excluded.re) ^ 2 :=
          Arithmetic.add_le_add_direct le_rfl gapLower
        _ = _ := by ring1
  | vertical x first last =>
      exact Arithmetic.add_le_add_direct le_rfl gapLower

/-- Vanishing squared clearance makes both the fixed square and varying interval gap vanish. -/
private theorem clearanceSq_zero_parts {start finish : Gaussian} (segment : AxisSegment start finish)
    (excluded : Gaussian) (zero : segment.clearanceSq excluded = 0) :
    segment.fixedGapSq excluded = 0 ∧ Data.Rat.Interval.Gap.gap (segment.movingBounds excluded) = 0 := by
  have fixedNonnegative : 0 ≤ segment.fixedGapSq excluded := by
    cases segment <;> exact Arithmetic.sq_nonneg_direct _
  have movingNonnegative := Arithmetic.sq_nonneg_direct
    (Data.Rat.Interval.Gap.gap (segment.movingBounds excluded))
  have fixedUpper : segment.fixedGapSq excluded ≤ 0 :=
    (le_add_of_nonneg_right movingNonnegative).trans_eq zero
  have movingUpper : Data.Rat.Interval.Gap.gap (segment.movingBounds excluded) ^ 2 ≤ 0 :=
    (le_add_of_nonneg_left fixedNonnegative).trans_eq zero
  exact ⟨Fraction.Order.Basic.le_antisymm _ _ fixedUpper fixedNonnegative,
    (Arithmetic.sq_eq_zero_direct _).mp
      (Fraction.Order.Basic.le_antisymm _ _ movingUpper movingNonnegative)⟩

/-- Compute the affine parameter where the varying coordinate meets the excluded coordinate.

The endpoint displacements retain the original orientation. A stationary
varying coordinate yields zero; a collision guarantee additionally needs
vanishing computed squared clearance. -/
@[expose] def collisionParameter {start finish : Gaussian} (segment : AxisSegment start finish)
    (excluded : Gaussian) : Coordinate :=
  match segment with
  | .horizontal first last _ =>
      Interval.ConvexCombination.segmentParameter (first - excluded.re) (last - excluded.re) 0
  | .vertical _ first last =>
      Interval.ConvexCombination.segmentParameter (first - excluded.im) (last - excluded.im) 0

/-- Zero computed squared clearance places the collision parameter in the closed unit interval. -/
theorem collisionParameter_bounds {start finish : Gaussian} (segment : AxisSegment start finish)
    (excluded : Gaussian) (zero : segment.clearanceSq excluded = 0) :
    0 ≤ segment.collisionParameter excluded ∧ segment.collisionParameter excluded ≤ 1 := by
  have parts := segment.clearanceSq_zero_parts excluded zero
  have inside := (Data.Rat.Interval.Gap.gap_eq_zero_iff (segment.movingBounds excluded)).mp parts.2
  cases segment with
  | horizontal first last y =>
      exact Interval.ConvexCombination.segmentParameter_bounds
        (first - excluded.re) (last - excluded.re) 0 inside
  | vertical x first last =>
      exact Interval.ConvexCombination.segmentParameter_bounds
        (first - excluded.im) (last - excluded.im) 0 inside

/-- Zero computed squared clearance makes the retained collision parameter hit the excluded point.

The varying coordinate is reconstructed from its exact affine inverse. The
zero fixed-coordinate square identifies the remaining coordinate directly. -/
theorem collisionParameter_hits {start finish : Gaussian} (segment : AxisSegment start finish)
    (excluded : Gaussian) (zero : segment.clearanceSq excluded = 0) :
    segment.pointAt (segment.collisionParameter excluded) = excluded := by
  have parts := segment.clearanceSq_zero_parts excluded zero
  have inside := (Data.Rat.Interval.Gap.gap_eq_zero_iff (segment.movingBounds excluded)).mp parts.2
  cases segment with
  | horizontal first last y =>
      have reconstructed := Interval.ConvexCombination.segmentParameter_interpolates
        (first - excluded.re) (last - excluded.re) 0 inside
      have fixedZero := (Arithmetic.sq_eq_zero_direct (y - excluded.im)).mp parts.1
      apply Data.Gaussian.Basic.ext
      · change first + (last - first) *
          Interval.ConvexCombination.segmentParameter (first - excluded.re) (last - excluded.re) 0 =
            excluded.re
        calc
          _ = ((first - excluded.re) +
              Interval.ConvexCombination.segmentParameter (first - excluded.re) (last - excluded.re) 0 *
                ((last - excluded.re) - (first - excluded.re))) + excluded.re := by ring1
          _ = 0 + excluded.re := congrArg (fun value => value + excluded.re) reconstructed
          _ = excluded.re := by ring1
      · change y = excluded.im
        calc
          y = (y - excluded.im) + excluded.im := by ring1
          _ = 0 + excluded.im := congrArg (fun value => value + excluded.im) fixedZero
          _ = excluded.im := by ring1
  | vertical x first last =>
      have reconstructed := Interval.ConvexCombination.segmentParameter_interpolates
        (first - excluded.im) (last - excluded.im) 0 inside
      have fixedZero := (Arithmetic.sq_eq_zero_direct (x - excluded.re)).mp parts.1
      apply Data.Gaussian.Basic.ext
      · change x = excluded.re
        calc
          x = (x - excluded.re) + excluded.re := by ring1
          _ = 0 + excluded.re := congrArg (fun value => value + excluded.re) fixedZero
          _ = excluded.re := by ring1
      · change first + (last - first) *
          Interval.ConvexCombination.segmentParameter (first - excluded.im) (last - excluded.im) 0 =
            excluded.im
        calc
          _ = ((first - excluded.im) +
              Interval.ConvexCombination.segmentParameter (first - excluded.im) (last - excluded.im) 0 *
                ((last - excluded.im) - (first - excluded.im))) + excluded.im := by ring1
          _ = 0 + excluded.im := congrArg (fun value => value + excluded.im) reconstructed
          _ = excluded.im := by ring1

/-- A retained unit-interval parameter at which the original axis segment hits an excluded point. -/
@[expose] def Collision {start finish : Gaussian} (segment : AxisSegment start finish) (excluded : Gaussian) : Type :=
  {parameter : Coordinate // 0 ≤ parameter ∧ parameter ≤ 1 ∧ segment.pointAt parameter = excluded}

namespace Collision

/-- Read the original exact collision parameter. -/
@[expose] def parameter {start finish : Gaussian} {segment : AxisSegment start finish} {excluded : Gaussian}
    (collision : Collision segment excluded) : Coordinate := collision.val

/-- The retained collision parameter is nonnegative. -/
theorem nonnegative {start finish : Gaussian} {segment : AxisSegment start finish} {excluded : Gaussian}
    (collision : Collision segment excluded) : 0 ≤ collision.parameter := collision.property.1

/-- The retained collision parameter is at most one. -/
theorem atMostOne {start finish : Gaussian} {segment : AxisSegment start finish} {excluded : Gaussian}
    (collision : Collision segment excluded) : collision.parameter ≤ 1 := collision.property.2.1

/-- Evaluation at the retained parameter hits the original excluded point. -/
theorem hits {start finish : Gaussian} {segment : AxisSegment start finish} {excluded : Gaussian}
    (collision : Collision segment excluded) : segment.pointAt collision.parameter = excluded :=
  collision.property.2.2

/-- Construct the explicit collision retained by a zero computed squared clearance. -/
@[expose] def ofZeroGap {start finish : Gaussian} (segment : AxisSegment start finish)
    (excluded : Gaussian) (zero : segment.clearanceSq excluded = 0) : Collision segment excluded :=
  ⟨segment.collisionParameter excluded,
    (segment.collisionParameter_bounds excluded zero).1,
    (segment.collisionParameter_bounds excluded zero).2,
    segment.collisionParameter_hits excluded zero⟩

end Collision

set_option genInjectivity false in
/-- A positive rational squared-distance bound valid on the whole closed unit segment.

The retained bound controls every unit-interval parameter, including endpoints
and stationary segments. A fixed-coordinate gap is one construction route. -/
structure Clearance {start finish : Gaussian}
    (segment : AxisSegment start finish) (excluded : Gaussian) where
  /-- The retained rational lower bound for squared distance from the excluded point. -/ bound :
    Coordinate
  /-- The retained squared clearance is strictly positive. -/ positive : 0 < bound
  /-- Every point of the closed unit segment satisfies the retained squared-distance lower bound. -/ lower :
    forall parameter : Coordinate, 0 ≤ parameter → parameter ≤ 1 →
      bound ≤ Norm.Basic.normSq (segment.pointAt parameter - excluded)

constructive_injectivity Clearance



/-- The retained clearance bounds squared distance at every unit-interval parameter. -/
theorem Clearance.normSq_lower {start finish : Gaussian}
    {segment : AxisSegment start finish} {excluded : Gaussian}
    (clearance : AxisSegment.Clearance segment excluded) (parameter :
      Coordinate) (nonnegative : 0 ≤ parameter) (atMostOne : parameter ≤ 1) :
    clearance.bound <=
      Norm.Basic.normSq
        (segment.pointAt parameter - excluded) := clearance.lower parameter nonnegative atMostOne

/-- Construct whole-segment clearance from a positive fixed-coordinate lower bound. -/
@[expose] def Clearance.ofFixedGap {start finish : Gaussian} (segment : AxisSegment start finish)
    (excluded : Gaussian) (bound : Coordinate) (positive : 0 < bound)
    (lower : bound ≤ segment.fixedGapSq excluded) : Clearance segment excluded where
  bound := bound
  positive := positive
  lower := fun parameter _ _ => lower.trans (segment.fixedGapSq_normSq_lower excluded parameter)

/-- Retain the computed interval-gap bound when it is positive. -/
@[expose] def Clearance.ofPositiveGap {start finish : Gaussian} (segment : AxisSegment start finish)
    (excluded : Gaussian) (positive : 0 < segment.clearanceSq excluded) : Clearance segment excluded where
  bound := segment.clearanceSq excluded
  positive := positive
  lower := segment.clearanceSq_normSq_lower excluded

/-- Every point of the closed unit segment differs from the specified excluded point. -/
@[expose] def Avoids {start finish : Gaussian} (segment : AxisSegment start finish) (excluded : Gaussian) : Prop :=
  ∀ parameter : Coordinate, 0 ≤ parameter → parameter ≤ 1 → segment.pointAt parameter ≠ excluded

/-- Positive clearance excludes a collision at every unit-interval parameter. -/
theorem Clearance.avoids {start finish : Gaussian} {segment : AxisSegment start finish} {excluded : Gaussian}
    (clearance : Clearance segment excluded) : segment.Avoids excluded := by
  intro parameter nonnegative atMostOne hits
  have lower := clearance.normSq_lower parameter nonnegative atMostOne
  rewrite [hits, Data.Gaussian.Basic.sub_self, Norm.Basic.normSq_zero] at lower
  exact clearance.positive.2 lower

/-- A retained collision contradicts intrinsic avoidance of the original excluded point. -/
theorem Collision.not_avoids {start finish : Gaussian} {segment : AxisSegment start finish} {excluded : Gaussian}
    (collision : Collision segment excluded) : ¬ segment.Avoids excluded :=
  fun avoids => avoids collision.parameter collision.nonnegative collision.atMostOne collision.hits

/-- Check the whole segment and retain either positive clearance or an exact collision.

The squared interval gap is computed once. Its zero branch retains an exact
unit parameter and evaluation identity; its positive branch retains that same
computed bound and the whole-interval distance law. -/
@[expose] def checkClearance {start finish : Gaussian} (segment : AxisSegment start finish)
    (excluded : Gaussian) : Sum (Clearance segment excluded) (Collision segment excluded) :=
  let bound := segment.clearanceSq excluded
  if zero : bound = 0 then
    .inr (Collision.ofZeroGap segment excluded zero)
  else
    .inl {
      bound := bound
      positive := ⟨segment.clearanceSq_nonnegative excluded,
        fun upper => zero (Fraction.Order.Basic.le_antisymm _ _ upper
          (segment.clearanceSq_nonnegative excluded))⟩
      lower := segment.clearanceSq_normSq_lower excluded }

/-- Construct positive quantitative clearance from intrinsic whole-segment avoidance.

The exact checker supplies its retained bound. An explicit collision is
excluded by the given mathematical avoidance condition, so no successful
search or numerical clearance is a caller input. -/
@[expose] def Clearance.ofAvoidance {start finish : Gaussian} (segment : AxisSegment start finish)
    (excluded : Gaussian) (avoids : segment.Avoids excluded) : Clearance segment excluded :=
  match segment.checkClearance excluded with
  | .inl clearance => clearance
  | .inr collision => False.elim (collision.not_avoids avoids)

/-- Preserve an excluded-point clearance when reversing its axis segment. -/
@[expose] def Clearance.reverse {start finish : Gaussian}
    {segment : AxisSegment start finish} {excluded : Gaussian}
    (clearance : Clearance segment excluded) :
    Clearance segment.reverse excluded where
  bound := clearance.bound
  positive := clearance.positive
  lower := by
    intro parameter nonnegative atMostOne
    rewrite [pointAt_reverse]
    apply clearance.lower
    · exact Arithmetic.sub_nonneg_direct atMostOne
    · calc
        1 - parameter ≤ 1 - 0 := Arithmetic.sub_le_sub_direct le_rfl nonnegative
        _ = 1 := by ring1

set_option genInjectivity false in
/-- The exact geometric portion of a Legendre segment. -/
structure Safe {start finish : Gaussian}
    (segment : AxisSegment start finish) where
  /-- The segment retains a positive squared clearance from the singular parameter zero. -/ avoidsZero :
    Clearance segment 0
  /-- The segment retains a positive squared clearance from the singular parameter one. -/ avoidsOne :
    Clearance segment 1

constructive_injectivity Safe

/-- Check both singular Legendre parameters on the whole retained segment.

A success retains both computed clearances. Invalidity identifies zero or one
and retains the exact unit parameter at which that singular value is reached. -/
@[expose] def checkSafety {start finish : Gaussian} (segment : AxisSegment start finish) :
    Sum (Safe segment) (Sum (Collision segment 0) (Collision segment 1)) :=
  match segment.checkClearance 0 with
  | .inr collision => .inr (.inl collision)
  | .inl zeroClearance =>
      match segment.checkClearance 1 with
      | .inr collision => .inr (.inr collision)
      | .inl oneClearance => .inl ⟨zeroClearance, oneClearance⟩

/-- Compute both singular-parameter clearances from intrinsic avoidance on the whole segment. -/
@[expose] def Safe.ofAvoidance {start finish : Gaussian} (segment : AxisSegment start finish)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) : Safe segment where
  avoidsZero := Clearance.ofAvoidance segment 0 avoidsZero
  avoidsOne := Clearance.ofAvoidance segment 1 avoidsOne




/-- Reverse both singular-parameter clearance certificates with their segment. -/
@[expose] def Safe.reverse {start finish : Gaussian}
    {segment : AxisSegment start finish} (safe : Safe segment) :
    Safe segment.reverse where
  avoidsZero := safe.avoidsZero.reverse
  avoidsOne := safe.avoidsOne.reverse

end AxisSegment

set_option genInjectivity false in
/-- A finite geometric path whose every segment carries exact avoidance of both singular parameters. -/
inductive SafePath : (start finish : Gaussian) -> Type
  /-- The empty geometric path at one exact parameter value. -/ | nil (point : Gaussian) :
    SafePath point point
  /-- Prepend an axis segment and its two clearances to a compatible safe path. -/ | cons {start middle finish :
    Gaussian}
      (segment : AxisSegment start middle)
      (safe : AxisSegment.Safe segment)
      (remaining : SafePath middle finish) : SafePath start
        finish

constructive_injectivity SafePath

namespace SafePath

/-- Count the finite segments of a geometrically safe path. -/
@[expose] def stepCount : {start finish : Gaussian} -> SafePath start finish
  -> Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ _ remaining => remaining.stepCount + 1

/-- Concatenate two safe paths at their common exact endpoint. -/
@[expose] def append {first middle last : Gaussian}
    (initial : SafePath first middle) (remaining : SafePath middle last) :
    SafePath first last :=
  match initial with
  | .nil _ => remaining
  | .cons segment safe tail => .cons segment safe (tail.append remaining)

/-- Reverse the segment order and every retained geometric clearance of a safe path. -/
@[expose] def reverse : {start finish : Gaussian} ->
    SafePath start finish -> SafePath finish start
  | _, _, .nil point => .nil point
  | start, _, .cons segment safe remaining =>
      remaining.reverse.append
        (.cons segment.reverse safe.reverse (.nil start))

end SafePath

/-! ## Executable rational rectangle examples -/

namespace RectangleExamples

/-- The rational coordinate one quarter. -/
@[expose] def quarter : Coordinate := 1 / 4
/-- The rational coordinate three quarters. -/
@[expose] def threeQuarters : Coordinate := 3 / 4
/-- The rational coordinate five quarters. -/
@[expose] def fiveQuarters : Coordinate := 5 / 4
/-- The rational coordinate minus one quarter. -/
@[expose] def negativeQuarter : Coordinate := -(1 / 4)
/-- The squared clearance constant one sixteenth. -/
@[expose] def sixteenth : Coordinate := 1 / 16

/-- The northeast vertex of the rational square of half-width one quarter centered at zero. -/
@[expose] def zeroNorthEast : Gaussian := gaussian quarter
  quarter
/-- The northwest vertex of the rational square of half-width one quarter centered at zero. -/
@[expose] def zeroNorthWest : Gaussian := gaussian
  negativeQuarter quarter
/-- The southwest vertex of the rational square of half-width one quarter centered at zero. -/
@[expose] def zeroSouthWest : Gaussian := gaussian
  negativeQuarter negativeQuarter
/-- The southeast vertex of the rational square of half-width one quarter centered at zero. -/
@[expose] def zeroSouthEast : Gaussian := gaussian quarter
  negativeQuarter

/-- The westward top segment of the square centered at zero. -/
@[expose] def zeroTop : AxisSegment zeroNorthEast
  zeroNorthWest :=
  .horizontal quarter negativeQuarter
    quarter

/-- The southward left segment of the square centered at zero. -/
@[expose] def zeroLeft : AxisSegment zeroNorthWest
  zeroSouthWest :=
  .vertical negativeQuarter quarter
    negativeQuarter

/-- The eastward bottom segment of the square centered at zero. -/
@[expose] def zeroBottom : AxisSegment zeroSouthWest
  zeroSouthEast :=
  .horizontal negativeQuarter quarter
    negativeQuarter

/-- The northward right segment of the square centered at zero. -/
@[expose] def zeroRight : AxisSegment zeroSouthEast
  zeroNorthEast :=
  .vertical quarter negativeQuarter
    quarter

/-- Build a segment clearance from a fixed-coordinate squared gap of at least one sixteenth. -/
@[expose] def clearanceSixteenth {start finish excluded : Gaussian}
    (segment : AxisSegment start finish)
    (lower : RectangleExamples.sixteenth <= segment.fixedGapSq excluded) :
    AxisSegment.Clearance segment excluded :=
  AxisSegment.Clearance.ofFixedGap segment excluded sixteenth (by decide) lower

/-- Exact one-sixteenth squared clearances from zero and one along the square's top segment centered at zero. -/
@[expose] def zeroTopSafe : AxisSegment.Safe zeroTop where
  avoidsZero := clearanceSixteenth
    zeroTop (by decide)
  avoidsOne := clearanceSixteenth
    zeroTop (by decide)

/-- Exact one-sixteenth squared clearances from zero and one along the square's left segment centered at zero. -/
@[expose] def zeroLeftSafe : AxisSegment.Safe zeroLeft
  where
  avoidsZero := clearanceSixteenth
    zeroLeft (by decide)
  avoidsOne := clearanceSixteenth
    zeroLeft (by decide)

/-- Exact one-sixteenth squared clearances from zero and one along the square's bottom segment centered at zero. -/
@[expose] def zeroBottomSafe : AxisSegment.Safe zeroBottom
  where
  avoidsZero := clearanceSixteenth
    zeroBottom (by decide)
  avoidsOne := clearanceSixteenth
    zeroBottom (by decide)

/-- Exact one-sixteenth squared clearances from zero and one along the square's right segment centered at zero. -/
@[expose] def zeroRightSafe : AxisSegment.Safe zeroRight
  where
  avoidsZero := clearanceSixteenth
    zeroRight (by decide)
  avoidsOne := clearanceSixteenth
    zeroRight (by decide)

/-- The four-segment counterclockwise square path centered at zero, with both singular-parameter clearances retained. -/
@[expose] def zeroRectangle : SafePath zeroNorthEast
  zeroNorthEast :=
  .cons zeroTop zeroTopSafe
    (.cons zeroLeft zeroLeftSafe
      (.cons zeroBottom zeroBottomSafe
        (.cons zeroRight zeroRightSafe
          (.nil zeroNorthEast))))

/-- The displayed square path centered at zero has four segments. -/
@[simp] theorem zeroRectangle_stepCount : RectangleExamples.zeroRectangle.stepCount = 4 := rfl

/-- The northeast vertex of the rational square of half-width one quarter centered at one. -/
@[expose] def oneNorthEast : Gaussian := gaussian
  fiveQuarters quarter
/-- The northwest vertex of the rational square of half-width one quarter centered at one. -/
@[expose] def oneNorthWest : Gaussian := gaussian
  threeQuarters quarter
/-- The southwest vertex of the rational square of half-width one quarter centered at one. -/
@[expose] def oneSouthWest : Gaussian := gaussian
  threeQuarters negativeQuarter
/-- The southeast vertex of the rational square of half-width one quarter centered at one. -/
@[expose] def oneSouthEast : Gaussian := gaussian
  fiveQuarters negativeQuarter

/-- The westward top segment of the square centered at one. -/
@[expose] def oneTop : AxisSegment oneNorthEast
  oneNorthWest :=
  .horizontal fiveQuarters threeQuarters
    quarter

/-- The southward left segment of the square centered at one. -/
@[expose] def oneLeft : AxisSegment oneNorthWest
  oneSouthWest :=
  .vertical threeQuarters quarter
    negativeQuarter

/-- The eastward bottom segment of the square centered at one. -/
@[expose] def oneBottom : AxisSegment oneSouthWest
  oneSouthEast :=
  .horizontal threeQuarters fiveQuarters
    negativeQuarter

/-- The northward right segment of the square centered at one. -/
@[expose] def oneRight : AxisSegment oneSouthEast
  oneNorthEast :=
  .vertical fiveQuarters negativeQuarter
    quarter

/-- Exact one-sixteenth squared clearances from zero and one along the square's top segment centered at one. -/
@[expose] def oneTopSafe : AxisSegment.Safe oneTop where
  avoidsZero := clearanceSixteenth
    oneTop (by decide)
  avoidsOne := clearanceSixteenth oneTop
    (by decide)

/-- Exact one-sixteenth squared clearances from zero and one along the square's left segment centered at one. -/
@[expose] def oneLeftSafe : AxisSegment.Safe oneLeft where
  avoidsZero := clearanceSixteenth
    oneLeft (by decide)
  avoidsOne := clearanceSixteenth
    oneLeft (by decide)

/-- Exact one-sixteenth squared clearances from zero and one along the square's bottom segment centered at one. -/
@[expose] def oneBottomSafe : AxisSegment.Safe oneBottom
  where
  avoidsZero := clearanceSixteenth
    oneBottom (by decide)
  avoidsOne := clearanceSixteenth
    oneBottom (by decide)

/-- Exact one-sixteenth squared clearances from zero and one along the square's right segment centered at one. -/
@[expose] def oneRightSafe : AxisSegment.Safe oneRight
  where
  avoidsZero := clearanceSixteenth
    oneRight (by decide)
  avoidsOne := clearanceSixteenth
    oneRight (by decide)

/-- The four-segment counterclockwise square path centered at one, with both singular-parameter clearances retained. -/
@[expose] def oneRectangle : SafePath oneNorthEast
  oneNorthEast :=
  .cons oneTop oneTopSafe
    (.cons oneLeft oneLeftSafe
      (.cons oneBottom oneBottomSafe
        (.cons oneRight oneRightSafe
          (.nil oneNorthEast))))

/-- The displayed square path centered at one has four segments. -/
@[simp] theorem oneRectangle_stepCount : RectangleExamples.oneRectangle.stepCount = 4 := rfl

/-- Every point of the retained rectangle's top edge satisfies its original certified lower bound on squared distance
from zero. -/
example (parameter : Coordinate) :
    RectangleExamples.zeroTopSafe.avoidsZero.bound <=
      Norm.Basic.normSq
      (RectangleExamples.zeroTop.pointAt parameter) :=
  by
    change sixteenth ≤ Norm.Basic.normSq (zeroTop.pointAt parameter)
    simpa only [Data.Gaussian.Basic.sub_zero] using
      (show sixteenth ≤ zeroTop.fixedGapSq 0 by decide).trans
        (zeroTop.fixedGapSq_normSq_lower 0 parameter)

/-- Every point of the retained rectangle's top edge satisfies its original certified lower bound on squared distance
from zero. -/
example (parameter : Coordinate) :
    RectangleExamples.oneLeftSafe.avoidsOne.bound <=
      Norm.Basic.normSq
      (RectangleExamples.oneLeft.pointAt parameter - 1) := by
  change sixteenth ≤ Norm.Basic.normSq (oneLeft.pointAt parameter - 1)
  exact (show sixteenth ≤ oneLeft.fixedGapSq 1 by decide).trans
    (oneLeft.fixedGapSq_normSq_lower 1 parameter)

end RectangleExamples

/-! ## Root frames and certified coefficient segments -/

set_option genInjectivity false in
/-- A Legendre chamber frame with a displayed logical identification of its three finite roots as `0`, `lambda`, and
`1`. -/
structure Frame (lambda : Gaussian) where
  /-- The original certified simple-root chamber frame. -/ chamber : ChamberFrame
  /-- The chamber polynomial is the exact displayed Legendre polynomial. -/ polynomial_eq : chamber.polynomial =
    polynomial lambda
  /-- The bijection identifying the three logical branch labels with chamber owners. -/ labels :
    Bijection 3 chamber.degree
  /-- Each logically labelled owner box contains its exact displayed branch point. -/ owner_contains : forall label :
    Fin 3,
    (chamber.owner (labels.forward label)).box.Contains
      (branchPoint lambda label)
  /-- The independent bijection from projection positions to original chamber owners. -/ projectionOrder :
    Bijection 3 chamber.degree
  /-- The certified refined root owner at each projection position. -/ projectionOwner : Fin 3 -> Local.Basic.LocalOwner
    chamber.polynomial
  /-- Each projection sample box refines its original chamber-owner box. -/ projection_refines : forall position : Fin
    3,
    (projectionOwner position).box.Refines
      (chamber.owner (projectionOrder.forward position)).box
  /-- The shared exact slope of the retained branch projection chart. -/ projectionSlope : Coordinate := 0
  /-- Rotated projection sample boxes are strictly ordered by their real-coordinate intervals. -/
    projection_xOrdered : forall
    left right : Fin 3, left.val < right.val ->
    (Geometry.Rational.Box.Rotation.enclosure projectionSlope (projectionOwner left).box).xUpper <
      (Geometry.Rational.Box.Rotation.enclosure projectionSlope (projectionOwner right).box).xLower

constructive_injectivity Frame

namespace Frame

/-- The chamber degree is exactly the displayed Legendre cubic degree. -/
theorem degree_eq_three {lambda : Gaussian} (frame : Frame lambda) :
    frame.chamber.degree = 3 := by
  calc
    frame.chamber.degree = frame.chamber.polynomial.natDegree :=
      frame.chamber.reference.polynomial_natDegree.symm
    _ = (polynomial lambda).natDegree :=
      congrArg DensePolynomial.natDegree
        frame.polynomial_eq
    _ = 3 := polynomial_natDegree lambda

/-- The independently certified left-to-right projection order on this Legendre root frame. -/
@[expose] def projected {lambda : Gaussian} (frame : Frame lambda) :
  ProjectedFrame 3 where
  chamber := frame.chamber
  degree_eq := frame.degree_eq_three
  orderToOwner := frame.projectionOrder
  sampleOwner := frame.projectionOwner
  sample_refines_owner := frame.projection_refines
  slope := frame.projectionSlope
  xOrdered := frame.projection_xOrdered

/-- Distinct logical branch labels have separated retained root-owner boxes. -/
theorem rootSeparation {lambda : Gaussian} (frame : Frame lambda)
    (left right : Fin 3) (different : left ≠ right) :
    (frame.chamber.owner (frame.labels.forward left)).box.Separated
      (frame.chamber.owner (frame.labels.forward right)).box :=
  frame.chamber.pairwiseSeparated _ _
    (fun equal => different (frame.labels.forward_injective equal))

/-- The retained labelled root owners exclude parameter zero.

The owners of `lambda` and `0` contain their exact branch points and are
positively separated, so those points cannot coincide. -/
theorem parameter_ne_zero {lambda : Gaussian} (frame : Frame lambda) : lambda ≠ 0 :=
  (frame.rootSeparation 1 0 (by decide)).points_ne
    (frame.owner_contains 1) (frame.owner_contains 0)

/-- The retained labelled root owners exclude parameter one.

The owners of `lambda` and `1` contain their exact branch points and are
positively separated, so those points cannot coincide. -/
theorem parameter_ne_one {lambda : Gaussian} (frame : Frame lambda) : lambda ≠ 1 :=
  (frame.rootSeparation 1 2 (by decide)).points_ne
    (frame.owner_contains 1) (frame.owner_contains 2)

/-- The difference from parameter one is nonzero in a retained root frame. -/
theorem parameter_sub_one_ne_zero {lambda : Gaussian} (frame : Frame lambda) : lambda - 1 ≠ 0 := by
  intro differenceZero
  exact frame.parameter_ne_one (Data.Gaussian.Basic.gaussian_eq_of_sub_eq_zero differenceZero)

end Frame

set_option genInjectivity false in
/-- A common positive rational lower bound for every owner bridge at both ends of one chamber overlap.

These are the finite square-root continuation clearances retained by the segment. -/
structure BridgeClearance {start finish : Gaussian}
    (left : Frame start) (right : Frame finish)
    (overlap : ChamberOverlap left.chamber right.chamber) where
  /-- The common rational lower bound for all endpoint bridge clearances. -/ bound : Coordinate
  /-- The common bridge bound is strictly positive. -/ positive : 0 < bound
  /-- The common clearance bounds every bridge clearance at the left endpoint. -/ leftLower : forall index :
    left.chamber.Index,
    bound <= (overlap.bridge index).leftClearance.bound
  /-- The common clearance bounds every bridge clearance at the right endpoint. -/ rightLower : forall index :
    left.chamber.Index,
    bound <= (overlap.bridge index).rightClearance.bound

constructive_injectivity BridgeClearance

set_option genInjectivity false in
/-- One fully certified Legendre parameter segment. -/
structure Segment {start finish : Gaussian}
    (left : Frame start) (right : Frame finish) where
  /-- The exact axis-aligned parameter segment joining the two frame parameters. -/ geometry :
    AxisSegment start finish
  /-- The segment clearance certificates for both singular parameter values. -/ safe :
    AxisSegment.Safe geometry
  /-- The atomic projected root overlap from which the braid event is extracted. -/ projection :
    ProjectedOverlap left.projected right.projected
  /-- The common positive bound for the original overlap bridge clearances. -/ sheetClearance :
    BridgeClearance left right projection.chamberOverlap

constructive_injectivity Segment

namespace Segment

/-- Construct a segment only from an atomic projected overlap.

Its braid word is extracted from the certified stationary/crossing event rather than accepted as an independent
annotation. -/
@[expose] def ofProjectedOverlap {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (geometry : AxisSegment start finish) (safe : AxisSegment.Safe geometry)
    (projection : ProjectedOverlap left.projected right.projected)
    (clearance : BridgeClearance left right projection.chamberOverlap) :
    Segment left right where
  geometry := geometry
  safe := safe
  projection := projection
  sheetClearance := clearance

/-- The root-owner overlap underlying the certified projected event. -/
@[expose] def coefficientOverlap {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (segment : Segment left right) : ChamberOverlap left.chamber
      right.chamber :=
  segment.projection.chamberOverlap

/-- The segment word is the output of its finite projected crossing chart. -/
@[expose] def crossings {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (segment : Segment left right) : Word 3 :=
  segment.projection.word

/-- The source owner at one certified projection position. -/
@[expose] def startOwnerIndex {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (_segment : Segment left right) (position : Fin 3) :
    left.chamber.Index :=
  left.projected.ownerIndex position

/-- Reverse a bridge-clearance certificate using the inverse owner matching.

The common bound is preserved and the two endpoint lower-bound families exchange roles. -/
@[expose] def reverseBridgeClearance {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    {overlap : ChamberOverlap left.chamber right.chamber}
    (clearance : BridgeClearance left right overlap) :
    BridgeClearance right left overlap.reverse where
  bound := clearance.bound
  positive := clearance.positive
  leftLower := by
    intro index
    change clearance.bound <=
      (overlap.bridge (overlap.matching.backward index)).rightClearance.bound
    exact clearance.rightLower (overlap.matching.backward index)
  rightLower := by
    intro index
    change clearance.bound <=
      (overlap.bridge (overlap.matching.backward index)).leftClearance.bound
    exact clearance.leftLower (overlap.matching.backward index)

/-- Reverse every geometric, root, sheet, and braid certificate of a segment. -/
@[expose] def reverse {start finish : Gaussian} {left : Frame start}
    {right : Frame finish} (segment : Segment left right) :
    Segment right left where
  geometry := segment.geometry.reverse
  safe := segment.safe.reverse
  projection := segment.projection.reverse
  sheetClearance := by
    rw [ProjectedOverlap.reverse_chamberOverlap]
    exact reverseBridgeClearance segment.sheetClearance

/-- The geometry of a reversed certified segment is the reversed original geometry. -/
@[simp] theorem reverse_geometry {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (segment : Segment left right) :
    segment.reverse.geometry = segment.geometry.reverse := rfl

/-- Reversing a certified segment inverts its extracted braid word. -/
@[simp] theorem reverse_crossings {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (segment : Segment left right) :
    segment.reverse.crossings = segment.crossings.inverse := by
  exact ProjectedOverlap.reverse_word
    segment.projection

end Segment

/-! ## Finite folds of certified segments -/

set_option genInjectivity false in
/-- A finite chain of certified parameter segments indexed by its original endpoint root frames. -/
inductive Path : {start finish : Gaussian} ->
    Frame start -> Frame finish -> Type 2
  /-- The empty certified path at one retained root frame. -/ | nil {parameter : Gaussian} (frame
    : Frame parameter) : Path frame frame
  /-- Prepend a certified segment to a path with its exact intermediate root frame. -/ | cons {start middle finish :
    Gaussian}
      {left : Frame start} {center : Frame middle} {right :
        Frame finish}
      (head : Segment left center) (remaining : Path center right) :
      Path left right

constructive_injectivity Path

namespace Path

/-- Count the finite certified segments in the path. -/
@[expose] def stepCount : {start finish : Gaussian} ->
    {left : Frame start} -> {right : Frame finish} ->
    Path left right -> Nat
  | _, _, _, _, .nil _ => 0
  | _, _, _, _, .cons _ remaining => remaining.stepCount + 1

/-- Segment words in traversal order, retained before flattening. -/
@[expose] def segmentWords : {start finish : Gaussian} ->
    {left : Frame start} -> {right : Frame finish} ->
    Path left right -> List (Word 3)
  | _, _, _, _, .nil _ => []
  | _, _, _, _, .cons head remaining =>
      head.crossings :: remaining.segmentWords

/-- Flatten the projected braid subdivisions in path order. -/
@[expose] def word : {start finish : Gaussian} ->
    {left : Frame start} -> {right : Frame finish} ->
    Path left right -> Word 3
  | _, _, _, _, .nil _ => []
  | _, _, _, _, .cons head remaining =>
      head.crossings ++ remaining.word

/-- Fold the actual chamber-owner matchings, independently of the extracted braid word. -/
@[expose] def ownerTransport : {start finish : Gaussian} ->
    {left : Frame start} -> {right : Frame finish} ->
    Path left right -> Bijection left.chamber.degree right.chamber.degree
  | _, _, _, _, .nil frame =>
      Bijection.identity frame.chamber.degree
  | _, _, _, _, .cons head remaining =>
      Bijection.comp remaining.ownerTransport
        head.projection.chamberOverlap.matching

/-- Every segment's exact bridge box followed by the boxes visited by the remaining logical branch label. -/
@[expose] def bridgeBoxes : {start finish : Gaussian} ->
    {left : Frame start} -> {right : Frame finish} ->
    (path : Path left right) -> Fin 3 -> List Rational.Box
  | _, _, _, _, .nil _, _ => []
  | _, _, _, _, .cons head remaining, position =>
      (head.projection.chamberOverlap.bridge
        (head.startOwnerIndex position)).box ::
        remaining.bridgeBoxes
          (head.projection.event.permutation.forward position)

/-- A branch-label route retains one bridge box for each segment in the certified path. -/
@[simp] theorem bridgeBoxes_length {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (path : Path left right) (label : Fin 3) :
    (path.bridgeBoxes label).length = path.stepCount := by
  induction path generalizing label with
  | nil frame => rfl
  | cons head remaining inductionHypothesis =>
      exact congrArg Nat.succ (inductionHypothesis
        ((ProjectedOverlap.event head.projection).permutation.forward label))

/-- The independently folded owner matching agrees pointwise with the word extracted from the atomic projection charts,
in the certified endpoint projection orders. -/
theorem ownerTransport_agrees {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (path : Path left right) (position : Fin 3) :
    path.ownerTransport.forward (left.projected.ownerIndex position) =
      right.projected.ownerIndex (path.word.permutation.forward position) := by
  induction path generalizing position with
  | nil frame =>
      change frame.projected.ownerIndex position =
        frame.projected.ownerIndex position
      rfl
  | @cons pathStart pathMiddle pathFinish pathLeft pathCenter pathRight
      head remaining inductionHypothesis =>
      change remaining.ownerTransport.forward
          (head.projection.chamberOverlap.matching.forward
            (pathLeft.projected.ownerIndex position)) = _
      rw [head.projection.matching_order position]
      calc
        remaining.ownerTransport.forward
            (pathCenter.projected.ownerIndex
              (head.projection.event.permutation.forward position)) =
            pathRight.projected.ownerIndex
              (remaining.word.permutation.forward
                (head.projection.event.permutation.forward position)) :=
          inductionHypothesis
            (head.projection.event.permutation.forward position)
        _ = pathRight.projected.ownerIndex
              ((head.crossings ++ remaining.word).permutation.forward
                position) :=
          congrArg pathRight.projected.ownerIndex
            (Word.permutation_append
              head.crossings remaining.word position).symm

/-- Concatenate certified paths while retaining their exact common intermediate frame. -/
@[expose] def append {first middle last : Gaussian}
    {left : Frame first} {center : Frame middle} {right :
      Frame last}
    (initial : Path left center) (remaining : Path center right) :
    Path left right :=
  match initial with
  | .nil _ => remaining
  | .cons head tail => .cons head (tail.append remaining)

open Purelib.Curves.Legendre.Paths.Path in
/-- Concatenating certified paths concatenates their extracted braid words in traversal order. -/
@[simp] theorem word_append {first middle last : Gaussian}
    {left : Frame first} {center : Frame middle} {right :
      Frame last}
    (initial : Path left center) (remaining : Path center right) :
    (initial.append remaining).word = initial.word ++ remaining.word := by
  induction initial with
  | nil frame => rfl
  | cons head tail inductionHypothesis =>
      change head.crossings ++ (tail.append remaining).word =
        (head.crossings ++ tail.word) ++ remaining.word
      rewrite [inductionHypothesis, Data.List.Append.append_assoc]
      exact Eq.refl _

/-- Owner transport along concatenated paths is the composition of their retained matchings. -/
theorem ownerTransport_append {first middle last : Gaussian}
    {left : Frame first} {center : Frame middle} {right :
      Frame last}
    (initial : Path left center) (remaining : Path center right)
    (index : left.chamber.Index) :
    (initial.append remaining).ownerTransport.forward index =
      remaining.ownerTransport.forward
        (initial.ownerTransport.forward index) := by
  induction initial with
  | nil frame =>
      change remaining.ownerTransport.forward index =
        remaining.ownerTransport.forward index
      rfl
  | cons head tail inductionHypothesis =>
      exact inductionHypothesis remaining
        (head.projection.chamberOverlap.matching.forward index)

/-- Reverse every certified segment and its order, retaining the reversed root frames. -/
@[expose] def reverse : {start finish : Gaussian} ->
    {left : Frame start} -> {right : Frame finish} ->
    Path left right -> Path right left
  | _, _, _, _, .nil frame => .nil frame
  | _, _, _, _, .cons head remaining =>
      remaining.reverse.append (.cons head.reverse (.nil _))

open Purelib.Curves.Legendre.Paths.Path in
/-- Reversing a certified path inverts its extracted braid word. -/
@[simp] theorem word_reverse {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (path : Path left right) : path.reverse.word = path.word.inverse := by
  induction path with
  | nil frame => rfl
  | cons head remaining inductionHypothesis =>
      rw [reverse, word_append, inductionHypothesis]
      simp only [word, head.reverse_crossings, Data.List.Append.append_nil]
      exact (Word.inverse_append
        head.crossings remaining.word).symm

/-- Reversed path transport is the backward map of the original owner bijection. -/
theorem ownerTransport_reverse {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (path : Path left right) (index : right.chamber.Index) :
    path.reverse.ownerTransport.forward index =
      path.ownerTransport.backward index := by
  induction path with
  | nil frame =>
      change index = index
      rfl
  | cons head remaining inductionHypothesis =>
      rw [reverse, ownerTransport_append]
      simp only [ownerTransport, Segment.reverse]
      rw [inductionHypothesis index]
      cases head.projection <;> rfl

end Path

@[expose] public section

set_option genInjectivity false in
/-- The ramification label at infinity is kept separate from the three finite-root labels, so its fixed transport is
definitionally visible. -/
inductive RamificationLabel
  /-- One of the three finite root ramification labels. -/ | finite (label : Fin 3)
  /-- The separate ramification label at infinity. -/ | infinity
deriving DecidableEq

constructive_injectivity RamificationLabel

derive_exposed_repr RamificationLabel

end

/-- Transport finite ramification labels by the braid permutation and retain infinity unchanged. -/
@[expose] def transportRamification (word : Word 3) :
    RamificationLabel -> RamificationLabel
  | .finite label => .finite (word.permutation.forward label)
  | .infinity => .infinity

/-- Every braid word fixes the separate infinity ramification label. -/
@[simp] theorem transportRamification_infinity (word : Word 3) :
    transportRamification word .infinity = .infinity := rfl

/-- Transport by the inverse braid word undoes ramification-label transport. -/
@[simp] theorem transportRamification_inverse (word : Word 3)
    (label : RamificationLabel) :
    transportRamification word.inverse (transportRamification word label) =
      label := by
  cases label with
  | infinity => rfl
  | finite label =>
      apply congrArg RamificationLabel.finite
      calc
        word.inverse.permutation.forward (word.permutation.forward label) =
            word.permutation.reverse.forward
              (word.permutation.forward label) :=
          Word.permutation_inverse word _
        _ = word.permutation.backward (word.permutation.forward label) := rfl
        _ = label := word.permutation.backward_forward label

end Purelib.Curves.Legendre.Paths
