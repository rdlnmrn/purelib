module

public import Purelib.Curves.Legendre.Paths
public import Purelib.Data.Rat.Interval.Radius
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Interval.ConvexCombination
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Quantitative windows in original axis segments

The original endpoint velocity determines exact squared displacement.
A unit anchor and a positive squared allowance compute a finite
parameter window whose every original point pays that allowance. Restriction
keeps the original affine parametrization and intrinsic branch avoidance.
-/

public section

namespace Purelib.Curves.Legendre.Paths.AxisSegment

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Fraction.Order

/-- Restrict the original axis segment to two displayed affine parameters.

The same horizontal or vertical direction is retained, with original
point evaluations as its indexed endpoints. Parameters may have either
orientation or coincide. -/
@[expose] def restrict {start finish : Gaussian} (segment : AxisSegment start finish)
    (first last : Coordinate) : AxisSegment (segment.pointAt first) (segment.pointAt last) :=
  match segment with
  | .horizontal firstCoord lastCoord height =>
      .horizontal (firstCoord + (lastCoord - firstCoord) * first)
        (firstCoord + (lastCoord - firstCoord) * last) height
  | .vertical real firstCoord lastCoord =>
      .vertical real (firstCoord + (lastCoord - firstCoord) * first)
        (firstCoord + (lastCoord - firstCoord) * last)

/-- A restricted segment evaluates the original parametrization at the affine combination of retained parameters. -/
theorem restrict_pointAt {start finish : Gaussian} (segment : AxisSegment start finish)
    (first last parameter : Coordinate) :
    (segment.restrict first last).pointAt parameter = segment.pointAt (first + parameter * (last - first)) := by
  cases segment with
  | horizontal firstCoord lastCoord height =>
      apply Gaussian.Basic.ext
      · change (firstCoord + (lastCoord - firstCoord) * first) +
          ((firstCoord + (lastCoord - firstCoord) * last) -
            (firstCoord + (lastCoord - firstCoord) * first)) * parameter =
            firstCoord + (lastCoord - firstCoord) * (first + parameter * (last - first))
        ring1
      · rfl
  | vertical real firstCoord lastCoord =>
      apply Gaussian.Basic.ext
      · rfl
      · change (firstCoord + (lastCoord - firstCoord) * first) +
          ((firstCoord + (lastCoord - firstCoord) * last) -
            (firstCoord + (lastCoord - firstCoord) * first)) * parameter =
            firstCoord + (lastCoord - firstCoord) * (first + parameter * (last - first))
        ring1

/-- Reversing the original axis segment preserves intrinsic avoidance of the same excluded point.

Every reversed unit parameter evaluates the original segment at its
complementary unit parameter. The original whole-interval exclusion
therefore excludes that same point after exchanging the endpoints. -/
theorem Avoids.reverse {start finish : Gaussian} {segment : AxisSegment start finish} {excluded : Gaussian}
    (avoids : segment.Avoids excluded) : segment.reverse.Avoids excluded := by
  intro parameter nonnegative atMostOne
  rewrite [pointAt_reverse]
  have upper : 1 - parameter ≤ 1 := by
    calc
      1 - parameter ≤ 1 - 0 := Arithmetic.sub_le_sub_left_direct nonnegative 1
      _ = 1 := by ring1
  exact avoids (1 - parameter) (Arithmetic.sub_nonneg_direct atMostOne) upper

/-- Restricting to original unit-interval parameters preserves intrinsic avoidance of the same excluded point. -/
theorem Avoids.restrict {start finish : Gaussian} {segment : AxisSegment start finish} {excluded : Gaussian}
    (avoids : segment.Avoids excluded) (first last : Coordinate)
    (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    (segment.restrict first last).Avoids excluded := by
  intro parameter nonnegative atMostOne
  have inside := Box.coordinate_between firstInside lastInside ⟨nonnegative, atMostOne⟩
  rewrite [restrict_pointAt]
  exact avoids _ inside.1 inside.2

/-- Original point displacement equals parameter displacement squared times the original endpoint velocity squared. -/
theorem pointAt_normSq_sub {start finish : Gaussian} (segment : AxisSegment start finish)
    (parameter anchor : Coordinate) :
    Gaussian.Norm.Basic.normSq (segment.pointAt parameter - segment.pointAt anchor) =
      (parameter - anchor) ^ 2 * Gaussian.Norm.Basic.normSq (finish - start) := by
  cases segment with
  | horizontal first last height =>
      change ((first + (last - first) * parameter) - (first + (last - first) * anchor)) ^ 2 +
        (height - height) ^ 2 = (parameter - anchor) ^ 2 * ((last - first) ^ 2 + (height - height) ^ 2)
      ring1
  | vertical real first last =>
      change (real - real) ^ 2 +
        ((first + (last - first) * parameter) - (first + (last - first) * anchor)) ^ 2 =
          (parameter - anchor) ^ 2 * ((real - real) ^ 2 + (last - first) ^ 2)
      ring1

/-- Compute a parameter radius from the original endpoint distances and squared displacement allowance.

Interior anchors retain their original two half-distance caps. At either
unit endpoint its zero cap is replaced by one, allowing a positive radius
on the retained side. The original incremented velocity cost pays the
same strict displacement allowance, including stationary segments. -/
@[expose] def windowRadius {start finish : Gaussian} (_segment : AxisSegment start finish)
    (anchor allowance : Coordinate) : Coordinate :=
  min (if anchor = 0 then 1 else anchor / 2) (min (if anchor = 1 then 1 else (1 - anchor) / 2)
    (min 1 (allowance / (Gaussian.Norm.Basic.normSq (finish - start) + 1))))

/-- Interior anchors retain the same complete original half-distance and velocity-allocation formula. -/
theorem windowRadius_of_interior {start finish : Gaussian} (segment : AxisSegment start finish)
    (anchor allowance : Coordinate) (interior : 0 < anchor ∧ anchor < 1) :
    segment.windowRadius anchor allowance = min (anchor / 2) (min ((1 - anchor) / 2)
      (min 1 (allowance / (Gaussian.Norm.Basic.normSq (finish - start) + 1)))) := by
  unfold windowRadius
  rewrite [if_neg interior.1.ne', if_neg interior.2.ne]
  rfl

/-- Every unit anchor and positive allowance give a strictly positive original window radius. -/
theorem windowRadius_positive {start finish : Gaussian} (segment : AxisSegment start finish)
    (anchor allowance : Coordinate) (inside : 0 ≤ anchor ∧ anchor ≤ 1) (positive : 0 < allowance) :
    0 < segment.windowRadius anchor allowance := by
  have left : 0 < (if anchor = 0 then 1 else anchor / 2) := by
    by_cases zero : anchor = 0
    · rewrite [if_pos zero]
      decide
    · rewrite [if_neg zero]
      have strict : 0 < anchor :=
        ⟨inside.1, fun reverse => zero (Basic.le_antisymm _ _ reverse inside.1)⟩
      exact Field.div_pos_direct strict (by decide)
  have right : 0 < (if anchor = 1 then 1 else (1 - anchor) / 2) := by
    by_cases one : anchor = 1
    · rewrite [if_pos one]
      decide
    · rewrite [if_neg one]
      have strict : anchor < 1 :=
        ⟨inside.2, fun reverse => one (Basic.le_antisymm _ _ inside.2 reverse)⟩
      exact Field.div_pos_direct (Arithmetic.sub_pos_direct strict) (by decide)
  unfold windowRadius
  exact Basic.lt_min left (Basic.lt_min right (Basic.lt_min (by decide) (Field.div_pos_direct positive
    (Arithmetic.add_pos_of_nonneg_of_pos_direct (Gaussian.Norm.Basic.normSq_nonneg _) (by decide)))))

/-- The computed radius is smaller than both original distances from an interior anchor to the unit endpoints. -/
theorem windowRadius_lt_endpoints {start finish : Gaussian} (segment : AxisSegment start finish)
    (anchor allowance : Coordinate) (interior : 0 < anchor ∧ anchor < 1) :
    segment.windowRadius anchor allowance < anchor ∧ segment.windowRadius anchor allowance < 1 - anchor := by
  rewrite [segment.windowRadius_of_interior anchor allowance interior]
  constructor
  · exact (Basic.min_le_left _ _).trans_lt (Field.half_lt_self interior.1)
  · exact ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _)).trans_lt
      (Field.half_lt_self (Arithmetic.sub_pos_direct interior.2))

/-- The computed radius uses no more than the same capped original velocity allocation. -/
theorem windowRadius_le_allocation {start finish : Gaussian} (segment : AxisSegment start finish)
    (anchor allowance : Coordinate) :
    segment.windowRadius anchor allowance ≤
      min 1 (allowance / (Gaussian.Norm.Basic.normSq (finish - start) + 1)) :=
  (Basic.min_le_right _ _).trans (Basic.min_le_right _ _)

/-- Construct the original rational parameter window at any unit anchor with its computed positive radius.

The original centered endpoints are clipped to the closed unit interval.
Interior anchors retain their exact original endpoints; a unit endpoint
anchor has a proper one-sided window containing that same endpoint. -/
@[expose] def window {start finish : Gaussian} (segment : AxisSegment start finish)
    (anchor allowance : Coordinate) (inside : 0 ≤ anchor ∧ anchor ≤ 1) (positive : 0 < allowance) : Interval.Bounds :=
  let radius := segment.windowRadius anchor allowance
  let nonnegative := (segment.windowRadius_positive anchor allowance inside positive).le
  have lower : max 0 (anchor - radius) ≤ anchor := Basic.max_le inside.1 (by
    calc
      anchor - radius ≤ anchor - 0 := Arithmetic.sub_le_sub_left_direct nonnegative anchor
      _ = anchor := by ring1)
  have upper : anchor ≤ min 1 (anchor + radius) := Basic.le_min inside.2 (by
    calc
      anchor = anchor + 0 := by ring1
      _ ≤ anchor + radius := Arithmetic.add_le_add_direct le_rfl nonnegative)
  ⟨max 0 (anchor - radius), min 1 (anchor + radius), lower.trans upper⟩

/-- The computed window is proper and lies in the original closed unit parameter interval. -/
theorem window_bounds {start finish : Gaussian} (segment : AxisSegment start finish)
    (anchor allowance : Coordinate) (inside : 0 ≤ anchor ∧ anchor ≤ 1) (positive : 0 < allowance) :
    0 ≤ (segment.window anchor allowance inside positive).lower ∧
      (segment.window anchor allowance inside positive).lower <
        (segment.window anchor allowance inside positive).upper ∧
      (segment.window anchor allowance inside positive).upper ≤ 1 := by
  have radiusPositive := segment.windowRadius_positive anchor allowance inside positive
  have lower : anchor - segment.windowRadius anchor allowance < anchor := by
    calc
      anchor - segment.windowRadius anchor allowance < anchor - 0 :=
        Arithmetic.sub_lt_sub_left_direct radiusPositive anchor
      _ = anchor := by ring1
  have upper : anchor < anchor + segment.windowRadius anchor allowance := by
    calc
      anchor = anchor + 0 := by ring1
      _ < anchor + segment.windowRadius anchor allowance := Arithmetic.add_lt_add_left_direct radiusPositive anchor
  exact ⟨Basic.le_max_left _ _,
    Basic.lt_min (Basic.max_lt (by decide) (lower.trans_le inside.2))
      (Basic.max_lt (inside.1.trans_lt upper) (lower.trans upper)), Basic.min_le_left _ _⟩

/-- The original window anchored at the initial unit endpoint retains that exact lower endpoint. -/
theorem window_lower_zero {start finish : Gaussian} (segment : AxisSegment start finish)
    (allowance : Coordinate) (positive : 0 < allowance) :
    (segment.window 0 allowance (by constructor <;> decide) positive).lower = 0 := by
  apply Basic.max_eq_left
  have nonnegative := (segment.windowRadius_positive 0 allowance (by constructor <;> decide) positive).le
  calc
    0 - segment.windowRadius 0 allowance ≤ 0 - 0 := Arithmetic.sub_le_sub_left_direct nonnegative 0
    _ = 0 := by ring1

/-- The original window anchored at the final unit endpoint retains that exact upper endpoint. -/
theorem window_upper_one {start finish : Gaussian} (segment : AxisSegment start finish)
    (allowance : Coordinate) (positive : 0 < allowance) :
    (segment.window 1 allowance (by constructor <;> decide) positive).upper = 1 := by
  apply Basic.min_eq_left
  have nonnegative := (segment.windowRadius_positive 1 allowance (by constructor <;> decide) positive).le
  calc
    1 = 1 + 0 := by ring1
    _ ≤ 1 + segment.windowRadius 1 allowance := Arithmetic.add_le_add_direct le_rfl nonnegative

/-- At an interior anchor the original lower endpoint is unchanged by closed-unit clipping. -/
theorem window_lower_of_interior {start finish : Gaussian} (segment : AxisSegment start finish)
    (anchor allowance : Coordinate) (inside : 0 ≤ anchor ∧ anchor ≤ 1) (positive : 0 < allowance)
    (interior : 0 < anchor ∧ anchor < 1) :
    (segment.window anchor allowance inside positive).lower = anchor - segment.windowRadius anchor allowance :=
  Basic.max_eq_right (Arithmetic.sub_pos_direct (segment.windowRadius_lt_endpoints anchor allowance interior).1).le

/-- At an interior anchor the original upper endpoint is unchanged by closed-unit clipping. -/
theorem window_upper_of_interior {start finish : Gaussian} (segment : AxisSegment start finish)
    (anchor allowance : Coordinate) (inside : 0 ≤ anchor ∧ anchor ≤ 1) (positive : 0 < allowance)
    (interior : 0 < anchor ∧ anchor < 1) :
    (segment.window anchor allowance inside positive).upper = anchor + segment.windowRadius anchor allowance := by
  apply Basic.min_eq_right
  have radiusBound := (segment.windowRadius_lt_endpoints anchor allowance interior).2
  calc
    anchor + segment.windowRadius anchor allowance ≤ anchor + (1 - anchor) :=
      Arithmetic.add_le_add_direct le_rfl radiusBound.le
    _ = 1 := by ring1

/-- Restricting to a computed original window preserves intrinsic avoidance of the same excluded point. -/
theorem Avoids.window_restrict {start finish : Gaussian} {segment : AxisSegment start finish} {excluded : Gaussian}
    (avoids : segment.Avoids excluded) (anchor allowance : Coordinate)
    (inside : 0 ≤ anchor ∧ anchor ≤ 1) (positive : 0 < allowance) :
    (segment.restrict (segment.window anchor allowance inside positive).lower
      (segment.window anchor allowance inside positive).upper).Avoids excluded := by
  have bounds := segment.window_bounds anchor allowance inside positive
  exact avoids.restrict _ _ ⟨bounds.1, (segment.window anchor allowance inside positive).valid.trans bounds.2.2⟩
    ⟨bounds.1.trans (segment.window anchor allowance inside positive).valid, bounds.2.2⟩

/-- The original anchor is contained in its computed parameter window, including either unit endpoint. -/
theorem window_contains_anchor {start finish : Gaussian} (segment : AxisSegment start finish)
    (anchor allowance : Coordinate) (inside : 0 ≤ anchor ∧ anchor ≤ 1) (positive : 0 < allowance) :
    (segment.window anchor allowance inside positive).Contains anchor := by
  have nonnegative := (segment.windowRadius_positive anchor allowance inside positive).le
  constructor
  · apply Basic.max_le inside.1
    calc
      anchor - segment.windowRadius anchor allowance ≤ anchor - 0 :=
        Arithmetic.sub_le_sub_left_direct nonnegative anchor
      _ = anchor := by ring1
  · apply Basic.le_min inside.2
    calc
      anchor = anchor + 0 := by ring1
      _ ≤ anchor + segment.windowRadius anchor allowance := Arithmetic.add_le_add_direct le_rfl nonnegative

/-- The original window's squared sample radius equals its same computed radius squared at every unit anchor.

Interior anchors retain their centered window. At either unit endpoint
one endpoint is the anchor and the other retains the same positive radius,
so clipping preserves the original maximum squared displacement. -/
theorem window_sampleRadiusSq {start finish : Gaussian} (segment : AxisSegment start finish)
    (anchor allowance : Coordinate) (inside : 0 ≤ anchor ∧ anchor ≤ 1) (positive : 0 < allowance) :
    Interval.Radius.sampleRadiusSq (segment.window anchor allowance inside positive) anchor =
      segment.windowRadius anchor allowance ^ 2 := by
  have radiusNonnegative := (segment.windowRadius_positive anchor allowance inside positive).le
  have radiusAtMostOne := (segment.windowRadius_le_allocation anchor allowance).trans (Basic.min_le_left _ _)
  by_cases zero : anchor = 0
  · subst anchor
    have lower : 0 - segment.windowRadius 0 allowance ≤ 0 := by
      calc
        0 - segment.windowRadius 0 allowance ≤ 0 - 0 :=
          Arithmetic.sub_le_sub_left_direct radiusNonnegative 0
        _ = 0 := by ring1
    have upper : 0 + segment.windowRadius 0 allowance ≤ 1 := by
      calc
        0 + segment.windowRadius 0 allowance = segment.windowRadius 0 allowance := by ring1
        _ ≤ 1 := radiusAtMostOne
    unfold Interval.Radius.sampleRadiusSq
    change max ((max 0 (0 - segment.windowRadius 0 allowance) - 0) ^ 2)
      ((min 1 (0 + segment.windowRadius 0 allowance) - 0) ^ 2) = segment.windowRadius 0 allowance ^ 2
    rewrite [Basic.max_eq_left lower, Basic.min_eq_right upper,
      show (0 - 0 : Coordinate) ^ 2 = 0 by ring1,
      show (0 + segment.windowRadius 0 allowance - 0) ^ 2 = segment.windowRadius 0 allowance ^ 2 by ring1]
    exact Basic.max_eq_right (Arithmetic.sq_nonneg_direct _)
  · by_cases one : anchor = 1
    · subst anchor
      have lower : 0 ≤ 1 - segment.windowRadius 1 allowance := Arithmetic.sub_nonneg_direct radiusAtMostOne
      have upper : 1 ≤ 1 + segment.windowRadius 1 allowance := by
        calc
          1 = 1 + 0 := by ring1
          _ ≤ 1 + segment.windowRadius 1 allowance := Arithmetic.add_le_add_direct le_rfl radiusNonnegative
      unfold Interval.Radius.sampleRadiusSq
      change max ((max 0 (1 - segment.windowRadius 1 allowance) - 1) ^ 2)
        ((min 1 (1 + segment.windowRadius 1 allowance) - 1) ^ 2) = segment.windowRadius 1 allowance ^ 2
      rewrite [Basic.max_eq_right lower, Basic.min_eq_left upper,
        show (1 - 1 : Coordinate) ^ 2 = 0 by ring1,
        show (1 - segment.windowRadius 1 allowance - 1) ^ 2 = segment.windowRadius 1 allowance ^ 2 by ring1]
      exact Basic.max_eq_left (Arithmetic.sq_nonneg_direct _)
    · have interior : 0 < anchor ∧ anchor < 1 :=
        ⟨⟨inside.1, fun reverse => zero (Basic.le_antisymm _ _ reverse inside.1)⟩,
          ⟨inside.2, fun reverse => one (Basic.le_antisymm _ _ inside.2 reverse)⟩⟩
      unfold Interval.Radius.sampleRadiusSq
      rewrite [segment.window_lower_of_interior anchor allowance inside positive interior,
        segment.window_upper_of_interior anchor allowance inside positive interior,
        show (anchor - segment.windowRadius anchor allowance - anchor) ^ 2 =
          segment.windowRadius anchor allowance ^ 2 by ring1,
        show (anchor + segment.windowRadius anchor allowance - anchor) ^ 2 =
          segment.windowRadius anchor allowance ^ 2 by ring1]
      exact Basic.max_eq_left le_rfl

/-- Every original point in the computed window has squared displacement from its retained anchor below the allowance.

The original interval bounds its squared parameter displacement. The radius
cap at one then bounds that square by the same radius, and the incremented
original velocity allocation pays the strict squared displacement bound. -/
theorem window_normSq_lt {start finish : Gaussian} (segment : AxisSegment start finish)
    (anchor allowance : Coordinate) (bounds : 0 ≤ anchor ∧ anchor ≤ 1) (positive : 0 < allowance)
    (parameter : Coordinate) (inside : (segment.window anchor allowance bounds positive).Contains parameter) :
    Gaussian.Norm.Basic.normSq (segment.pointAt parameter - segment.pointAt anchor) < allowance := by
  have parameterSquare := Interval.Radius.sub_sq_le_sampleRadiusSq _ (sample := anchor) inside
  rewrite [window_sampleRadiusSq] at parameterSquare
  have radiusNonnegative := (segment.windowRadius_positive anchor allowance bounds positive).le
  have allocated := segment.windowRadius_le_allocation anchor allowance
  have radiusAtMostOne := allocated.trans (Basic.min_le_left _ _)
  have radiusSquare : segment.windowRadius anchor allowance ^ 2 ≤ segment.windowRadius anchor allowance := by
    calc
      _ = segment.windowRadius anchor allowance * segment.windowRadius anchor allowance := by ring1
      _ ≤ 1 * segment.windowRadius anchor allowance :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct radiusAtMostOne radiusNonnegative
      _ = segment.windowRadius anchor allowance := Fraction.Field.one_mul _
  rewrite [pointAt_normSq_sub]
  calc
    _ ≤ segment.windowRadius anchor allowance ^ 2 * Gaussian.Norm.Basic.normSq (finish - start) :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct parameterSquare (Gaussian.Norm.Basic.normSq_nonneg _)
    _ ≤ segment.windowRadius anchor allowance * Gaussian.Norm.Basic.normSq (finish - start) :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct radiusSquare (Gaussian.Norm.Basic.normSq_nonneg _)
    _ = Gaussian.Norm.Basic.normSq (finish - start) * segment.windowRadius anchor allowance := by ring1
    _ ≤ Gaussian.Norm.Basic.normSq (finish - start) *
        min 1 (allowance / (Gaussian.Norm.Basic.normSq (finish - start) + 1)) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct allocated (Gaussian.Norm.Basic.normSq_nonneg _)
    _ < allowance := Field.mul_min_one_div_lt (Gaussian.Norm.Basic.normSq_nonneg _) positive

/-- The computed original parameter window contains an interior anchor strictly between its endpoints.

The original positive radius puts the same lower and upper endpoints
strictly on opposite sides of every interior anchor. Those original
endpoints are unchanged by the closed-unit clipping. -/
theorem window_anchor_interior {start finish : Gaussian} (segment : AxisSegment start finish)
    (anchor allowance : Coordinate) (interior : 0 < anchor ∧ anchor < 1) (positive : 0 < allowance) :
    (segment.window anchor allowance ⟨interior.1.le, interior.2.le⟩ positive).lower < anchor ∧
      anchor < (segment.window anchor allowance ⟨interior.1.le, interior.2.le⟩ positive).upper := by
  have radiusPositive := segment.windowRadius_positive anchor allowance ⟨interior.1.le, interior.2.le⟩ positive
  rewrite [segment.window_lower_of_interior anchor allowance _ positive interior,
    segment.window_upper_of_interior anchor allowance _ positive interior]
  constructor
  · calc
      anchor - segment.windowRadius anchor allowance < anchor - 0 :=
        Arithmetic.sub_lt_sub_left_direct radiusPositive anchor
      _ = anchor := by ring1
  · calc
      anchor = anchor + 0 := by ring1
      _ < anchor + segment.windowRadius anchor allowance := Arithmetic.add_lt_add_left_direct radiusPositive anchor

end Purelib.Curves.Legendre.Paths.AxisSegment
