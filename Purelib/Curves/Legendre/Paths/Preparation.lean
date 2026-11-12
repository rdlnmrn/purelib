module

public import Purelib.Curves.Legendre.Paths.Projection
import Purelib.Curves.Legendre.Paths
public import Purelib.Data.Fin
public import Purelib.Geometry.Rational.Box.Square.Centered.Rotation
import Purelib.Data.Fin.Bijection.Transposition
import Purelib.Data.Fin.Cases
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Bounds.Abs
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Tactic.Ring

/-!
# Preparation of original Legendre root frames

A retained separating rational chart orders the original parameter's three
branch readings. Exact finite bijections retain the original logical labels
zero, parameter and one while computing their increasing projection order.
-/

public section

namespace Purelib.Curves.Legendre.Paths

open Purelib
open Purelib.Data
open Purelib.Data.Fin.Bijection
open Purelib.Data.Gaussian.Coordinates
open Purelib.Data.Rat
open Fraction.Order
open Purelib.Geometry.Rational
open Box.Square.Centered

/-- Compute the increasing projection order of the original three branch labels.

The fixed zero and one readings leave three possible positions for the
parameter reading. Two exact comparisons select identity or the appropriate
adjacent transposition, preserving an explicit inverse on the same labels. -/
@[expose] def branchOrder (lambda : Gaussian) (slope : Coordinate) : Bijection 3 3 :=
  if (branchProjection lambda 1 slope).re < 0 then Transposition.transposition 0 1
  else if (branchProjection lambda 1 slope).re < 1 then identity 3
  else Transposition.transposition 1 2

/-- A negative moving-branch reading gives the original lower adjacent transposition of logical labels. -/
theorem branchOrder_of_negative (lambda : Gaussian) (slope : Coordinate)
    (negative : (branchProjection lambda 1 slope).re < 0) :
    branchOrder lambda slope = Transposition.transposition 0 1 := by
  unfold branchOrder
  rewrite [if_pos negative]
  rfl

/-- A moving-branch reading strictly between the fixed readings gives the original identity label order. -/
theorem branchOrder_of_between (lambda : Gaussian) (slope : Coordinate)
    (positive : 0 < (branchProjection lambda 1 slope).re)
    (belowOne : (branchProjection lambda 1 slope).re < 1) : branchOrder lambda slope = identity 3 := by
  unfold branchOrder
  rewrite [if_neg (fun negative => lt_asymm negative positive), if_pos belowOne]
  rfl

/-- A moving-branch reading above one gives the original upper adjacent transposition of logical labels. -/
theorem branchOrder_of_above_one (lambda : Gaussian) (slope : Coordinate)
    (aboveOne : 1 < (branchProjection lambda 1 slope).re) :
    branchOrder lambda slope = Transposition.transposition 1 2 := by
  have positive := (by decide : (0 : Coordinate) < 1).trans aboveOne
  unfold branchOrder
  rewrite [if_neg (fun negative => lt_asymm negative positive),
    if_neg (fun belowOne => lt_asymm belowOne aboveOne)]
  rfl

/-- The actual moving branch retains the original parameter reading in every displayed chart. -/
private theorem moving_real (lambda : Gaussian) (slope : Coordinate) :
    (branchProjection lambda 1 slope).re = lambda.re + slope * lambda.im := by
  rewrite [branchProjection, branchPoint_one, Rotation.rotate_real]
  rfl

/-- Charts above the same original forbidden-slope cost have the same complete original branch-order bijection.

Positive imaginary parameters read above one in either chart, and negative
imaginary parameters read below zero. A real parameter keeps the same
original real reading. Each case selects the identical original finite
bijection; no equality between forward functions is assumed or proved.
-/
theorem branchOrder_eq_of_slopeCost (lambda : Gaussian) (first last : Coordinate)
    (firstPaid : Projection.slopeCost lambda < first) (lastPaid : Projection.slopeCost lambda < last) :
    branchOrder lambda first = branchOrder lambda last := by
  rcases lt_trichotomy lambda.im 0 with negative | real | positive
  · have firstBelow : (branchProjection lambda 1 first).re < 0 := by
      rewrite [moving_real]
      exact Projection.reading_below_zero lambda first firstPaid negative
    have lastBelow : (branchProjection lambda 1 last).re < 0 := by
      rewrite [moving_real]
      exact Projection.reading_below_zero lambda last lastPaid negative
    rewrite [branchOrder_of_negative lambda first firstBelow, branchOrder_of_negative lambda last lastBelow]
    rfl
  · have firstReal : (branchProjection lambda 1 first).re = lambda.re :=
      (moving_real lambda first).trans (Projection.reading_of_real lambda first real)
    have lastReal : (branchProjection lambda 1 last).re = lambda.re :=
      (moving_real lambda last).trans (Projection.reading_of_real lambda last real)
    unfold branchOrder
    rewrite [firstReal, lastReal]
    rfl
  · have firstAbove : 1 < (branchProjection lambda 1 first).re := by
      rewrite [moving_real]
      exact Projection.reading_above_one lambda first firstPaid positive
    have lastAbove : 1 < (branchProjection lambda 1 last).re := by
      rewrite [moving_real]
      exact Projection.reading_above_one lambda last lastPaid positive
    rewrite [branchOrder_of_above_one lambda first firstAbove, branchOrder_of_above_one lambda last lastAbove]
    rfl

/-- Two computed finite-family charts retain the same complete branch order at the same original shared parameter.

The families may have different lengths, additional vertices or repeated
vertices. The displayed point equality retains the shared original
parameter, and both actual computed slopes pay its own forbidden cost.
-/
theorem branchOrder_forParameters_eq {firstCount lastCount : Nat}
    (first : Fin firstCount → Gaussian) (last : Fin lastCount → Gaussian)
    (firstIndex : Fin firstCount) (lastIndex : Fin lastCount) (same : first firstIndex = last lastIndex) :
    branchOrder (first firstIndex) (Projection.forParameters first) =
      branchOrder (last lastIndex) (Projection.forParameters last) := by
  have lastPaid := Projection.slopeCost_lt_forParameters last lastIndex
  rewrite [← same] at lastPaid
  have orders := branchOrder_eq_of_slopeCost (first firstIndex) (Projection.forParameters first)
    (Projection.forParameters last) (Projection.slopeCost_lt_forParameters first firstIndex) lastPaid
  exact orders.trans (congrArg (fun parameter => branchOrder parameter (Projection.forParameters last)) same)

/-- The zero branch retains real reading zero in every selected projection chart. -/
private theorem zero_real (lambda : Gaussian) (slope : Coordinate) : (branchProjection lambda 0 slope).re = 0 := by
  rewrite [branchProjection, branchPoint_zero, Rotation.rotate_real]
  change 0 + slope * 0 = 0
  ring1

/-- The one branch retains real reading one in every selected projection chart. -/
private theorem one_real (lambda : Gaussian) (slope : Coordinate) : (branchProjection lambda 2 slope).re = 1 := by
  rewrite [branchProjection, branchPoint_two, Rotation.rotate_real]
  change 1 + slope * 0 = 1
  ring1

/-- Adjacent strict inequalities order every pair of increasing indices in a three-entry rational reading. -/
private theorem ordered_three (reading : Fin 3 → Coordinate)
    (first : reading 0 < reading 1) (second : reading 1 < reading 2)
    (left right : Fin 3) (ordered : left.val < right.val) : reading left < reading right := by
  rcases Fin.Cases.three left with leftZero | leftOne | leftTwo <;>
    subst left <;>
    rcases Fin.Cases.three right with rightZero | rightOne | rightTwo <;>
    subst right
  all_goals first
    | exact ((by decide : ¬ ((0 : Nat) < 0)) ordered).elim
    | exact ((by decide : ¬ ((1 : Nat) < 0)) ordered).elim
    | exact ((by decide : ¬ ((1 : Nat) < 1)) ordered).elim
    | exact ((by decide : ¬ ((2 : Nat) < 0)) ordered).elim
    | exact ((by decide : ¬ ((2 : Nat) < 1)) ordered).elim
    | exact ((by decide : ¬ ((2 : Nat) < 2)) ordered).elim
    | exact first
    | exact second
    | exact first.trans second

/-- The retained chart separation makes the computed branch order strictly increasing in its retained chart.

The same chart separates all original branch readings. The two possible
equality branches are excluded by its exact separation laws; the finite
order is computed rather than supplied. -/
theorem branchOrder_real_lt (lambda : Gaussian) (slope : Coordinate)
    (separated : lambda.re + slope * lambda.im ≠ 0 ∧ lambda.re + slope * lambda.im ≠ 1)
    (left right : Fin 3) (ordered : left.val < right.val) :
    (branchProjection lambda ((branchOrder lambda slope).forward left) slope).re <
      (branchProjection lambda ((branchOrder lambda slope).forward right) slope).re := by
  rcases lt_trichotomy (branchProjection lambda 1 slope).re 0 with negative | equalZero | positive
  · rewrite [branchOrder, if_pos negative]
    apply ordered_three _ _ _ left right ordered
    · change (branchProjection lambda 1 slope).re < (branchProjection lambda 0 slope).re
      rewrite [zero_real]
      exact negative
    · change (branchProjection lambda 0 slope).re < (branchProjection lambda 2 slope).re
      rewrite [zero_real, one_real]
      decide
  · exact (branchProjection_real_distinct_of_separation lambda slope separated 1 0 (by decide)
      (equalZero.trans (zero_real lambda slope).symm)).elim
  · have notNegative : ¬ (branchProjection lambda 1 slope).re < 0 :=
      fun negative => lt_asymm negative positive
    rewrite [branchOrder, if_neg notNegative]
    rcases lt_trichotomy (branchProjection lambda 1 slope).re 1 with between | equalOne | above
    · rewrite [if_pos between]
      apply ordered_three _ _ _ left right ordered
      · change (branchProjection lambda 0 slope).re < (branchProjection lambda 1 slope).re
        rewrite [zero_real]
        exact positive
      · change (branchProjection lambda 1 slope).re < (branchProjection lambda 2 slope).re
        rewrite [one_real]
        exact between
    · exact (branchProjection_real_distinct_of_separation lambda slope separated 1 2 (by decide)
        (equalOne.trans (one_real lambda slope).symm)).elim
    · have notBetween : ¬ (branchProjection lambda 1 slope).re < 1 :=
        fun between => lt_asymm between above
      rewrite [if_neg notBetween]
      apply ordered_three _ _ _ left right ordered
      · change (branchProjection lambda 0 slope).re < (branchProjection lambda 2 slope).re
        rewrite [zero_real, one_real]
        decide
      · change (branchProjection lambda 2 slope).re < (branchProjection lambda 1 slope).re
        rewrite [one_real]
        exact above

/-- The smaller adjacent gap between the three exactly ordered branch projections.

The original order, shared slope and all three readings are retained in the calculation.
This minimum bounds both consecutive projection gaps in that same chart. -/
@[expose] def branchProjectionGap (lambda : Gaussian) (slope : Coordinate) : Coordinate :=
  let order := branchOrder lambda slope
  let lower := branchProjection lambda (order.forward 0) slope
  let middle := branchProjection lambda (order.forward 1) slope
  let upper := branchProjection lambda (order.forward 2) slope
  min (middle.re - lower.re) (upper.re - middle.re)

/-- The computed projection gap is positive in every retained separating chart. -/
theorem branchProjectionGap_positive (lambda : Gaussian) (slope : Coordinate)
    (separated : lambda.re + slope * lambda.im ≠ 0 ∧ lambda.re + slope * lambda.im ≠ 1) :
    0 < branchProjectionGap lambda slope := by
  unfold branchProjectionGap
  exact Basic.lt_min
    (Arithmetic.sub_pos_direct (branchOrder_real_lt lambda slope separated 0 1 (by decide)))
    (Arithmetic.sub_pos_direct (branchOrder_real_lt lambda slope separated 1 2 (by decide)))

/-- Floors paid by both original fixed-reading displacements and by one bound the actual adjacent projection gap.

The original three-branch order places the moving reading below zero,
between zero and one, or above one. Its two actual adjacent differences
are therefore paid by the corresponding displacement magnitudes or by
the original fixed zero-to-one difference. -/
theorem branchProjectionGap_lower_bound (lambda : Gaussian) (slope floor : Coordinate)
    (fixed : floor ≤ 1) (zero : floor ≤ Fraction.abs (branchProjection lambda 1 slope).re)
    (one : floor ≤ Fraction.abs ((branchProjection lambda 1 slope).re - 1)) :
    floor ≤ branchProjectionGap lambda slope := by
  by_cases negative : (branchProjection lambda 1 slope).re < 0
  · unfold branchProjectionGap
    rewrite [branchOrder_of_negative _ _ negative]
    change floor ≤ min ((branchProjection lambda 0 slope).re - (branchProjection lambda 1 slope).re)
      ((branchProjection lambda 2 slope).re - (branchProjection lambda 0 slope).re)
    rewrite [zero_real, one_real, show (1 - 0 : Coordinate) = 1 by ring1]
    rewrite [Bounds.Abs.abs_of_nonpositive negative.le] at zero
    rewrite [show (0 : Coordinate) - (branchProjection lambda 1 slope).re =
      -(branchProjection lambda 1 slope).re by ring1]
    exact Basic.le_min zero fixed
  · have nonnegative := le_of_not_gt negative
    unfold branchProjectionGap branchOrder
    rewrite [if_neg negative]
    by_cases belowOne : (branchProjection lambda 1 slope).re < 1
    · rewrite [if_pos belowOne]
      change floor ≤ min ((branchProjection lambda 1 slope).re - (branchProjection lambda 0 slope).re)
        ((branchProjection lambda 2 slope).re - (branchProjection lambda 1 slope).re)
      rewrite [zero_real, one_real,
        show (branchProjection lambda 1 slope).re - 0 = (branchProjection lambda 1 slope).re by ring1]
      rewrite [Bounds.Abs.abs_of_nonnegative nonnegative] at zero
      have shiftedNonpositive : (branchProjection lambda 1 slope).re - 1 ≤ 0 :=
        Boundary.sub_nonpositive_iff.mpr belowOne.le
      rewrite [Bounds.Abs.abs_of_nonpositive shiftedNonpositive,
        show -((branchProjection lambda 1 slope).re - 1) = 1 - (branchProjection lambda 1 slope).re by ring1] at one
      exact Basic.le_min zero one
    · rewrite [if_neg belowOne]
      change floor ≤ min ((branchProjection lambda 2 slope).re - (branchProjection lambda 0 slope).re)
        ((branchProjection lambda 1 slope).re - (branchProjection lambda 2 slope).re)
      rewrite [zero_real, one_real, show (1 - 0 : Coordinate) = 1 by ring1]
      rewrite [Bounds.Abs.abs_of_nonnegative (Arithmetic.sub_nonneg_direct (le_of_not_gt belowOne))] at one
      exact Basic.le_min fixed one

/-- The computed adjacent minimum bounds every increasing pair of original branch projections.

The outer pair has the sum of the two positive adjacent gaps. The same
retained minimum therefore bounds all three possible increasing pairs. -/
theorem branchProjectionGap_le_difference (lambda : Gaussian) (slope : Coordinate)
    (separated : lambda.re + slope * lambda.im ≠ 0 ∧ lambda.re + slope * lambda.im ≠ 1)
    (left right : Fin 3) (ordered : left.val < right.val) :
    branchProjectionGap lambda slope ≤
      (branchProjection lambda ((branchOrder lambda slope).forward right) slope).re -
        (branchProjection lambda ((branchOrder lambda slope).forward left) slope).re := by
  have first : branchProjectionGap lambda slope ≤
      (branchProjection lambda ((branchOrder lambda slope).forward 1) slope).re -
        (branchProjection lambda ((branchOrder lambda slope).forward 0) slope).re :=
    Basic.min_le_left _ _
  have second : branchProjectionGap lambda slope ≤
      (branchProjection lambda ((branchOrder lambda slope).forward 2) slope).re -
        (branchProjection lambda ((branchOrder lambda slope).forward 1) slope).re :=
    Basic.min_le_right _ _
  have outer : branchProjectionGap lambda slope ≤
      (branchProjection lambda ((branchOrder lambda slope).forward 2) slope).re -
        (branchProjection lambda ((branchOrder lambda slope).forward 0) slope).re := by
    have secondPositive := Arithmetic.sub_pos_direct
      (branchOrder_real_lt lambda slope separated 1 2 (by decide))
    calc
      branchProjectionGap lambda slope ≤
          (branchProjection lambda ((branchOrder lambda slope).forward 1) slope).re -
            (branchProjection lambda ((branchOrder lambda slope).forward 0) slope).re := first
      _ = ((branchProjection lambda ((branchOrder lambda slope).forward 1) slope).re -
          (branchProjection lambda ((branchOrder lambda slope).forward 0) slope).re) + 0 := by ring1
      _ ≤ ((branchProjection lambda ((branchOrder lambda slope).forward 1) slope).re -
          (branchProjection lambda ((branchOrder lambda slope).forward 0) slope).re) +
          ((branchProjection lambda ((branchOrder lambda slope).forward 2) slope).re -
            (branchProjection lambda ((branchOrder lambda slope).forward 1) slope).re) :=
        Arithmetic.add_le_add_direct le_rfl secondPositive.le
      _ = _ := by ring1
  have pairs : (left = 0 ∧ right = 1) ∨ (left = 1 ∧ right = 2) ∨ (left = 0 ∧ right = 2) := by
    rcases Fin.Cases.three left with leftZero | leftOne | leftTwo <;>
      subst left <;>
      rcases Fin.Cases.three right with rightZero | rightOne | rightTwo <;>
      subst right
    all_goals first
      | exact ((by decide : ¬ ((0 : Nat) < 0)) ordered).elim
      | exact ((by decide : ¬ ((1 : Nat) < 0)) ordered).elim
      | exact ((by decide : ¬ ((1 : Nat) < 1)) ordered).elim
      | exact ((by decide : ¬ ((2 : Nat) < 0)) ordered).elim
      | exact ((by decide : ¬ ((2 : Nat) < 1)) ordered).elim
      | exact ((by decide : ¬ ((2 : Nat) < 2)) ordered).elim
      | exact Or.inl ⟨rfl, rfl⟩
      | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  rcases pairs with ⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩
  · cases leftEq
    cases rightEq
    exact first
  · cases leftEq
    cases rightEq
    exact second
  · cases leftEq
    cases rightEq
    exact outer

/-- Compute a rational square radius whose two rotated half-widths fit inside the original branch projection gap.

The exact gap is divided by one plus the combined enclosure cost. The
retained positive cap and unit cap limit the same radius while preserving
the full two-box projection payment. -/
@[expose] def branchRadius (lambda : Gaussian) (slope : Coordinate)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) : Coordinate :=
  min (min 1 cap.val) (branchProjectionGap lambda slope / (2 * (1 + Fraction.abs slope) + 1))

/-- The computed original branch radius is at most the same retained positive cap. -/
theorem branchRadius_le_cap (lambda : Gaussian) (slope : Coordinate)
    (cap : {value : Coordinate // 0 < value}) : branchRadius lambda slope cap ≤ cap.val :=
  (Basic.min_le_left _ _).trans (Basic.min_le_right _ _)

/-- A capped original branch radius is at most the radius of the original unit-capped procedure. -/
theorem branchRadius_le_default (lambda : Gaussian) (slope : Coordinate)
    (cap : {value : Coordinate // 0 < value}) : branchRadius lambda slope cap ≤ branchRadius lambda slope :=
  Basic.le_min ((Basic.min_le_left _ _).trans (Basic.min_le_left _ _)) (Basic.min_le_right _ _)

/-- The two-box rotation enclosure cost is nonnegative for every selected slope. -/
private theorem enclosureCost_nonnegative (slope : Coordinate) :
    0 ≤ 2 * (1 + Fraction.abs slope) := by
  have factorNonnegative := Arithmetic.add_le_add_direct
    (show (0 : Fraction.Rational) ≤ 1 by decide)
    (Arithmetic.abs_nonneg_direct (slope))
  change 0 ≤ 1 + Fraction.abs slope at factorNonnegative
  exact Arithmetic.mul_nonneg_direct (by decide) factorNonnegative

/-- A lower bound on the original projection gap gives the same chart's explicit lower bound on its computed radius.

Dividing the supplied scalar floor by the original positive enclosure
cost and capping at one stays below the actual unit-capped branch radius.
The floor need not be positive for this comparison law. -/
theorem branchRadius_lower_bound (lambda : Gaussian) (slope floor : Coordinate)
    (below : floor ≤ branchProjectionGap lambda slope) :
    min 1 (floor / (2 * (1 + Fraction.abs slope) + 1)) ≤ branchRadius lambda slope := by
  have costPositive := Arithmetic.add_pos_of_nonneg_of_pos_direct
    (enclosureCost_nonnegative slope) (by decide : (0 : Coordinate) < 1)
  unfold branchRadius
  rewrite [Basic.min_eq_left (le_rfl : (1 : Coordinate) ≤ 1)]
  exact Basic.min_le_min le_rfl (Field.div_le_div_of_cross costPositive costPositive
    (Arithmetic.mul_le_mul_of_nonneg_right_direct below costPositive.le))

/-- The retained chart separation makes the computed branch square radius positive. -/
theorem branchRadius_positive (lambda : Gaussian) (slope : Coordinate)
    (separated : lambda.re + slope * lambda.im ≠ 0 ∧ lambda.re + slope * lambda.im ≠ 1)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    0 < branchRadius lambda slope cap := by
  unfold branchRadius
  exact Basic.lt_min (Basic.lt_min (by decide) cap.property)
    (Field.div_pos_direct (branchProjectionGap_positive lambda slope separated)
      (Arithmetic.add_pos_of_nonneg_of_pos_direct (enclosureCost_nonnegative slope) (by decide)))

/-- The actual two-box rotated width of the computed radius is strictly below the original projection gap. -/
theorem branchRadius_pays_enclosures (lambda : Gaussian) (slope : Coordinate)
    (separated : lambda.re + slope * lambda.im ≠ 0 ∧ lambda.re + slope * lambda.im ≠ 1)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    2 * ((1 + Fraction.abs slope) * branchRadius lambda slope cap) < branchProjectionGap lambda slope := by
  calc
    2 * ((1 + Fraction.abs slope) * branchRadius lambda slope cap) =
        (2 * (1 + Fraction.abs slope)) * branchRadius lambda slope cap := by ring1
    _ ≤ (2 * (1 + Fraction.abs slope)) * branchRadius lambda slope :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct (branchRadius_le_default lambda slope cap)
        (enclosureCost_nonnegative slope)
    _ < branchProjectionGap lambda slope :=
      Field.mul_min_one_div_lt (enclosureCost_nonnegative slope)
        (branchProjectionGap_positive lambda slope separated)

/-- Compute the three original branch squares using one retained positive radius.

The radius and all three boxes are constructed before the entry selector.
Logical labels continue to mean zero, parameter and one independently of
their computed projection positions. -/
@[expose] def branchBoxes (lambda : Gaussian) (slope : Coordinate)
    (separated : lambda.re + slope * lambda.im ≠ 0 ∧ lambda.re + slope * lambda.im ≠ 1)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    Fin 3 → Box :=
  let radius := branchRadius lambda slope cap
  let nonnegative := (branchRadius_positive lambda slope separated cap).le
  let zero := Affine.centeredSquare (branchPoint lambda 0) radius nonnegative
  let moving := Affine.centeredSquare (branchPoint lambda 1) radius nonnegative
  let one := Affine.centeredSquare (branchPoint lambda 2) radius nonnegative
  Data.Fin.cases zero (fun rest => Data.Fin.cases moving (fun _ => one) rest)

/-- Each retained branch box is the original square about its own logical branch point. -/
theorem branchBoxes_eq (lambda : Gaussian) (slope : Coordinate)
    (separated : lambda.re + slope * lambda.im ≠ 0 ∧ lambda.re + slope * lambda.im ≠ 1)
    (label : Fin 3) (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    branchBoxes lambda slope separated (cap := cap) label =
      Affine.centeredSquare (branchPoint lambda label) (branchRadius lambda slope cap)
        (branchRadius_positive lambda slope separated cap).le := by
  rcases Fin.Cases.three label with atZero | atOne | atTwo <;> subst label <;> rfl

/-- Every internally computed branch square is proper. -/
theorem branchBoxes_proper (lambda : Gaussian) (slope : Coordinate)
    (separated : lambda.re + slope * lambda.im ≠ 0 ∧ lambda.re + slope * lambda.im ≠ 1)
    (label : Fin 3) (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    (branchBoxes lambda slope separated (cap := cap) label).Proper := by
  rewrite [branchBoxes_eq (cap := cap)]
  exact centeredSquare_proper _ (branchRadius_positive lambda slope separated cap)

/-- The rotated enclosures of the retained branch squares have their computed strict projection order.

The exact enclosure formula uses the original selected slope and cached
radius. The radius payment is below the retained branch gap, which bounds
the actual difference of these two ordered projection readings. -/
theorem branchBoxes_xOrdered (lambda : Gaussian) (slope : Coordinate)
    (separated : lambda.re + slope * lambda.im ≠ 0 ∧ lambda.re + slope * lambda.im ≠ 1)
    (left right : Fin 3) (ordered : left.val < right.val)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    (Box.Rotation.enclosure (slope)
      (branchBoxes lambda slope separated (cap := cap) ((branchOrder lambda slope).forward left))).xUpper <
    (Box.Rotation.enclosure (slope)
      (branchBoxes lambda slope separated (cap := cap) ((branchOrder lambda slope).forward right))).xLower := by
  rewrite [branchBoxes_eq (cap := cap), branchBoxes_eq (cap := cap), Box.Rotation.enclosure_centeredSquare,
    Box.Rotation.enclosure_centeredSquare]
  change (branchProjection lambda ((branchOrder lambda slope).forward left) slope).re +
      (1 + Fraction.abs slope) * branchRadius lambda slope cap <
    (branchProjection lambda ((branchOrder lambda slope).forward right) slope).re -
      (1 + Fraction.abs slope) * branchRadius lambda slope cap
  apply Arithmetic.lt_of_sub_pos_direct
  have paid := (branchRadius_pays_enclosures lambda slope separated cap).trans_le
    (branchProjectionGap_le_difference lambda slope separated left right ordered)
  have positive := Arithmetic.sub_pos_direct paid
  calc
    0 < ((branchProjection lambda ((branchOrder lambda slope).forward right) slope).re -
        (branchProjection lambda ((branchOrder lambda slope).forward left) slope).re) -
        2 * ((1 + Fraction.abs slope) * branchRadius lambda slope cap) := positive
    _ = _ := by ring1

/-- Increasing projection positions give separated original branch boxes.

If the original boxes overlapped, their displayed common point would rotate
into both enclosures. Their strict horizontal gap excludes that same point,
so the retained original boxes already have a strict coordinate separation. -/
private theorem branchBoxes_ordered_separated (lambda : Gaussian) (slope : Coordinate)
    (separated : lambda.re + slope * lambda.im ≠ 0 ∧ lambda.re + slope * lambda.im ≠ 1)
    (left right : Fin 3) (ordered : left.val < right.val)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    (branchBoxes lambda slope separated (cap := cap) ((branchOrder lambda slope).forward left)).Separated
      (branchBoxes lambda slope separated (cap := cap) ((branchOrder lambda slope).forward right)) := by
  by_cases boxesSeparated :
      (branchBoxes lambda slope separated (cap := cap) ((branchOrder lambda slope).forward left)).Separated
        (branchBoxes lambda slope separated (cap := cap) ((branchOrder lambda slope).forward right))
  · exact boxesSeparated
  · have common := Box.contains_overlapPoint_of_not_separated boxesSeparated
    have leftContains := Box.Rotation.enclosure_contains (slope) _ common.1
    have rightContains := Box.Rotation.enclosure_contains (slope) _ common.2
    have gap := branchBoxes_xOrdered lambda slope separated left right ordered cap
    exact (lt_irrefl _ ((leftContains.2.1.trans_lt gap).trans_le rightContains.1)).elim

/-- Different logical branches have pairwise separated internally computed original boxes.

The inverse of the retained projection order identifies their positions.
One of the two strict position orders applies to the same original boxes;
no root enumeration or replacement owner is selected. -/
theorem branchBoxes_separated (lambda : Gaussian) (slope : Coordinate)
    (separated : lambda.re + slope * lambda.im ≠ 0 ∧ lambda.re + slope * lambda.im ≠ 1)
    (left right : Fin 3) (different : left ≠ right)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    (branchBoxes lambda slope separated (cap := cap) left).Separated
      (branchBoxes lambda slope separated (cap := cap) right) := by
  have positionsDifferent : (branchOrder lambda slope).backward left ≠ (branchOrder lambda slope).backward right := by
    intro same
    have labelsSame := congrArg (branchOrder lambda slope).forward same
    rewrite [(branchOrder lambda slope).forward_backward, (branchOrder lambda slope).forward_backward] at labelsSame
    exact different labelsSame
  rcases lt_trichotomy ((branchOrder lambda slope).backward left).val
      ((branchOrder lambda slope).backward right).val with increasing | same | decreasing
  · have separated := branchBoxes_ordered_separated lambda slope separated
      ((branchOrder lambda slope).backward left) ((branchOrder lambda slope).backward right) increasing cap
    rewrite [(branchOrder lambda slope).forward_backward, (branchOrder lambda slope).forward_backward] at separated
    exact separated
  · exact (positionsDifferent (Fin.ext same)).elim
  · have separated := branchBoxes_ordered_separated lambda slope separated
      ((branchOrder lambda slope).backward right) ((branchOrder lambda slope).backward left) decreasing cap
    rewrite [(branchOrder lambda slope).forward_backward, (branchOrder lambda slope).forward_backward] at separated
    exact Box.separated_symm separated

end Purelib.Curves.Legendre.Paths
