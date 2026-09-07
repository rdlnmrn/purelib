import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.Cylinder
import CCL.Geometry.FiniteGeometric
import CCL.Measure.Basic
import FiniteMeasure.Bounds

/-!
# Rational diameter content of finite CCL cylinders

The quantity here is explicitly a geometric squared-diameter budget, not a
probability mass.  Every statement concerns a supplied finite block list and
supplied finite realization certificates.
-/

namespace CCL.FiniteMeasure

abbrev Block := CCL.Cylinder.Block
abbrev Proj := CCL.GaussianProjective.Proj

/-- Canonical rational squared-chordal spread of a completed-block prefix. -/
def cylinderSpread (blocks : List Block) : Coordinate :=
  (1 / 2 : Coordinate) ^ blocks.length

theorem cylinderSpread_nonneg (blocks : List Block) :
    0 ≤ cylinderSpread blocks :=
  RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) blocks.length

theorem half_pow_le_one (count : Nat) :
    (1 / 2 : Coordinate) ^ count ≤ 1 := by
  induction count with
  | zero => exact le_rfl
  | succ count inductionHypothesis =>
      rw [pow_succ]
      calc
        (1 / 2 : Coordinate) ^ count * (1 / 2) ≤ 1 * (1 / 2) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            inductionHypothesis (by decide)
        _ ≤ 1 := by decide

theorem cylinderSpread_le_one (blocks : List Block) :
    cylinderSpread blocks ≤ 1 :=
  half_pow_le_one blocks.length

/-- Enclose all realized pairwise squared distances between zero and the
canonical finite prefix spread. -/
def cylinderDistanceBound (blocks : List Block) :
    _root_.FiniteMeasure.Bound where
  lower := 0
  upper := cylinderSpread blocks
  valid := cylinderSpread_nonneg blocks

theorem cylinderDistanceBound_width (blocks : List Block) :
    (cylinderDistanceBound blocks).width = cylinderSpread blocks := by
  dsimp only [_root_.FiniteMeasure.Bound.width, cylinderDistanceBound]
  ring1

/-- Every two supplied realizations of the finite prefix have squared
chordal distance inside its rational diameter enclosure. -/
theorem realized_distance_mem
    {blocks : List Block} {left right : Proj}
    (leftRealizes : CCL.Cylinder.Realizes blocks left)
    (rightRealizes : CCL.Cylinder.Realizes blocks right) :
    (cylinderDistanceBound blocks).Contains
      (CCL.Chordal.chordalSq left right) :=
  ⟨CCL.Chordal.chordalSq_nonneg left right,
    CCL.Cylinder.Realizes.chordalSq_le_half_pow
      leftRealizes rightRealizes⟩

/-- A finite number of completed blocks calculated from a positive rational
squared-chordal request.  The factor two converts quarter-power search into
the CCL half-power spread. -/
def requiredBlockCount (target : Coordinate) : Nat :=
  2 * CCL.FiniteGeometric.firstQuarterBelow 1 0 target

private theorem half_pow_two_mul (index : Nat) :
    (1 / 2 : Coordinate) ^ (2 * index) = (1 / 4 : Coordinate) ^ index := by
  calc
    (1 / 2 : Coordinate) ^ (2 * index) =
        ((1 / 2 : Coordinate) ^ 2) ^ index := by rw [pow_mul]
    _ = (1 / 4 : Coordinate) ^ index := by
      have halfSquare : (1 / 2 : Coordinate) ^ 2 = 1 / 4 := by decide
      rw [halfSquare]

/-- The computed finite block count has canonical spread below the supplied
positive rational request. -/
theorem requiredBlockCount_spread_lt
    {target : Coordinate} (positive : 0 < target) :
    (1 / 2 : Coordinate) ^ requiredBlockCount target < target := by
  let index := CCL.FiniteGeometric.firstQuarterBelow 1 0 target
  have requested := CCL.FiniteGeometric.firstQuarterBelow_accurate
    (scale := (1 : Coordinate)) (by decide) 0 target positive
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow] at requested
  simp only [one_mul] at requested
  simpa only [requiredBlockCount, index, half_pow_two_mul] using requested

/-- Adding still more completed blocks preserves a met diameter request. -/
theorem cylinderSpread_lt_of_requiredBlockCount_le
    {blocks : List Block} {target : Coordinate} (positive : 0 < target)
    (enough : requiredBlockCount target ≤ blocks.length) :
    cylinderSpread blocks < target := by
  obtain ⟨extra, lengthEqual⟩ := Nat.exists_eq_add_of_le enough
  rw [cylinderSpread, lengthEqual, pow_add]
  have extraPowerLeOne : (1 / 2 : Coordinate) ^ extra ≤ 1 := by
    have powerBound := RFAP.ConstructiveFraction.pow_le_pow_direct
      (by decide : (0 : Coordinate) ≤ 1 / 2)
      (by decide : (1 / 2 : Coordinate) ≤ 1) extra
    simpa only [one_pow] using powerBound
  have prefixNonnegative :
      0 ≤ (1 / 2 : Coordinate) ^ requiredBlockCount target :=
    RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _
  calc
    (1 / 2 : Coordinate) ^ requiredBlockCount target *
          (1 / 2 : Coordinate) ^ extra ≤
        (1 / 2 : Coordinate) ^ requiredBlockCount target * 1 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        extraPowerLeOne prefixNonnegative
    _ = (1 / 2 : Coordinate) ^ requiredBlockCount target := by ring1
    _ < target := requiredBlockCount_spread_lt positive

/-- Requested-length finite CCL realizations are pairwise below the rational
squared-chordal target, without selecting a projective point. -/
theorem realized_distance_lt_requested
    {blocks : List Block} {target : Coordinate} (positive : 0 < target)
    (enough : requiredBlockCount target ≤ blocks.length)
    {left right : Proj}
    (leftRealizes : CCL.Cylinder.Realizes blocks left)
    (rightRealizes : CCL.Cylinder.Realizes blocks right) :
    CCL.Chordal.chordalSq left right < target :=
  (CCL.Cylinder.Realizes.chordalSq_le_half_pow
    leftRealizes rightRealizes).trans_lt
      (cylinderSpread_lt_of_requiredBlockCount_le positive enough)

end CCL.FiniteMeasure
