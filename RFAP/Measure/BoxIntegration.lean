import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Integration
import RFAP.Measure.BoxContent

/-!
# Finite rational box integration

Displayed RFAP boxes supply exact nonnegative cell weights for the generic
finite integration layer.  Vertical and horizontal rational cuts become
certified integration subdivisions by exact finite area conservation.
-/

namespace RFAP.FiniteMeasure

/-- One rational box carrying a certified rational range for an integrand. -/
structure BoxIntegrationCell where
  box : Box
  lower : Coordinate
  upper : Coordinate
  range_valid : lower ≤ upper

namespace BoxIntegrationCell

/-- Forget box-specific syntax while retaining exact area as cell weight. -/
def toIntegrationCell (cell : BoxIntegrationCell) :
    _root_.FiniteMeasure.IntegrationCell Box where
  item := cell.box
  weight := boxContent cell.box
  weight_nonnegative := boxContent_nonneg cell.box
  lower := cell.lower
  upper := cell.upper
  range_valid := cell.range_valid

/-- Reuse the parent's integrand range on one displayed child box. -/
def sameRange (parent : BoxIntegrationCell) (box : Box) :
    BoxIntegrationCell :=
  ⟨box, parent.lower, parent.upper, parent.range_valid⟩

end BoxIntegrationCell

/-- Convert a displayed box-cell list into the neutral finite integration
frontier. -/
def boxIntegrationCells (cells : List BoxIntegrationCell) :
    List (_root_.FiniteMeasure.IntegrationCell Box) :=
  cells.map BoxIntegrationCell.toIntegrationCell

theorem integrationWeight_boxIntegrationCells :
    ∀ cells : List BoxIntegrationCell,
      _root_.FiniteMeasure.integrationWeight (boxIntegrationCells cells) =
        (cells.map fun cell => boxContent cell.box).sum
  | [] => rfl
  | cell :: remaining => by
      simp only [boxIntegrationCells, List.map_cons,
        _root_.FiniteMeasure.integrationWeight,
        BoxIntegrationCell.toIntegrationCell, List.sum_cons]
      change boxContent cell.box +
          _root_.FiniteMeasure.integrationWeight
            (boxIntegrationCells remaining) =
        boxContent cell.box +
          (remaining.map fun candidate => boxContent candidate.box).sum
      rw [integrationWeight_boxIntegrationCells remaining]

/-- Lower/upper finite rational integral enclosure for displayed box cells. -/
def boxIntegralBound (cells : List BoxIntegrationCell) :
    _root_.FiniteMeasure.Bound :=
  _root_.FiniteMeasure.integralBound (boxIntegrationCells cells)

theorem boxIntegralBound_width (cells : List BoxIntegrationCell) :
    (boxIntegralBound cells).width =
      _root_.FiniteMeasure.integralOscillation
        (boxIntegrationCells cells) :=
  _root_.FiniteMeasure.integralBound_width _

/-- Box-specific finite subdivision certificate. -/
structure BoxIntegrationSplit (parent : BoxIntegrationCell) where
  children : List BoxIntegrationCell
  content_conserved :
    (children.map fun child => boxContent child.box).sum =
      boxContent parent.box
  lower_refines : ∀ child, child ∈ children → parent.lower ≤ child.lower
  upper_refines : ∀ child, child ∈ children → child.upper ≤ parent.upper

namespace BoxIntegrationSplit

/-- A box subdivision is a generic finite integration subdivision. -/
def toIntegrationSplit {parent : BoxIntegrationCell}
    (split : BoxIntegrationSplit parent) :
    _root_.FiniteMeasure.IntegrationSplit parent.toIntegrationCell where
  children := boxIntegrationCells split.children
  weight_conserved := by
    rw [integrationWeight_boxIntegrationCells, split.content_conserved]
    rfl
  lower_refines := by
    intro child member
    simp only [boxIntegrationCells, QuotientFreeList.mem_map] at member
    rcases member with ⟨boxChild, boxChildMember, rfl⟩
    exact split.lower_refines boxChild boxChildMember
  upper_refines := by
    intro child member
    simp only [boxIntegrationCells, QuotientFreeList.mem_map] at member
    rcases member with ⟨boxChild, boxChildMember, rfl⟩
    exact split.upper_refines boxChild boxChildMember

theorem integralBound_refines {parent : BoxIntegrationCell}
    (split : BoxIntegrationSplit parent) :
    _root_.FiniteMeasure.Bound.Refines
      (_root_.FiniteMeasure.integralBound
        (boxIntegrationCells split.children))
      (_root_.FiniteMeasure.integralBound [parent.toIntegrationCell]) :=
  split.toIntegrationSplit.integralBound_refines

end BoxIntegrationSplit

theorem boxContent_sameRange_cells (parent : BoxIntegrationCell) :
    ∀ boxes : List Box,
      (boxes.map parent.sameRange).map
          (fun child => boxContent child.box) =
        boxes.map boxContent
  | [] => rfl
  | box :: remaining => by
      simp only [List.map_cons, BoxIntegrationCell.sameRange]
      rw [boxContent_sameRange_cells parent remaining]

/-- Any exact finite area partition becomes an integration split when every
child retains the parent's displayed integrand range. -/
def sameRangeSplit (parent : BoxIntegrationCell) (boxes : List Box)
    (conserved : (boxes.map boxContent).sum = boxContent parent.box) :
    BoxIntegrationSplit parent where
  children := boxes.map parent.sameRange
  content_conserved := by
    rw [boxContent_sameRange_cells]
    exact conserved
  lower_refines := by
    intro child member
    simp only [QuotientFreeList.mem_map] at member
    rcases member with ⟨box, boxMember, rfl⟩
    exact le_rfl
  upper_refines := by
    intro child member
    simp only [QuotientFreeList.mem_map] at member
    rcases member with ⟨box, boxMember, rfl⟩
    exact le_rfl

/-- Exact two-child integration split at a displayed vertical rational cut. -/
def verticalSameRangeSplit (parent : BoxIntegrationCell)
    (cut : Coordinate)
    (inside : parent.box.xLower ≤ cut ∧ cut ≤ parent.box.xUpper) :
    BoxIntegrationSplit parent :=
  sameRangeSplit parent
    [parent.box.verticalLeft cut inside, parent.box.verticalRight cut inside]
    (by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      exact vertical_content_add parent.box cut inside)

/-- Exact two-child integration split at a displayed horizontal rational
cut. -/
def horizontalSameRangeSplit (parent : BoxIntegrationCell)
    (cut : Coordinate)
    (inside : parent.box.yLower ≤ cut ∧ cut ≤ parent.box.yUpper) :
    BoxIntegrationSplit parent :=
  sameRangeSplit parent
    [parent.box.horizontalLower cut inside,
      parent.box.horizontalUpper cut inside]
    (by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      exact horizontal_content_add parent.box cut inside)

theorem verticalSameRange_integralBound_refines
    (parent : BoxIntegrationCell) (cut : Coordinate)
    (inside : parent.box.xLower ≤ cut ∧ cut ≤ parent.box.xUpper) :
    _root_.FiniteMeasure.Bound.Refines
      (_root_.FiniteMeasure.integralBound
        (boxIntegrationCells
          (verticalSameRangeSplit parent cut inside).children))
      (_root_.FiniteMeasure.integralBound [parent.toIntegrationCell]) :=
  (verticalSameRangeSplit parent cut inside).integralBound_refines

theorem horizontalSameRange_integralBound_refines
    (parent : BoxIntegrationCell) (cut : Coordinate)
    (inside : parent.box.yLower ≤ cut ∧ cut ≤ parent.box.yUpper) :
    _root_.FiniteMeasure.Bound.Refines
      (_root_.FiniteMeasure.integralBound
        (boxIntegrationCells
          (horizontalSameRangeSplit parent cut inside).children))
      (_root_.FiniteMeasure.integralBound [parent.toIntegrationCell]) :=
  (horizontalSameRangeSplit parent cut inside).integralBound_refines

/-! ## Bounded upper sums on finite covers -/

/-- Give every box in a finite cover the same displayed integrand range. -/
def coverRangeCells (cover : BoxCover) (lower upper : Coordinate)
    (valid : lower ≤ upper) : List BoxIntegrationCell :=
  cover.boxes.map fun box => ⟨box, lower, upper, valid⟩

theorem lowerIntegral_coverRangeCells (cover : BoxCover)
    (lower upper : Coordinate) (valid : lower ≤ upper) :
    _root_.FiniteMeasure.lowerIntegral
        (boxIntegrationCells (coverRangeCells cover lower upper valid)) =
      cover.content * lower := by
  rcases cover with ⟨boxes⟩
  induction boxes with
  | nil =>
      simp only [coverRangeCells, boxIntegrationCells,
        _root_.FiniteMeasure.lowerIntegral, BoxCover.content,
        List.map_nil, List.sum_nil, zero_mul]
  | cons box remaining inductionHypothesis =>
      simp only [coverRangeCells, boxIntegrationCells, List.map_cons,
        _root_.FiniteMeasure.lowerIntegral,
        BoxIntegrationCell.toIntegrationCell, BoxCover.content,
        List.sum_cons] at inductionHypothesis ⊢
      rw [inductionHypothesis]
      ring1

theorem upperIntegral_coverRangeCells (cover : BoxCover)
    (lower upper : Coordinate) (valid : lower ≤ upper) :
    _root_.FiniteMeasure.upperIntegral
        (boxIntegrationCells (coverRangeCells cover lower upper valid)) =
      cover.content * upper := by
  rcases cover with ⟨boxes⟩
  induction boxes with
  | nil =>
      simp only [coverRangeCells, boxIntegrationCells,
        _root_.FiniteMeasure.upperIntegral, BoxCover.content,
        List.map_nil, List.sum_nil, zero_mul]
  | cons box remaining inductionHypothesis =>
      simp only [coverRangeCells, boxIntegrationCells, List.map_cons,
        _root_.FiniteMeasure.upperIntegral,
        BoxIntegrationCell.toIntegrationCell, BoxCover.content,
        List.sum_cons] at inductionHypothesis ⊢
      rw [inductionHypothesis]
      ring1

namespace EffectiveNull

/-- Finite box cells requested for a bounded nonnegative upper-sum test on
an effectively null predicate. -/
def requestedBoundedCells {predicate : Gaussian → Prop}
    (null : EffectiveNull predicate) (ceiling : Coordinate)
    (ceilingPositive : 0 < ceiling) (target : Coordinate)
    (targetPositive : 0 < target) : List BoxIntegrationCell :=
  let coverTarget := target / ceiling
  let coverTargetPositive := RFAP.ConstructiveFraction.div_pos_direct
    targetPositive ceilingPositive
  coverRangeCells (null.request coverTarget coverTargetPositive)
    0 ceiling (RFAP.ConstructiveFraction.le_of_lt_direct ceilingPositive)

/-- The boxes underlying a requested bounded-cell list cover the supplied
null predicate. -/
theorem requestedBoundedCells_cover {predicate : Gaussian → Prop}
    (null : EffectiveNull predicate) (ceiling : Coordinate)
    (ceilingPositive : 0 < ceiling) (target : Coordinate)
    (targetPositive : 0 < target) :
    (null.request (target / ceiling)
      (RFAP.ConstructiveFraction.div_pos_direct targetPositive
        ceilingPositive)).Covers predicate :=
  null.covers _ _

/-- Every positive rational tolerance yields a finite cover whose complete
bounded upper box sum lies below that tolerance. -/
theorem requestedBoundedCells_upper_lt {predicate : Gaussian → Prop}
    (null : EffectiveNull predicate) (ceiling : Coordinate)
    (ceilingPositive : 0 < ceiling) (target : Coordinate)
    (targetPositive : 0 < target) :
    _root_.FiniteMeasure.upperIntegral
        (boxIntegrationCells
          (null.requestedBoundedCells ceiling ceilingPositive
            target targetPositive)) < target := by
  let coverTarget := target / ceiling
  have coverTargetPositive : (0 : Coordinate) < coverTarget :=
    RFAP.ConstructiveFraction.div_pos_direct targetPositive ceilingPositive
  let cover := null.request coverTarget coverTargetPositive
  change _root_.FiniteMeasure.upperIntegral
      (boxIntegrationCells
        (coverRangeCells cover 0 ceiling
          (RFAP.ConstructiveFraction.le_of_lt_direct ceilingPositive))) < target
  rw [upperIntegral_coverRangeCells]
  have small := null.small coverTarget coverTargetPositive
  have scaled :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      small ceilingPositive
  calc
    cover.content * ceiling < coverTarget * ceiling := scaled
    _ = target :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne target ceiling
        ceilingPositive.ne'

end EffectiveNull

end RFAP.FiniteMeasure
