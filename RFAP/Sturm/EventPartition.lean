import mathlib.Tactic.QuotientFreeRing
import RFAP.Cauchy.Resolution
import RFAP.Sturm.RootCount

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

namespace RFAP.SturmEventPartition

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Interval := RFAP.PathClearance.Interval
abbrev CauchyEventSigns := RFAP.CauchyCells.CauchyEventSigns

open RFAP.PathClearance
open RFAP.IntervalSign
open RFAP.SturmRootCount

namespace Interval

def width (interval : Interval) : Coordinate :=
  interval.upper - interval.lower

theorem width_nonneg (interval : Interval) : 0 ≤ interval.width :=
  RFAP.ConstructiveFraction.sub_nonneg_direct interval.valid

theorem width_pos {interval : Interval}
    (proper : interval.lower < interval.upper) : 0 < interval.width :=
  RFAP.ConstructiveFraction.sub_pos_direct proper

def leftChild (interval : Interval) (cut : Coordinate)
    (lowerLe : interval.lower ≤ cut) : Interval :=
  ⟨interval.lower, cut, lowerLe⟩

def rightChild (interval : Interval) (cut : Coordinate)
    (upperLe : cut ≤ interval.upper) : Interval :=
  ⟨cut, interval.upper, upperLe⟩

@[simp] theorem leftChild_width
    (interval : Interval) (cut : Coordinate)
    (lowerLe : interval.lower ≤ cut) :
    (interval.leftChild cut lowerLe).width = cut - interval.lower := rfl

@[simp] theorem rightChild_width
    (interval : Interval) (cut : Coordinate)
    (upperLe : cut ≤ interval.upper) :
    (interval.rightChild cut upperLe).width = interval.upper - cut := rfl

theorem leftChild_refines
    (interval : Interval) (cut : Coordinate)
    (lowerLe : interval.lower ≤ cut) (upperLe : cut ≤ interval.upper) :
    (interval.leftChild cut lowerLe).Refines interval :=
  ⟨le_rfl, upperLe⟩

theorem rightChild_refines
    (interval : Interval) (cut : Coordinate)
    (lowerLe : interval.lower ≤ cut) (upperLe : cut ≤ interval.upper) :
    (interval.rightChild cut upperLe).Refines interval :=
  ⟨lowerLe, le_rfl⟩

end Interval

/-- One proper rational parameter cell. -/
structure Cell where
  interval : Interval
  proper : interval.lower < interval.upper

namespace Cell

def left (cell : Cell) (cut : Coordinate)
    (lowerLt : cell.interval.lower < cut) : Cell :=
  { interval := cell.interval.leftChild cut lowerLt.le
    proper := lowerLt }

def right (cell : Cell) (cut : Coordinate)
    (upperLt : cut < cell.interval.upper) : Cell :=
  { interval := cell.interval.rightChild cut upperLt.le
    proper := upperLt }

end Cell

/-- Proof-bearing safe split of one parameter cell. -/
structure SafeSplit (numerator denominator : Polynomial) (cell : Cell) where
  cut : Coordinate
  lowerLt : cell.interval.lower < cut
  upperLt : cut < cell.interval.upper
  guardNonzero : (chainGuard numerator denominator).eval cut ≠ 0
  leftContracts :
    cut - cell.interval.lower < (2 / 3 : Coordinate) * cell.interval.width
  rightContracts :
    cell.interval.upper - cut < (2 / 3 : Coordinate) * cell.interval.width

namespace SafeSplit

def leftCell {numerator denominator : Polynomial} {cell : Cell}
    (split : SafeSplit numerator denominator cell) : Cell :=
  cell.left split.cut split.lowerLt

def rightCell {numerator denominator : Polynomial} {cell : Cell}
    (split : SafeSplit numerator denominator cell) : Cell :=
  cell.right split.cut split.upperLt

end SafeSplit

def safeSplit
    (numerator denominator : Polynomial)
    (denominatorNonzero : denominator.isZero = false)
    (cell : Cell) : SafeSplit numerator denominator cell := by
  let cut := RFAP.SturmRootCount.safeCut numerator denominator
    denominatorNonzero cell.interval cell.proper
  have specification :=
    RFAP.SturmRootCount.safeCut_spec numerator denominator
      denominatorNonzero cell.interval cell.proper
  have contraction :=
    RFAP.SturmRootCount.safeCut_contraction numerator denominator
      denominatorNonzero cell.interval cell.proper
  exact
    { cut := cut
      lowerLt := specification.2.1
      upperLt := specification.2.2
      guardNonzero := specification.1
      leftContracts := contraction.1
      rightContracts := contraction.2 }

/-- Finite binary subdivision syntax.  Cells and cut certificates are stored
explicitly instead of in dependent indices, keeping elaboration inexpensive. -/
inductive Subdivision (numerator denominator : Polynomial) where
  | leaf (cell : Cell)
  | split (cell : Cell) (data : SafeSplit numerator denominator cell)
      (left right : Subdivision numerator denominator)

namespace Subdivision

/-- Execute exactly the requested number of safe central-third rounds. -/
def build
    (numerator denominator : Polynomial)
    (denominatorNonzero : denominator.isZero = false) :
    Nat → Cell → Subdivision numerator denominator
  | 0, cell => .leaf cell
  | depth + 1, cell =>
      let data := safeSplit numerator denominator denominatorNonzero cell
      .split cell data
        (build numerator denominator denominatorNonzero depth data.leftCell)
        (build numerator denominator denominatorNonzero depth data.rightCell)

def leaves {numerator denominator : Polynomial} :
    Subdivision numerator denominator → List Cell
  | .leaf cell => [cell]
  | .split _ _ left right => left.leaves ++ right.leaves

theorem build_leaf_refines
    (numerator denominator : Polynomial)
    (denominatorNonzero : denominator.isZero = false)
    (depth : Nat) (root : Cell) {leaf : Cell}
    (member : leaf ∈
      (build numerator denominator denominatorNonzero depth root).leaves) :
    leaf.interval.Refines root.interval := by
  induction depth generalizing root with
  | zero =>
      simp only [build, leaves, List.mem_singleton] at member
      subst leaf
      exact ⟨le_rfl, le_rfl⟩
  | succ depth inductionHypothesis =>
      let data := safeSplit numerator denominator denominatorNonzero root
      change leaf ∈
        (build numerator denominator denominatorNonzero depth data.leftCell).leaves ++
          (build numerator denominator denominatorNonzero depth
            data.rightCell).leaves at member
      rw [List.mem_append] at member
      rcases member with leftMember | rightMember
      · have leafChild := inductionHypothesis data.leftCell leftMember
        have childRoot := root.interval.leftChild_refines data.cut
          data.lowerLt.le data.upperLt.le
        exact ⟨childRoot.1.trans leafChild.1,
          leafChild.2.trans childRoot.2⟩
      · have leafChild := inductionHypothesis data.rightCell rightMember
        have childRoot := root.interval.rightChild_refines data.cut
          data.lowerLt.le data.upperLt.le
        exact ⟨childRoot.1.trans leafChild.1,
          leafChild.2.trans childRoot.2⟩

/-- Every leaf built at a requested depth is at most the fixed `2/3`
contraction power times the initial width. -/
theorem build_leaf_width_le
    (numerator denominator : Polynomial)
    (denominatorNonzero : denominator.isZero = false)
    (depth : Nat) (root : Cell) {leaf : Cell}
    (member : leaf ∈
      (build numerator denominator denominatorNonzero depth root).leaves) :
    leaf.interval.width ≤
      (2 / 3 : Coordinate) ^ depth * root.interval.width := by
  induction depth generalizing root with
  | zero =>
      simp only [build, leaves, List.mem_singleton] at member
      subst leaf
      simp only [pow_zero, one_mul]
      exact le_rfl
  | succ depth inductionHypothesis =>
      let data := safeSplit numerator denominator denominatorNonzero root
      change leaf ∈
        (build numerator denominator denominatorNonzero depth data.leftCell).leaves ++
          (build numerator denominator denominatorNonzero depth
            data.rightCell).leaves at member
      rw [List.mem_append] at member
      have powerPositive : 0 < (2 / 3 : Coordinate) ^ depth :=
        RFAP.ConstructiveFraction.pow_pos_direct (by decide) depth
      rcases member with leftMember | rightMember
      · exact (calc
          leaf.interval.width ≤
              (2 / 3 : Coordinate) ^ depth * data.leftCell.interval.width :=
            inductionHypothesis data.leftCell leftMember
          _ < (2 / 3 : Coordinate) ^ depth *
                ((2 / 3 : Coordinate) * root.interval.width) :=
            RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
              powerPositive data.leftContracts
          _ = (2 / 3 : Coordinate) ^ Nat.succ depth *
                root.interval.width := by
            rw [pow_succ]
            ring1
        ).le
      · exact (calc
          leaf.interval.width ≤
              (2 / 3 : Coordinate) ^ depth * data.rightCell.interval.width :=
            inductionHypothesis data.rightCell rightMember
          _ < (2 / 3 : Coordinate) ^ depth *
                ((2 / 3 : Coordinate) * root.interval.width) :=
            RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
              powerPositive data.rightContracts
          _ = (2 / 3 : Coordinate) ^ Nat.succ depth *
                root.interval.width := by
            rw [pow_succ]
            ring1
        ).le

end Subdivision

/-! ## Coefficient-computed event resolution -/

def reducedClearance
    (numerator denominator : Polynomial) (root : Cell) :
    RFAP.PathClearance.Certificate
      (reducedDenominator numerator denominator)
      (reducedNumerator numerator denominator) root.interval :=
  RFAP.PathClearance.certificateOfCoprime
    (reducedPairCoprime numerator denominator) root.interval

def resolutionRadiusSq
    (numerator denominator : Polynomial) (root : Cell) : Coordinate :=
  RFAP.CauchyResolution.signedChainResolutionRadiusSq
    (reducedDenominator numerator denominator)
    (reducedNumerator numerator denominator)
    (reducedClearance numerator denominator root)

theorem resolutionRadiusSq_pos
    (numerator denominator : Polynomial) (root : Cell) :
    0 < resolutionRadiusSq numerator denominator root :=
  RFAP.CauchyResolution.signedChainResolutionRadiusSq_pos
    (reducedDenominator numerator denominator)
    (reducedNumerator numerator denominator)
    (reducedClearance numerator denominator root)

/-- Width threshold that turns an unsquared interval estimate into the
squared-radius estimate consumed by the finite event scanner. -/
def eventLeafWidth
    (numerator denominator : Polynomial) (root : Cell) : Coordinate :=
  min 1 (resolutionRadiusSq numerator denominator root)

theorem eventLeafWidth_pos
    (numerator denominator : Polynomial) (root : Cell) :
    0 < eventLeafWidth numerator denominator root :=
  lt_min (by decide) (resolutionRadiusSq_pos numerator denominator root)

theorem sampleRadiusSq_lt_of_width_lt
    {interval : Interval} (proper : interval.lower < interval.upper)
    {radiusBound : Coordinate}
    (widthSmall : interval.width < min 1 radiusBound) :
    RFAP.IntervalSign.sampleRadiusSq interval interval.lower <
      radiusBound := by
  let width := interval.width
  have widthPositive : 0 < width := Interval.width_pos proper
  have widthBelowOne : width < 1 :=
    widthSmall.trans_le (min_le_left _ _)
  have widthBelowRadius : width < radiusBound :=
    widthSmall.trans_le (min_le_right _ _)
  have squareBelowWidth : width ^ 2 < width := by
    have multiplied :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
        widthBelowOne widthPositive
    simpa only [pow_two, one_mul] using multiplied
  rw [RFAP.IntervalSign.sampleRadiusSq_lower_eq_widthSq]
  exact squareBelowWidth.trans widthBelowRadius

def eventDepth
    (numerator denominator : Polynomial) (root : Cell) : Nat :=
  RFAP.SafeCandidates.geometricDepth root.interval.width
    (eventLeafWidth numerator denominator root / 2)

def eventSubdivision
    (numerator denominator : Polynomial)
    (denominatorNonzero : denominator.isZero = false)
    (root : Cell) : Subdivision numerator denominator :=
  Subdivision.build numerator denominator denominatorNonzero
    (eventDepth numerator denominator root) root

theorem eventSubdivision_leaf_refines
    (numerator denominator : Polynomial)
    (denominatorNonzero : denominator.isZero = false)
    (root leaf : Cell)
    (member : leaf ∈
      (eventSubdivision numerator denominator denominatorNonzero root).leaves) :
    leaf.interval.Refines root.interval := by
  exact Subdivision.build_leaf_refines numerator denominator
    denominatorNonzero (eventDepth numerator denominator root) root member

theorem eventSubdivision_leaf_width_lt
    (numerator denominator : Polynomial)
    (denominatorNonzero : denominator.isZero = false)
    (root leaf : Cell)
    (member : leaf ∈
      (eventSubdivision numerator denominator denominatorNonzero root).leaves) :
    leaf.interval.width < eventLeafWidth numerator denominator root := by
  let leafWidth := eventLeafWidth numerator denominator root
  have leafWidthPositive : 0 < leafWidth := by
    simpa only [leafWidth] using
      eventLeafWidth_pos numerator denominator root
  have geometric :=
    RFAP.SafeCandidates.geometricDepth_sufficient
      (width := root.interval.width) (epsilon := leafWidth / 2)
      root.interval.width_nonneg
      (RFAP.ConstructiveFraction.div_pos_direct leafWidthPositive
        (show (0 : Coordinate) < 2 by decide))
  have geometric' :
      (2 / 3 : Coordinate) ^ eventDepth numerator denominator root *
          root.interval.width ≤ leafWidth / 2 := by
    simpa only [eventDepth] using geometric
  have halfBelow : leafWidth / 2 < leafWidth := by
    have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      (show (1 / 2 : Coordinate) < 1 by decide) leafWidthPositive
    rw [RFAP.ExplicitField.div_eq_mul_inv]
    have halfInverse : (2 : Coordinate)⁻¹ = 1 / 2 := by
      rw [RFAP.ExplicitField.div_eq_mul_inv]
      exact (RFAP.ConstructiveFraction.one_mul _).symm
    rw [halfInverse]
    simpa only [RFAP.ConstructiveFraction.mul_comm, one_mul] using scaled
  exact (Subdivision.build_leaf_width_le numerator denominator
    denominatorNonzero (eventDepth numerator denominator root) root member).trans_lt
      (geometric'.trans_lt halfBelow)

/-- Every leaf of the coefficient-computed subdivision carries a total finite
sign record for the complete gcd-reduced Cauchy--Sturm chain. -/
def leafEvent
    (numerator denominator : Polynomial)
    (denominatorNonzero : denominator.isZero = false)
    (root leaf : Cell)
    (member : leaf ∈
      (eventSubdivision numerator denominator denominatorNonzero root).leaves) :
    CauchyEventSigns (reducedNumerator numerator denominator)
      (reducedDenominator numerator denominator) leaf.interval :=
  RFAP.CauchyResolution.cauchyEventSignsOfRefinedRadiusSq
    (reducedClearance numerator denominator root)
    (eventSubdivision_leaf_refines numerator denominator denominatorNonzero
      root leaf member)
    (sampleRadiusSq_lt_of_width_lt leaf.proper
      (eventSubdivision_leaf_width_lt numerator denominator denominatorNonzero
        root leaf member))

/-- The finite event partition packages its executable safe-cut tree together
with the total classifier for every emitted leaf. -/
structure EventPartition
    (numerator denominator : Polynomial) (root : Cell) where
  tree : Subdivision numerator denominator
  classify : (leaf : Cell) → leaf ∈ tree.leaves →
    CauchyEventSigns (reducedNumerator numerator denominator)
      (reducedDenominator numerator denominator) leaf.interval

def classifyEvents
    (numerator denominator : Polynomial)
    (denominatorNonzero : denominator.isZero = false)
    (root : Cell) : EventPartition numerator denominator root where
  tree := eventSubdivision numerator denominator denominatorNonzero root
  classify := leafEvent numerator denominator denominatorNonzero root

/-! ## Telescoping the classified leaves -/

def cellIndex2
    (numerator denominator : Polynomial) (cell : Cell) : Int :=
  reducedCauchyIndex2 numerator denominator
    cell.interval.lower cell.interval.upper

theorem build_cellIndex2_sum
    (numerator denominator : Polynomial)
    (denominatorNonzero : denominator.isZero = false)
    (depth : Nat) (root : Cell) :
    cellIndex2 numerator denominator root =
      ((Subdivision.build numerator denominator denominatorNonzero depth root).leaves.map
        (cellIndex2 numerator denominator)).sum := by
  induction depth generalizing root with
  | zero => simp [Subdivision.build, Subdivision.leaves]
  | succ depth inductionHypothesis =>
      let data := safeSplit numerator denominator denominatorNonzero root
      have splitIndex : cellIndex2 numerator denominator root =
          cellIndex2 numerator denominator data.leftCell +
            cellIndex2 numerator denominator data.rightCell := by
        unfold cellIndex2
        simpa only [SafeSplit.leftCell, SafeSplit.rightCell, Cell.left,
          Cell.right, Interval.leftChild, Interval.rightChild] using
          reducedCauchyIndex2_add numerator denominator root.interval.lower
            data.cut root.interval.upper
      rw [splitIndex, inductionHypothesis data.leftCell,
        inductionHypothesis data.rightCell]
      simp only [Subdivision.build, Subdivision.leaves, List.map_append,
        List.sum_append, data]

def eventIndex2
    {R S : Polynomial} {interval : Interval}
    (event : CauchyEventSigns R S interval) : Int :=
  event.numerator.eventIndex2 event.denominator
    (RFAP.CauchyProductSigns.FiniteSign.ofCoordinate
      (R.eval interval.lower))
    (RFAP.CauchyProductSigns.FiniteSign.ofCoordinate
      (S.eval interval.lower))
    (RFAP.CauchyProductSigns.FiniteSign.ofCoordinate
      (R.eval interval.upper))
    (RFAP.CauchyProductSigns.FiniteSign.ofCoordinate
      (S.eval interval.upper))

theorem leafEvent_index2
    (numerator denominator : Polynomial)
    (denominatorNonzero : denominator.isZero = false)
    (root leaf : Cell)
    (member : leaf ∈
      (eventSubdivision numerator denominator denominatorNonzero root).leaves) :
    cellIndex2 numerator denominator leaf =
      eventIndex2
        (leafEvent numerator denominator denominatorNonzero root leaf member) := by
  unfold cellIndex2 reducedCauchyIndex2 eventIndex2
  exact (leafEvent numerator denominator denominatorNonzero
    root leaf member).index

theorem eventSubdivision_cellIndex2_sum
    (numerator denominator : Polynomial)
    (denominatorNonzero : denominator.isZero = false)
    (root : Cell) :
    cellIndex2 numerator denominator root =
      ((eventSubdivision numerator denominator denominatorNonzero root).leaves.map
        (cellIndex2 numerator denominator)).sum :=
  build_cellIndex2_sum numerator denominator denominatorNonzero
    (eventDepth numerator denominator root) root

end RFAP.SturmEventPartition
