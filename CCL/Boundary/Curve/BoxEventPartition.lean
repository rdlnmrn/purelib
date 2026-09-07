import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import CCL.Boundary.Curve.BoxConditions
import CCL.Boundary.Curve.CoordinateTaylor
import RFAP.Sturm.NonzeroEvent

/-!
# Common finite event partitions for curve roots and box edges

The root-event polynomial of a boundary chart and the four cleared box-edge
polynomials must be classified on the same parameter cells.  This module
forms one product of their complete reduced-chain guards, uses it for every
central-third cut, and chooses a coefficient-computed depth below all of the
individual event-resolution widths.

Consequently every emitted leaf has, simultaneously:

* a finite Cauchy--Sturm event record for the chart root polynomial; and
* a finite event record for every nontrivial box-edge condition.

Identically-zero box conditions are retained separately by
`CurveBoxConditions.condition_zero_or_active`; they never make
the common cut guard vanish.
-/

namespace CCL.CurveBoxEventPartition

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev RationalCurve := CCL.RationalCurve.RationalCurve
abbrev Box := RFAP.Boxes.Box
abbrev Cell := RFAP.SturmEventPartition.Cell
abbrev Interval := RFAP.PathClearance.Interval
abbrev CauchyEventSigns := RFAP.CauchyCells.CauchyEventSigns
abbrev CauchyEventResolution :=
  RFAP.CauchyCells.CauchyEventResolution

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.SturmRootCount

/-- Complete reduced-chain guard for the Sturm count of one polynomial. -/
def polynomialEventGuard (polynomial : Polynomial) : Polynomial :=
  chainGuard (RFAP.ComputableDerivative.derivative polynomial) polynomial

theorem polynomialEventGuard_isZero_false
    {polynomial : Polynomial} (nonzero : polynomial.isZero = false) :
    (polynomialEventGuard polynomial).isZero = false :=
  chainGuard_isZero_false nonzero

/-- The main chart-root guard followed by every nontrivial box-condition
guard. -/
def eventGuards
    (event : Polynomial) (curve : RationalCurve) (box : Box) :
    List Polynomial :=
  polynomialEventGuard event ::
    (CCL.CurveBoxConditions.activeConditionPolynomials curve box).map
      polynomialEventGuard

theorem eventGuards_all_nonzero
    {event : Polynomial} (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box) :
    (eventGuards event curve box).Forall fun guard => guard.isZero = false := by
  rw [eventGuards, List.forall_cons]
  constructor
  · exact polynomialEventGuard_isZero_false eventNonzero
  · rw [List.forall_iff_forall_mem]
    intro guard member
    rw [QuotientFreeList.mem_map] at member
    rcases member with ⟨condition, conditionMember, rfl⟩
    exact polynomialEventGuard_isZero_false
      (of_decide_eq_true (List.mem_filter.mp conditionMember).2)

/-- One nonzero product guard for all aligned root and box-edge event
classifiers. -/
def commonGuard
    (event : Polynomial) (curve : RationalCurve) (box : Box) : Polynomial :=
  polynomialProduct (eventGuards event curve box)

theorem commonGuard_isZero_false
    {event : Polynomial} (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box) :
    (commonGuard event curve box).isZero = false :=
  polynomialProduct_isZero_false
    (eventGuards_all_nonzero eventNonzero curve box)

theorem eval_ne_zero_of_eventGuard
    {event : Polynomial} {curve : RationalCurve} {box : Box}
    {guard : Polynomial} {parameter : Coordinate}
    (member : guard ∈ eventGuards event curve box)
    (commonNonzero : (commonGuard event curve box).eval parameter ≠ 0) :
    guard.eval parameter ≠ 0 :=
  eval_ne_zero_of_mem_of_polynomialProduct member commonNonzero

/-- One common safe split.  Its cut avoids every member of every reduced
chain used by the aligned classifiers. -/
structure SafeSplit
    (event : Polynomial) (curve : RationalCurve) (box : Box) (cell : Cell) where
  cut : Coordinate
  lowerLt : cell.interval.lower < cut
  upperLt : cut < cell.interval.upper
  guardNonzero : (commonGuard event curve box).eval cut ≠ 0
  leftContracts :
    cut - cell.interval.lower <
      (2 / 3 : Coordinate) * cell.interval.width
  rightContracts :
    cell.interval.upper - cut <
      (2 / 3 : Coordinate) * cell.interval.width

namespace SafeSplit

def leftCell
    {event : Polynomial} {curve : RationalCurve} {box : Box} {cell : Cell}
    (split : SafeSplit event curve box cell) : Cell :=
  cell.left split.cut split.lowerLt

def rightCell
    {event : Polynomial} {curve : RationalCurve} {box : Box} {cell : Cell}
    (split : SafeSplit event curve box cell) : Cell :=
  cell.right split.cut split.upperLt

theorem avoidsEventGuard
    {event : Polynomial} {curve : RationalCurve} {box : Box} {cell : Cell}
    (split : SafeSplit event curve box cell) :
    (polynomialEventGuard event).eval split.cut ≠ 0 := by
  apply eval_ne_zero_of_eventGuard (event := event) (curve := curve) (box := box)
  · exact List.mem_cons_self
  · exact split.guardNonzero

theorem avoidsActiveConditionGuard
    {event : Polynomial} {curve : RationalCurve} {box : Box} {cell : Cell}
    (split : SafeSplit event curve box cell) {condition : Polynomial}
    (member : condition ∈
      CCL.CurveBoxConditions.activeConditionPolynomials curve box) :
    (polynomialEventGuard condition).eval split.cut ≠ 0 := by
  apply eval_ne_zero_of_eventGuard (event := event) (curve := curve) (box := box)
  · exact List.mem_cons_of_mem _ (QuotientFreeList.mem_map.mpr ⟨condition, member, rfl⟩)
  · exact split.guardNonzero

end SafeSplit

def safeSplit
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box) (cell : Cell) :
    SafeSplit event curve box cell := by
  let guard := commonGuard event curve box
  let cut := RFAP.SafeCandidates.centralSearchValue guard
    guard.natDegree cell.proper
    (commonGuard_isZero_false eventNonzero curve box) (Nat.le_refl _)
  have specification :=
    RFAP.SafeCandidates.centralSearchValue_spec guard
      guard.natDegree cell.proper
      (commonGuard_isZero_false eventNonzero curve box) (Nat.le_refl _)
  have contraction :=
    RFAP.SafeCandidates.centralSearchValue_contraction guard
      guard.natDegree cell.proper
      (commonGuard_isZero_false eventNonzero curve box) (Nat.le_refl _)
  exact
    { cut := cut
      lowerLt := specification.2.1
      upperLt := specification.2.2
      guardNonzero := specification.1
      leftContracts := contraction.1
      rightContracts := contraction.2 }

/-- Finite common binary subdivision syntax. -/
inductive Subdivision
    (event : Polynomial) (curve : RationalCurve) (box : Box) where
  | leaf (cell : Cell)
  | split (cell : Cell) (data : SafeSplit event curve box cell)
      (left right : Subdivision event curve box)

namespace Subdivision

def build
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box) :
    Nat → Cell → Subdivision event curve box
  | 0, cell => .leaf cell
  | depth + 1, cell =>
      let data := safeSplit event eventNonzero curve box cell
      .split cell data
        (build event eventNonzero curve box depth data.leftCell)
        (build event eventNonzero curve box depth data.rightCell)

def leaves {event : Polynomial} {curve : RationalCurve} {box : Box} :
    Subdivision event curve box → List Cell
  | .leaf cell => [cell]
  | .split _ _ left right => left.leaves ++ right.leaves

theorem build_leaf_refines
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box)
    (depth : Nat) (root : Cell) {leaf : Cell}
    (member : leaf ∈
      (build event eventNonzero curve box depth root).leaves) :
    leaf.interval.Refines root.interval := by
  induction depth generalizing root with
  | zero =>
      simp only [build, leaves, List.mem_singleton] at member
      subst leaf
      exact ⟨le_rfl, le_rfl⟩
  | succ depth inductionHypothesis =>
      let data := safeSplit event eventNonzero curve box root
      change leaf ∈
        (build event eventNonzero curve box depth data.leftCell).leaves ++
          (build event eventNonzero curve box depth data.rightCell).leaves
        at member
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

theorem build_leaf_width_le
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box)
    (depth : Nat) (root : Cell) {leaf : Cell}
    (member : leaf ∈
      (build event eventNonzero curve box depth root).leaves) :
    leaf.interval.width ≤
      (2 / 3 : Coordinate) ^ depth * root.interval.width := by
  induction depth generalizing root with
  | zero =>
      simp only [build, leaves, List.mem_singleton] at member
      subst leaf
      simp only [pow_zero, one_mul]
      exact le_rfl
  | succ depth inductionHypothesis =>
      let data := safeSplit event eventNonzero curve box root
      change leaf ∈
        (build event eventNonzero curve box depth data.leftCell).leaves ++
          (build event eventNonzero curve box depth data.rightCell).leaves
        at member
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

/-- The doubled root-event count of one parameter cell. -/
def cellEventCount (event : Polynomial) (cell : Cell) : Int :=
  sturmRootCount2 event cell.interval.lower cell.interval.upper

/-- Additivity of the doubled Sturm count across every common subdivision.
The common cuts were chosen for all aligned classifiers, but the count
identity itself is the exact finite endpoint telescoping law. -/
theorem build_cellEventCount_sum
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box)
    (depth : Nat) (root : Cell) :
    cellEventCount event root =
      ((build event eventNonzero curve box depth root).leaves.map
        (cellEventCount event)).sum := by
  induction depth generalizing root with
  | zero => simp [build, leaves]
  | succ depth inductionHypothesis =>
      let data := safeSplit event eventNonzero curve box root
      have splitCount : cellEventCount event root =
          cellEventCount event data.leftCell +
            cellEventCount event data.rightCell := by
        unfold cellEventCount
        change sturmRootCount2 event root.interval.lower root.interval.upper =
          sturmRootCount2 event root.interval.lower data.cut +
            sturmRootCount2 event data.cut root.interval.upper
        exact sturmRootCount2_add event root.interval.lower data.cut
          root.interval.upper
      rw [splitCount, inductionHypothesis data.leftCell,
        inductionHypothesis data.rightCell]
      simp only [build, leaves, List.map_append, List.sum_append, data]

/-- Proof-bearing result of the deterministic leaf-location program.  The
build indices are retained without first reducing the full tree in the
result type, keeping ordinary elaboration limits sufficient. -/
structure BuildLocation
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box)
    (depth : Nat) (root : Cell) (parameter : Coordinate) where
  leaf : Cell
  member : leaf ∈ (build event eventNonzero curve box depth root).leaves
  contains : leaf.interval.Contains parameter

/-- Locate a displayed parameter by following the common finite tree.
Parameters equal to a cut are owned by the left child; this fixed convention
prevents endpoint events from being duplicated. -/
def locateBuild
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box)
    (depth : Nat) (root : Cell) (parameter : Coordinate)
    (inside : root.interval.Contains parameter) :
    BuildLocation event eventNonzero curve box depth root parameter := by
  induction depth generalizing root with
  | zero => exact ⟨root, by simp [build, leaves], inside⟩
  | succ depth inductionHypothesis =>
      let data := safeSplit event eventNonzero curve box root
      by_cases left : parameter ≤ data.cut
      · let found := inductionHypothesis data.leftCell ⟨inside.1, left⟩
        exact ⟨found.leaf, by
          change found.leaf ∈
            (build event eventNonzero curve box depth data.leftCell).leaves ++
              (build event eventNonzero curve box depth data.rightCell).leaves
          exact List.mem_append_left _ found.member,
          found.contains⟩
      · have cutLower : data.cut ≤ parameter := (lt_of_not_ge left).le
        let found := inductionHypothesis data.rightCell ⟨cutLower, inside.2⟩
        exact ⟨found.leaf, by
          change found.leaf ∈
            (build event eventNonzero curve box depth data.leftCell).leaves ++
              (build event eventNonzero curve box depth data.rightCell).leaves
          exact List.mem_append_right _ found.member,
          found.contains⟩

/-- Proposition-level coverage corollary of the executable locator. -/
theorem build_covers
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box)
    (depth : Nat) (root : Cell) (parameter : Coordinate)
    (inside : root.interval.Contains parameter) :
    ∃ leaf,
      leaf ∈ (build event eventNonzero curve box depth root).leaves ∧
        leaf.interval.Contains parameter := by
  let found := locateBuild event eventNonzero curve box depth root
    parameter inside
  exact ⟨found.leaf, found.member, found.contains⟩

end Subdivision

/-! ## One coefficient-computed common resolution -/

def positiveMinimum (values : List Coordinate) : Coordinate :=
  values.foldr min 1

theorem positiveMinimum_pos (values : List Coordinate)
    (positive : ∀ value ∈ values, 0 < value) :
    0 < positiveMinimum values := by
  induction values with
  | nil => exact (by decide)
  | cons head tail inductionHypothesis =>
      rw [positiveMinimum, List.foldr_cons]
      exact lt_min (positive head (by simp))
        (inductionHypothesis fun value member =>
          positive value (by simp [member]))

theorem positiveMinimum_le_of_mem
    {values : List Coordinate} {value : Coordinate}
    (member : value ∈ values) : positiveMinimum values ≤ value := by
  induction values with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      rw [positiveMinimum, List.foldr_cons]
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans
          (inductionHypothesis tailMember)

def eventLeafWidth (polynomial : Polynomial) (root : Cell) : Coordinate :=
  RFAP.SturmEventPartition.eventLeafWidth
    (RFAP.ComputableDerivative.derivative polynomial) polynomial root

theorem eventLeafWidth_pos (polynomial : Polynomial) (root : Cell) :
    0 < eventLeafWidth polynomial root :=
  RFAP.SturmEventPartition.eventLeafWidth_pos
    (RFAP.ComputableDerivative.derivative polynomial) polynomial root

def conditionLeafWidths
    (curve : RationalCurve) (box : Box) (root : Cell) : List Coordinate :=
  (CCL.CurveBoxConditions.activeConditionPolynomials curve box).map
    fun polynomial => eventLeafWidth polynomial root

def commonLeafWidth
    (event : Polynomial) (curve : RationalCurve) (box : Box) (root : Cell) :
    Coordinate :=
  min (eventLeafWidth event root)
    (positiveMinimum (conditionLeafWidths curve box root))

theorem commonLeafWidth_pos
    (event : Polynomial) (curve : RationalCurve) (box : Box) (root : Cell) :
    0 < commonLeafWidth event curve box root := by
  apply lt_min (eventLeafWidth_pos event root)
  apply positiveMinimum_pos
  intro width member
  rw [conditionLeafWidths, QuotientFreeList.mem_map] at member
  rcases member with ⟨polynomial, _polynomialMember, rfl⟩
  exact eventLeafWidth_pos polynomial root

theorem commonLeafWidth_le_event
    (event : Polynomial) (curve : RationalCurve) (box : Box) (root : Cell) :
    commonLeafWidth event curve box root ≤ eventLeafWidth event root :=
  min_le_left _ _

theorem commonLeafWidth_le_condition
    (event : Polynomial) {curve : RationalCurve} {box : Box} (root : Cell)
    {condition : Polynomial}
    (member : condition ∈
      CCL.CurveBoxConditions.activeConditionPolynomials curve box) :
    commonLeafWidth event curve box root ≤ eventLeafWidth condition root := by
  exact (min_le_right _ _).trans (positiveMinimum_le_of_mem
    (QuotientFreeList.mem_map.mpr ⟨condition, member, rfl⟩))

def commonDepth
    (event : Polynomial) (curve : RationalCurve) (box : Box) (root : Cell) :
    Nat :=
  RFAP.SafeCandidates.geometricDepth root.interval.width
    (commonLeafWidth event curve box root / 2)

def commonSubdivision
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box) (root : Cell) :
    Subdivision event curve box :=
  Subdivision.build event eventNonzero curve box
    (commonDepth event curve box root) root

theorem commonSubdivision_leaf_refines
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box) (root leaf : Cell)
    (member : leaf ∈
      (commonSubdivision event eventNonzero curve box root).leaves) :
    leaf.interval.Refines root.interval :=
  Subdivision.build_leaf_refines event eventNonzero curve box
    (commonDepth event curve box root) root member

theorem commonSubdivision_leaf_width_lt
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box) (root leaf : Cell)
    (member : leaf ∈
      (commonSubdivision event eventNonzero curve box root).leaves) :
    leaf.interval.width < commonLeafWidth event curve box root := by
  let leafWidth := commonLeafWidth event curve box root
  have leafWidthPositive : 0 < leafWidth := by
    simpa only [leafWidth] using commonLeafWidth_pos event curve box root
  have geometric :=
    RFAP.SafeCandidates.geometricDepth_sufficient
      (width := root.interval.width) (epsilon := leafWidth / 2)
      root.interval.width_nonneg
      (RFAP.ConstructiveFraction.div_pos_direct leafWidthPositive
        (show (0 : Coordinate) < 2 by decide))
  have geometric' :
      (2 / 3 : Coordinate) ^ commonDepth event curve box root *
          root.interval.width ≤ leafWidth / 2 := by
    simpa only [commonDepth, leafWidth] using geometric
  have halfBelow : leafWidth / 2 < leafWidth := by
    have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      (show (1 / 2 : Coordinate) < 1 by decide) leafWidthPositive
    rw [RFAP.ExplicitField.div_eq_mul_inv]
    have halfInverse : (2 : Coordinate)⁻¹ = 1 / 2 := by
      rw [RFAP.ExplicitField.div_eq_mul_inv]
      exact (RFAP.ConstructiveFraction.one_mul _).symm
    rw [halfInverse]
    simpa only [RFAP.ConstructiveFraction.mul_comm, one_mul] using scaled
  exact (Subdivision.build_leaf_width_le event eventNonzero curve box
    (commonDepth event curve box root) root member).trans_lt
      (geometric'.trans_lt halfBelow)

theorem commonSubdivision_covers
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box) (root : Cell)
    (parameter : Coordinate) (inside : root.interval.Contains parameter) :
    ∃ leaf,
      leaf ∈ (commonSubdivision event eventNonzero curve box root).leaves ∧
        leaf.interval.Contains parameter :=
  Subdivision.build_covers event eventNonzero curve box
    (commonDepth event curve box root) root parameter inside

/-- The aligned common leaves preserve the exact parent curve-event count. -/
theorem commonSubdivision_eventCount_sum
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box) (root : Cell) :
    Subdivision.cellEventCount event root =
      ((commonSubdivision event eventNonzero curve box root).leaves.map
        (Subdivision.cellEventCount event)).sum :=
  Subdivision.build_cellEventCount_sum event eventNonzero curve box
    (commonDepth event curve box root) root

/-! ## Squarefree/Taylor refinement -/

abbrev SquarefreeCertificate (event : Polynomial) :=
  RFAP.PathClearance.CoprimeCertificate event
    (RFAP.ComputableDerivative.derivative event)

/-- The ordinary simultaneous event width, further restricted by the finite
Taylor orientation radius for the squarefree root-event polynomial. -/
def squarefreeLeafWidth
    (event : Polynomial) (squarefree : SquarefreeCertificate event)
    (curve : RationalCurve) (box : Box) (root : Cell) : Coordinate :=
  min (commonLeafWidth event curve box root)
    (CCL.CoordinateTaylor.rootOrientationWidth
      event squarefree root.interval)

theorem squarefreeLeafWidth_pos
    (event : Polynomial) (squarefree : SquarefreeCertificate event)
    (curve : RationalCurve) (box : Box) (root : Cell) :
    0 < squarefreeLeafWidth event squarefree curve box root :=
  lt_min (commonLeafWidth_pos event curve box root)
    (CCL.CoordinateTaylor.rootOrientationWidth_pos
      event squarefree root.interval)

theorem squarefreeLeafWidth_le_common
    (event : Polynomial) (squarefree : SquarefreeCertificate event)
    (curve : RationalCurve) (box : Box) (root : Cell) :
    squarefreeLeafWidth event squarefree curve box root ≤
      commonLeafWidth event curve box root :=
  min_le_left _ _

theorem squarefreeLeafWidth_le_orientation
    (event : Polynomial) (squarefree : SquarefreeCertificate event)
    (curve : RationalCurve) (box : Box) (root : Cell) :
    squarefreeLeafWidth event squarefree curve box root ≤
      CCL.CoordinateTaylor.rootOrientationWidth
        event squarefree root.interval :=
  min_le_right _ _

def squarefreeDepth
    (event : Polynomial) (squarefree : SquarefreeCertificate event)
    (curve : RationalCurve) (box : Box) (root : Cell) : Nat :=
  RFAP.SafeCandidates.geometricDepth root.interval.width
    (squarefreeLeafWidth event squarefree curve box root / 2)

def squarefreeSubdivision
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (squarefree : SquarefreeCertificate event)
    (curve : RationalCurve) (box : Box) (root : Cell) :
    Subdivision event curve box :=
  Subdivision.build event eventNonzero curve box
    (squarefreeDepth event squarefree curve box root) root

theorem squarefreeSubdivision_leaf_refines
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (squarefree : SquarefreeCertificate event)
    (curve : RationalCurve) (box : Box) (root leaf : Cell)
    (member : leaf ∈
      (squarefreeSubdivision event eventNonzero squarefree
        curve box root).leaves) :
    leaf.interval.Refines root.interval :=
  Subdivision.build_leaf_refines event eventNonzero curve box
    (squarefreeDepth event squarefree curve box root) root member

theorem squarefreeSubdivision_leaf_width_lt
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (squarefree : SquarefreeCertificate event)
    (curve : RationalCurve) (box : Box) (root leaf : Cell)
    (member : leaf ∈
      (squarefreeSubdivision event eventNonzero squarefree
        curve box root).leaves) :
    leaf.interval.width <
      squarefreeLeafWidth event squarefree curve box root := by
  let leafWidth := squarefreeLeafWidth event squarefree curve box root
  have leafWidthPositive : 0 < leafWidth := by
    simpa only [leafWidth] using
      squarefreeLeafWidth_pos event squarefree curve box root
  have geometric :=
    RFAP.SafeCandidates.geometricDepth_sufficient
      (width := root.interval.width) (epsilon := leafWidth / 2)
      root.interval.width_nonneg
      (RFAP.ConstructiveFraction.div_pos_direct leafWidthPositive
        (show (0 : Coordinate) < 2 by decide))
  have geometric' :
      (2 / 3 : Coordinate) ^
          squarefreeDepth event squarefree curve box root *
            root.interval.width ≤ leafWidth / 2 := by
    simpa only [squarefreeDepth, leafWidth] using geometric
  have halfBelow : leafWidth / 2 < leafWidth := by
    have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      (show (1 / 2 : Coordinate) < 1 by decide) leafWidthPositive
    rw [RFAP.ExplicitField.div_eq_mul_inv]
    have halfInverse : (2 : Coordinate)⁻¹ = 1 / 2 := by
      rw [RFAP.ExplicitField.div_eq_mul_inv]
      exact (RFAP.ConstructiveFraction.one_mul _).symm
    rw [halfInverse]
    simpa only [RFAP.ConstructiveFraction.mul_comm, one_mul] using scaled
  exact (Subdivision.build_leaf_width_le event eventNonzero curve box
    (squarefreeDepth event squarefree curve box root) root member).trans_lt
      (geometric'.trans_lt halfBelow)

/-- The finer squarefree leaves still telescope to the exact parent event
count. -/
theorem squarefreeSubdivision_eventCount_sum
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (squarefree : SquarefreeCertificate event)
    (curve : RationalCurve) (box : Box) (root : Cell) :
    Subdivision.cellEventCount event root =
      ((squarefreeSubdivision event eventNonzero squarefree
        curve box root).leaves.map
          (Subdivision.cellEventCount event)).sum :=
  Subdivision.build_cellEventCount_sum event eventNonzero curve box
    (squarefreeDepth event squarefree curve box root) root

/-! ## Simultaneous leaf classifiers -/

/-- Certificate-retaining resolution from explicit refinement and width
evidence.  This direct interface is shared by the ordinary common partition
and its finer squarefree/Taylor specialization. -/
def polynomialEventResolutionOfBounds
    (event : Polynomial) (root leaf : Cell)
    (refines : leaf.interval.Refines root.interval)
    (widthSmall : leaf.interval.width < eventLeafWidth event root) :
    CauchyEventResolution
      (reducedNumerator (RFAP.ComputableDerivative.derivative event) event)
      (reducedDenominator (RFAP.ComputableDerivative.derivative event) event)
      leaf.interval :=
  RFAP.CauchyResolution.cauchyEventResolutionOfRefinedRadiusSq
    (RFAP.SturmEventPartition.reducedClearance
      (RFAP.ComputableDerivative.derivative event) event root)
    refines
    (RFAP.SturmEventPartition.sampleRadiusSq_lt_of_width_lt
      leaf.proper widthSmall)

/-- Certificate-retaining resolution of the main curve-root event. -/
def polynomialEventResolution
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box) (root leaf : Cell)
    (member : leaf ∈
      (commonSubdivision event eventNonzero curve box root).leaves) :
    CauchyEventResolution
      (reducedNumerator (RFAP.ComputableDerivative.derivative event) event)
      (reducedDenominator (RFAP.ComputableDerivative.derivative event) event)
      leaf.interval :=
  polynomialEventResolutionOfBounds event root leaf
    (commonSubdivision_leaf_refines event eventNonzero curve box root leaf member)
    ((commonSubdivision_leaf_width_lt event eventNonzero curve box
      root leaf member).trans_le
        (commonLeafWidth_le_event event curve box root))

def polynomialEventSigns
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box) (root leaf : Cell)
    (member : leaf ∈
      (commonSubdivision event eventNonzero curve box root).leaves) :
    CauchyEventSigns
      (reducedNumerator (RFAP.ComputableDerivative.derivative event) event)
      (reducedDenominator (RFAP.ComputableDerivative.derivative event) event)
      leaf.interval :=
  (polynomialEventResolution event eventNonzero curve box root leaf member).signs

/-- One aligned event record for a nontrivial box-edge polynomial. -/
structure ConditionEvent
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box) (root leaf : Cell) where
  polynomial : Polynomial
  member : polynomial ∈
    CCL.CurveBoxConditions.activeConditionPolynomials curve box
  resolution : CauchyEventResolution
    (reducedNumerator (RFAP.ComputableDerivative.derivative polynomial)
      polynomial)
    (reducedDenominator (RFAP.ComputableDerivative.derivative polynomial)
      polynomial)
    leaf.interval

namespace ConditionEvent

def signs
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {curve : RationalCurve} {box : Box} {root leaf : Cell}
    (condition : ConditionEvent event eventNonzero curve box root leaf) :
    CauchyEventSigns
      (reducedNumerator
        (RFAP.ComputableDerivative.derivative condition.polynomial)
        condition.polynomial)
      (reducedDenominator
        (RFAP.ComputableDerivative.derivative condition.polynomial)
        condition.polynomial)
      leaf.interval :=
  condition.resolution.signs

end ConditionEvent

def conditionEvent
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box) (root leaf : Cell)
    (leafMember : leaf ∈
      (commonSubdivision event eventNonzero curve box root).leaves)
    (polynomial : Polynomial)
    (member : polynomial ∈
      CCL.CurveBoxConditions.activeConditionPolynomials curve box) :
    ConditionEvent event eventNonzero curve box root leaf where
  polynomial := polynomial
  member := member
  resolution :=
    polynomialEventResolutionOfBounds polynomial root leaf
      (commonSubdivision_leaf_refines event eventNonzero curve box
        root leaf leafMember)
      ((commonSubdivision_leaf_width_lt event eventNonzero
        curve box root leaf leafMember).trans_le
          (commonLeafWidth_le_condition event root member))

def conditionEvents
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box) (root leaf : Cell)
    (leafMember : leaf ∈
      (commonSubdivision event eventNonzero curve box root).leaves) :
    List (ConditionEvent event eventNonzero curve box root leaf) :=
  (CCL.CurveBoxConditions.activeConditionPolynomials curve box).attach.map
    fun entry => conditionEvent event eventNonzero curve box root leaf
      leafMember entry.1 entry.2

theorem conditionEvents_length
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box) (root leaf : Cell)
    (leafMember : leaf ∈
      (commonSubdivision event eventNonzero curve box root).leaves) :
    (conditionEvents event eventNonzero curve box root leaf leafMember).length =
      (CCL.CurveBoxConditions.activeConditionPolynomials
        curve box).length := by
  simp [conditionEvents]

/-! ## Exhaustive squarefree leaves -/

def squarefreeConditionEvent
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (squarefree : SquarefreeCertificate event)
    (curve : RationalCurve) (box : Box) (root leaf : Cell)
    (leafMember : leaf ∈
      (squarefreeSubdivision event eventNonzero squarefree
        curve box root).leaves)
    (polynomial : Polynomial)
    (member : polynomial ∈
      CCL.CurveBoxConditions.activeConditionPolynomials curve box) :
    ConditionEvent event eventNonzero curve box root leaf where
  polynomial := polynomial
  member := member
  resolution :=
    polynomialEventResolutionOfBounds polynomial root leaf
      (squarefreeSubdivision_leaf_refines event eventNonzero squarefree
        curve box root leaf leafMember)
      ((squarefreeSubdivision_leaf_width_lt event eventNonzero squarefree
        curve box root leaf leafMember).trans_le
          ((squarefreeLeafWidth_le_common event squarefree curve box root).trans
            (commonLeafWidth_le_condition event root member)))

def squarefreeConditionEvents
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (squarefree : SquarefreeCertificate event)
    (curve : RationalCurve) (box : Box) (root leaf : Cell)
    (leafMember : leaf ∈
      (squarefreeSubdivision event eventNonzero squarefree
        curve box root).leaves) :
    List (ConditionEvent event eventNonzero curve box root leaf) :=
  (CCL.CurveBoxConditions.activeConditionPolynomials curve box).attach.map
    fun entry => squarefreeConditionEvent event eventNonzero squarefree
      curve box root leaf leafMember entry.1 entry.2

/-- A squarefree common leaf retains the ordinary aligned box-condition
records and the stronger Taylor width that makes the root-event count
semantically exhaustive. -/
structure SquarefreeClassifiedLeaf
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (squarefree : SquarefreeCertificate event)
    (curve : RationalCurve) (box : Box) (root : Cell) where
  cell : Cell
  member : cell ∈
    (squarefreeSubdivision event eventNonzero squarefree
      curve box root).leaves
  refines : cell.interval.Refines root.interval
  widthSmall : cell.interval.width <
    squarefreeLeafWidth event squarefree curve box root
  eventResolution : CauchyEventResolution
    (reducedNumerator (RFAP.ComputableDerivative.derivative event) event)
    (reducedDenominator (RFAP.ComputableDerivative.derivative event) event)
    cell.interval
  boxConditionEvents :
    List (ConditionEvent event eventNonzero curve box root cell)

def classifySquarefreeLeaf
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (squarefree : SquarefreeCertificate event)
    (curve : RationalCurve) (box : Box) (root leaf : Cell)
    (member : leaf ∈
      (squarefreeSubdivision event eventNonzero squarefree
        curve box root).leaves) :
    SquarefreeClassifiedLeaf event eventNonzero squarefree
      curve box root where
  cell := leaf
  member := member
  refines := squarefreeSubdivision_leaf_refines event eventNonzero squarefree
    curve box root leaf member
  widthSmall := squarefreeSubdivision_leaf_width_lt event eventNonzero
    squarefree curve box root leaf member
  eventResolution :=
    polynomialEventResolutionOfBounds event root leaf
      (squarefreeSubdivision_leaf_refines event eventNonzero squarefree
        curve box root leaf member)
      ((squarefreeSubdivision_leaf_width_lt event eventNonzero squarefree
        curve box root leaf member).trans_le
          ((squarefreeLeafWidth_le_common event squarefree curve box root).trans
            (commonLeafWidth_le_event event curve box root)))
  boxConditionEvents := squarefreeConditionEvents event eventNonzero squarefree
    curve box root leaf member

namespace SquarefreeClassifiedLeaf

def eventSigns
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {squarefree : SquarefreeCertificate event}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (leaf : SquarefreeClassifiedLeaf event eventNonzero squarefree
      curve box root) :
    CauchyEventSigns
      (reducedNumerator (RFAP.ComputableDerivative.derivative event) event)
      (reducedDenominator (RFAP.ComputableDerivative.derivative event) event)
      leaf.cell.interval :=
  leaf.eventResolution.signs

def eventCount
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {squarefree : SquarefreeCertificate event}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (leaf : SquarefreeClassifiedLeaf event eventNonzero squarefree
      curve box root) : Int :=
  RFAP.SturmEventPartition.eventIndex2 leaf.eventSigns

theorem eventCount_eq_sturmRootCount2
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {squarefree : SquarefreeCertificate event}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (leaf : SquarefreeClassifiedLeaf event eventNonzero squarefree
      curve box root) :
    leaf.eventCount = sturmRootCount2 event
      leaf.cell.interval.lower leaf.cell.interval.upper := by
  unfold eventCount RFAP.SturmEventPartition.eventIndex2
    sturmRootCount2 reducedCauchyIndex2
  exact leaf.eventSigns.index.symm

/-- The key semantic closure: every displayed rational root in a squarefree
leaf forces the stored event integer to be nonzero. -/
theorem eventCount_ne_zero_of_root
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {squarefree : SquarefreeCertificate event}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (leaf : SquarefreeClassifiedLeaf event eventNonzero squarefree
      curve box root)
    (parameter : Coordinate) (inside : leaf.cell.interval.Contains parameter)
    (rootZero : event.eval parameter = 0) : leaf.eventCount ≠ 0 := by
  rw [leaf.eventCount_eq_sturmRootCount2]
  exact CCL.CoordinateTaylor.sturmRootCount2_ne_zero_of_root
    event squarefree leaf.refines leaf.cell.proper
      (leaf.widthSmall.trans_le
        (squarefreeLeafWidth_le_orientation event squarefree curve box root))
      leaf.eventResolution parameter inside rootZero

def eventState
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {squarefree : SquarefreeCertificate event}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (leaf : SquarefreeClassifiedLeaf event eventNonzero squarefree
      curve box root)
    (countNonzero : leaf.eventCount ≠ 0) :
    RFAP.SturmNonzeroEvent.State event where
  cell := leaf.cell
  countNonzero := by
    rw [← leaf.eventCount_eq_sturmRootCount2]
    exact countNonzero

/-- Exhaustive squarefree leaf status.  A zero event count now carries a
pointwise no-root certificate; the other branch starts the persistent
nonzero-event transducer. -/
inductive Status
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {squarefree : SquarefreeCertificate event}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (leaf : SquarefreeClassifiedLeaf event eventNonzero squarefree
      curve box root) where
  | clear (noRoot : ∀ parameter, leaf.cell.interval.Contains parameter →
      event.eval parameter ≠ 0)
  | event (state : RFAP.SturmNonzeroEvent.State event)
      (cell_eq : state.cell = leaf.cell)

def classify
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {squarefree : SquarefreeCertificate event}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (leaf : SquarefreeClassifiedLeaf event eventNonzero squarefree
      curve box root) : Status leaf := by
  by_cases countNonzero : leaf.eventCount ≠ 0
  · exact .event (leaf.eventState countNonzero) rfl
  · have countZero : leaf.eventCount = 0 :=
      Decidable.not_not.mp countNonzero
    exact .clear fun parameter inside rootZero =>
      (leaf.eventCount_ne_zero_of_root parameter inside rootZero countZero).elim

end SquarefreeClassifiedLeaf

/-- Executed squarefree/Taylor subdivision with an exhaustive classifier on
every emitted leaf. -/
structure SquarefreeEventPartition
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (squarefree : SquarefreeCertificate event)
    (curve : RationalCurve) (box : Box) (root : Cell) where
  tree : Subdivision event curve box
  tree_eq : tree = squarefreeSubdivision event eventNonzero squarefree
    curve box root
  classify : (leaf : Cell) → leaf ∈ tree.leaves →
    SquarefreeClassifiedLeaf event eventNonzero squarefree curve box root
  classify_cell : ∀ (leaf : Cell) (member : leaf ∈ tree.leaves),
    (classify leaf member).cell = leaf

def classifySquarefreeEvents
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (squarefree : SquarefreeCertificate event)
    (curve : RationalCurve) (box : Box) (root : Cell) :
    SquarefreeEventPartition event eventNonzero squarefree curve box root where
  tree := squarefreeSubdivision event eventNonzero squarefree curve box root
  tree_eq := rfl
  classify := fun leaf member => classifySquarefreeLeaf event eventNonzero
    squarefree curve box root leaf member
  classify_cell := fun _leaf _member => rfl

/-- Constructive location in the exhaustive squarefree partition. -/
structure LocatedSquarefreeParameter
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {squarefree : SquarefreeCertificate event}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (partition : SquarefreeEventPartition event eventNonzero squarefree
      curve box root)
    (parameter : Coordinate) where
  leaf : Cell
  member : leaf ∈ partition.tree.leaves
  contains : leaf.interval.Contains parameter
  classification : SquarefreeClassifiedLeaf event eventNonzero squarefree
    curve box root
  classification_eq : classification = partition.classify leaf member
  classification_cell : classification.cell = leaf

def SquarefreeEventPartition.locate
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {squarefree : SquarefreeCertificate event}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (partition : SquarefreeEventPartition event eventNonzero squarefree
      curve box root)
    (parameter : Coordinate) (inside : root.interval.Contains parameter) :
    LocatedSquarefreeParameter partition parameter := by
  let found := Subdivision.locateBuild event eventNonzero curve box
    (squarefreeDepth event squarefree curve box root) root parameter inside
  have treeMember : found.leaf ∈ partition.tree.leaves := by
    rw [partition.tree_eq]
    exact found.member
  exact
    { leaf := found.leaf
      member := treeMember
      contains := found.contains
      classification := partition.classify found.leaf treeMember
      classification_eq := rfl
      classification_cell := partition.classify_cell found.leaf treeMember }

/-- One common leaf with every aligned event classification already
executed. -/
structure ClassifiedLeaf
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box) (root : Cell) where
  cell : Cell
  member : cell ∈
    (commonSubdivision event eventNonzero curve box root).leaves
  refines : cell.interval.Refines root.interval
  widthSmall : cell.interval.width < commonLeafWidth event curve box root
  eventResolution : CauchyEventResolution
    (reducedNumerator (RFAP.ComputableDerivative.derivative event) event)
    (reducedDenominator (RFAP.ComputableDerivative.derivative event) event)
    cell.interval
  boxConditionEvents :
    List (ConditionEvent event eventNonzero curve box root cell)

def classifyLeaf
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box) (root leaf : Cell)
    (member : leaf ∈
      (commonSubdivision event eventNonzero curve box root).leaves) :
    ClassifiedLeaf event eventNonzero curve box root where
  cell := leaf
  member := member
  refines := commonSubdivision_leaf_refines event eventNonzero curve box
    root leaf member
  widthSmall := commonSubdivision_leaf_width_lt event eventNonzero curve box
    root leaf member
  eventResolution :=
    polynomialEventResolution event eventNonzero curve box root leaf member
  boxConditionEvents := conditionEvents event eventNonzero curve box
    root leaf member

namespace ClassifiedLeaf

def eventSigns
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (leaf : ClassifiedLeaf event eventNonzero curve box root) :
    CauchyEventSigns
      (reducedNumerator (RFAP.ComputableDerivative.derivative event) event)
      (reducedDenominator (RFAP.ComputableDerivative.derivative event) event)
      leaf.cell.interval :=
  leaf.eventResolution.signs

/-- Quantitative zero-event evidence retained from the neutral scanner
branch. -/
structure NeutralCertificate
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (leaf : ClassifiedLeaf event eventNonzero curve box root) where
  denominator : RFAP.IntervalSign.Certificate
    (reducedDenominator (RFAP.ComputableDerivative.derivative event) event)
    leaf.cell.interval

def neutralCertificate?
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (leaf : ClassifiedLeaf event eventNonzero curve box root) :
    Option (NeutralCertificate leaf) :=
  match leaf.eventResolution with
  | .neutral denominator _chain => some ⟨denominator⟩
  | .numerator _certificate _tail => none

theorem NeutralCertificate.event_eval_ne_zero
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {curve : RationalCurve} {box : Box} {root : Cell}
    {leaf : ClassifiedLeaf event eventNonzero curve box root}
    (neutral : NeutralCertificate leaf)
    (squarefree : RFAP.PathClearance.CoprimeCertificate event
      (RFAP.ComputableDerivative.derivative event))
    {parameter : Coordinate}
    (inside : leaf.cell.interval.Contains parameter) :
    event.eval parameter ≠ 0 :=
  denominator_eval_ne_zero_of_reduced_of_coprime squarefree
    (neutral.denominator.eval_ne_zero inside)

/-- The finite integer attached to the main curve-root event in this aligned
leaf.  It is definitionally the displayed doubled Sturm count, but retaining
the classified finite-sign presentation avoids recomputing the chain. -/
def eventCount
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (leaf : ClassifiedLeaf event eventNonzero curve box root) : Int :=
  RFAP.SturmEventPartition.eventIndex2 leaf.eventSigns

theorem eventCount_eq_sturmRootCount2
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (leaf : ClassifiedLeaf event eventNonzero curve box root) :
    leaf.eventCount = sturmRootCount2 event
      leaf.cell.interval.lower leaf.cell.interval.upper := by
  unfold eventCount RFAP.SturmEventPartition.eventIndex2
    sturmRootCount2 reducedCauchyIndex2
  exact leaf.eventSigns.index.symm

/-- A classified nonzero curve event starts the persistent shrinking
univariate event transducer without discarding its aligned parent leaf. -/
def eventState
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (leaf : ClassifiedLeaf event eventNonzero curve box root)
    (countNonzero : leaf.eventCount ≠ 0) :
    RFAP.SturmNonzeroEvent.State event where
  cell := leaf.cell
  countNonzero := by
    rw [← leaf.eventCount_eq_sturmRootCount2]
    exact countNonzero

/-- Refine a classified nonzero curve event to an arbitrary positive
rational parameter width. -/
def requestEvent
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (leaf : ClassifiedLeaf event eventNonzero curve box root)
    (countNonzero : leaf.eventCount ≠ 0) (epsilon : Coordinate) :
    RFAP.SturmNonzeroEvent.State event :=
  RFAP.SturmNonzeroEvent.request event eventNonzero
    (leaf.eventState countNonzero) epsilon

theorem requestEvent_refines
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (leaf : ClassifiedLeaf event eventNonzero curve box root)
    (countNonzero : leaf.eventCount ≠ 0) (epsilon : Coordinate) :
    (leaf.requestEvent countNonzero epsilon).cell.interval.Refines
      leaf.cell.interval :=
  RFAP.SturmNonzeroEvent.request_refines event eventNonzero
    (leaf.eventState countNonzero) epsilon

theorem requestEvent_width_le
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (leaf : ClassifiedLeaf event eventNonzero curve box root)
    (countNonzero : leaf.eventCount ≠ 0) (epsilon : Coordinate)
    (positive : 0 < epsilon) :
    (leaf.requestEvent countNonzero epsilon).cell.interval.width ≤ epsilon :=
  RFAP.SturmNonzeroEvent.request_width_le event eventNonzero
    (leaf.eventState countNonzero) epsilon positive

/-- Executable zero/nonzero split of the already-classified curve-event
integer.  The nonzero branch carries the persistent shrinking state rather
than only a proposition about the count. -/
inductive CountStatus
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (leaf : ClassifiedLeaf event eventNonzero curve box root) where
  | zero (countZero : leaf.eventCount = 0)
  | nonzero (state : RFAP.SturmNonzeroEvent.State event)
      (cell_eq : state.cell = leaf.cell)

def classifyCount
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (leaf : ClassifiedLeaf event eventNonzero curve box root) :
    CountStatus leaf := by
  by_cases countNonzero : leaf.eventCount ≠ 0
  · exact .nonzero (leaf.eventState countNonzero) rfl
  · exact .zero (Decidable.not_not.mp countNonzero)

end ClassifiedLeaf

/-- The finite common tree paired with the total simultaneous classifier for
every emitted leaf. -/
structure EventPartition
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box) (root : Cell) where
  tree : Subdivision event curve box
  tree_eq : tree = commonSubdivision event eventNonzero curve box root
  classify : (leaf : Cell) → leaf ∈ tree.leaves →
    ClassifiedLeaf event eventNonzero curve box root
  classify_cell : ∀ (leaf : Cell) (member : leaf ∈ tree.leaves),
    (classify leaf member).cell = leaf

def classifyEvents
    (event : Polynomial) (eventNonzero : event.isZero = false)
    (curve : RationalCurve) (box : Box) (root : Cell) :
    EventPartition event eventNonzero curve box root where
  tree := commonSubdivision event eventNonzero curve box root
  tree_eq := rfl
  classify := fun leaf member =>
    classifyLeaf event eventNonzero curve box root leaf member
  classify_cell := fun _leaf _member => rfl

/-- Constructive location of one displayed parameter in the classified
common leaf family. -/
structure LocatedParameter
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (partition : EventPartition event eventNonzero curve box root)
    (parameter : Coordinate) where
  leaf : Cell
  member : leaf ∈ partition.tree.leaves
  contains : leaf.interval.Contains parameter
  classification : ClassifiedLeaf event eventNonzero curve box root
  classification_eq : classification = partition.classify leaf member
  classification_cell : classification.cell = leaf

def EventPartition.locate
    {event : Polynomial} {eventNonzero : event.isZero = false}
    {curve : RationalCurve} {box : Box} {root : Cell}
    (partition : EventPartition event eventNonzero curve box root)
    (parameter : Coordinate) (inside : root.interval.Contains parameter) :
    LocatedParameter partition parameter := by
  let found := Subdivision.locateBuild event eventNonzero curve box
    (commonDepth event curve box root) root parameter inside
  have treeMember : found.leaf ∈ partition.tree.leaves := by
    rw [partition.tree_eq]
    exact found.member
  exact
    { leaf := found.leaf
      member := treeMember
      contains := found.contains
      classification := partition.classify found.leaf treeMember
      classification_eq := rfl
      classification_cell := partition.classify_cell found.leaf treeMember }

end CCL.CurveBoxEventPartition
