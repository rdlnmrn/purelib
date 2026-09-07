import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Isolation.AxisSafeCuts

/-!
# Choice-free raw-winding safe subdivision

Central-third eliminant-certified cuts split a clear box into four clear
children.  A finite first-nonzero scan retains raw winding while every round
contracts squared diagonal by `4/9`.
-/

namespace RFAP.RawSubdivision

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev BoundaryClearance := RFAP.BoxClearance.BoundaryClearance
abbrev AxisEliminationCertificate :=
  RFAP.AxisSafeCuts.AxisEliminationCertificate

open RFAP.Winding
open RFAP.AxisSafeCuts

/-- A clear proper subbox carrying nonzero raw winding. -/
structure RawWindingState
    (p : GaussianPolynomial) (ambient : Box) where
  box : Box
  refinesAmbient : box.Refines ambient
  proper : box.Proper
  clearance : BoundaryClearance p box
  rawWinding_ne : quadrupledBoxWinding p box ≠ 0

/-- A clear child, before the deterministic nonzero-winding choice. -/
structure RawChild
    (p : GaussianPolynomial) (ambient parent : Box) where
  box : Box
  refinesParent : box.Refines parent
  refinesAmbient : box.Refines ambient
  proper : box.Proper
  clearance : BoundaryClearance p box
  contracts : box.diagonalSq ≤ (4 / 9 : Coordinate) * parent.diagonalSq

private theorem diagonalSq_le_four_ninths {child parent : Box}
    (widthX : child.widthX ≤ (2 / 3 : Coordinate) * parent.widthX)
    (widthY : child.widthY ≤ (2 / 3 : Coordinate) * parent.widthY) :
    child.diagonalSq ≤ (4 / 9 : Coordinate) * parent.diagonalSq := by
  have childXNonnegative := child.widthX_nonneg
  have childYNonnegative := child.widthY_nonneg
  have scaledXNonnegative :
      0 ≤ (2 / 3 : Coordinate) * parent.widthX :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      parent.widthX_nonneg
  have scaledYNonnegative :
      0 ≤ (2 / 3 : Coordinate) * parent.widthY :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      parent.widthY_nonneg
  have squareX : child.widthX ^ 2 ≤
      ((2 / 3 : Coordinate) * parent.widthX) ^ 2 := by
    rw [pow_two, pow_two]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct widthX widthX
      childXNonnegative scaledXNonnegative
  have squareY : child.widthY ^ 2 ≤
      ((2 / 3 : Coordinate) * parent.widthY) ^ 2 := by
    rw [pow_two, pow_two]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct widthY widthY
      childYNonnegative scaledYNonnegative
  have scaleSquare : (2 / 3 : Coordinate) ^ 2 = 4 / 9 := by
    decide
  calc
    child.diagonalSq = child.widthX ^ 2 + child.widthY ^ 2 := rfl
    _ ≤ ((2 / 3 : Coordinate) * parent.widthX) ^ 2 +
          ((2 / 3 : Coordinate) * parent.widthY) ^ 2 :=
      add_le_add squareX squareY
    _ = (2 / 3 : Coordinate) ^ 2 *
          (parent.widthX ^ 2 + parent.widthY ^ 2) := by
      ring1
    _ = (4 / 9 : Coordinate) * parent.diagonalSq := by
      rw [scaleSquare]
      rfl

/-- Four clear children with exact raw additivity and uniform contraction. -/
structure RawFourGrid
    {p : GaussianPolynomial} {ambient : Box}
    (state : RawWindingState p ambient) where
  lowerLeft : RawChild p ambient state.box
  upperLeft : RawChild p ambient state.box
  lowerRight : RawChild p ambient state.box
  upperRight : RawChild p ambient state.box
  additive : quadrupledBoxWinding p state.box =
    quadrupledBoxWinding p lowerLeft.box +
      quadrupledBoxWinding p upperLeft.box +
      quadrupledBoxWinding p lowerRight.box +
      quadrupledBoxWinding p upperRight.box

/-- One executable central safe-cut grid. -/
def safeRawFourGrid
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) : RawFourGrid state := by
  let grid := buildClearFourGrid elimination state.box state.proper
  let clearances := grid.childClearances state.clearance
  have xSpec := verticalSafeCoordinate_spec elimination state.box state.proper
  have ySpec := horizontalSafeCoordinate_spec elimination state.box state.proper
  have xContract :=
    verticalSafeCoordinate_contraction elimination state.box state.proper
  have yContract :=
    horizontalSafeCoordinate_contraction elimination state.box state.proper
  have lowerLeftContract : grid.lowerLeft.diagonalSq ≤
      (4 / 9 : Coordinate) * state.box.diagonalSq := by
    apply diagonalSq_le_four_ninths
    · change grid.xCut - state.box.xLower ≤
        (2 / 3 : Coordinate) * state.box.widthX
      exact xContract.1.le
    · change grid.yCut - state.box.yLower ≤
        (2 / 3 : Coordinate) * state.box.widthY
      exact yContract.1.le
  have upperLeftContract : grid.upperLeft.diagonalSq ≤
      (4 / 9 : Coordinate) * state.box.diagonalSq := by
    apply diagonalSq_le_four_ninths
    · change grid.xCut - state.box.xLower ≤
        (2 / 3 : Coordinate) * state.box.widthX
      exact xContract.1.le
    · change state.box.yUpper - grid.yCut ≤
        (2 / 3 : Coordinate) * state.box.widthY
      exact yContract.2.le
  have lowerRightContract : grid.lowerRight.diagonalSq ≤
      (4 / 9 : Coordinate) * state.box.diagonalSq := by
    apply diagonalSq_le_four_ninths
    · change state.box.xUpper - grid.xCut ≤
        (2 / 3 : Coordinate) * state.box.widthX
      exact xContract.2.le
    · change grid.yCut - state.box.yLower ≤
        (2 / 3 : Coordinate) * state.box.widthY
      exact yContract.1.le
  have upperRightContract : grid.upperRight.diagonalSq ≤
      (4 / 9 : Coordinate) * state.box.diagonalSq := by
    apply diagonalSq_le_four_ninths
    · change state.box.xUpper - grid.xCut ≤
        (2 / 3 : Coordinate) * state.box.widthX
      exact xContract.2.le
    · change state.box.yUpper - grid.yCut ≤
        (2 / 3 : Coordinate) * state.box.widthY
      exact yContract.2.le
  exact
    { lowerLeft :=
        { box := grid.lowerLeft
          refinesParent := grid.lowerLeft_refines
          refinesAmbient := grid.lowerLeft_refines.trans state.refinesAmbient
          proper := ⟨xSpec.2.1, ySpec.2.1⟩
          clearance := clearances.1
          contracts := lowerLeftContract }
      upperLeft :=
        { box := grid.upperLeft
          refinesParent := grid.upperLeft_refines
          refinesAmbient := grid.upperLeft_refines.trans state.refinesAmbient
          proper := ⟨xSpec.2.1, ySpec.2.2⟩
          clearance := clearances.2.1
          contracts := upperLeftContract }
      lowerRight :=
        { box := grid.lowerRight
          refinesParent := grid.lowerRight_refines
          refinesAmbient := grid.lowerRight_refines.trans state.refinesAmbient
          proper := ⟨xSpec.2.2, ySpec.2.1⟩
          clearance := clearances.2.2.1
          contracts := lowerRightContract }
      upperRight :=
        { box := grid.upperRight
          refinesParent := grid.upperRight_refines
          refinesAmbient := grid.upperRight_refines.trans state.refinesAmbient
          proper := ⟨xSpec.2.2, ySpec.2.2⟩
          clearance := clearances.2.2.2
          contracts := upperRightContract }
      additive := grid.winding_additive }

@[simp] theorem safeRawFourGrid_lowerLeft_box
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) :
    (safeRawFourGrid elimination state).lowerLeft.box =
      (buildClearFourGrid elimination state.box state.proper).lowerLeft := rfl

@[simp] theorem safeRawFourGrid_upperLeft_box
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) :
    (safeRawFourGrid elimination state).upperLeft.box =
      (buildClearFourGrid elimination state.box state.proper).upperLeft := rfl

@[simp] theorem safeRawFourGrid_lowerRight_box
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) :
    (safeRawFourGrid elimination state).lowerRight.box =
      (buildClearFourGrid elimination state.box state.proper).lowerRight := rfl

@[simp] theorem safeRawFourGrid_upperRight_box
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) :
    (safeRawFourGrid elimination state).upperRight.box =
      (buildClearFourGrid elimination state.box state.proper).upperRight := rfl

/-- Fixed finite order on the four children. -/
def firstNonzeroChild
    {p : GaussianPolynomial} {ambient : Box}
    {state : RawWindingState p ambient} (grid : RawFourGrid state) :
    RawChild p ambient state.box :=
  if quadrupledBoxWinding p grid.lowerLeft.box ≠ 0 then grid.lowerLeft
  else if quadrupledBoxWinding p grid.upperLeft.box ≠ 0 then grid.upperLeft
  else if quadrupledBoxWinding p grid.lowerRight.box ≠ 0 then grid.lowerRight
  else grid.upperRight

theorem firstNonzeroChild_rawWinding_ne
    {p : GaussianPolynomial} {ambient : Box}
    {state : RawWindingState p ambient} (grid : RawFourGrid state) :
    quadrupledBoxWinding p (firstNonzeroChild grid).box ≠ 0 := by
  by_cases lowerLeftNonzero :
      quadrupledBoxWinding p grid.lowerLeft.box ≠ 0
  · simp [firstNonzeroChild, lowerLeftNonzero]
  by_cases upperLeftNonzero :
      quadrupledBoxWinding p grid.upperLeft.box ≠ 0
  · simp [firstNonzeroChild, lowerLeftNonzero, upperLeftNonzero]
  by_cases lowerRightNonzero :
      quadrupledBoxWinding p grid.lowerRight.box ≠ 0
  · simp [firstNonzeroChild, lowerLeftNonzero, upperLeftNonzero,
      lowerRightNonzero]
  have upperRightNonzero :
      quadrupledBoxWinding p grid.upperRight.box ≠ 0 := by
    have lowerLeftZero :
        quadrupledBoxWinding p grid.lowerLeft.box = 0 := by
      by_cases equal : quadrupledBoxWinding p grid.lowerLeft.box = 0
      · exact equal
      · exact (lowerLeftNonzero equal).elim
    have upperLeftZero :
        quadrupledBoxWinding p grid.upperLeft.box = 0 := by
      by_cases equal : quadrupledBoxWinding p grid.upperLeft.box = 0
      · exact equal
      · exact (upperLeftNonzero equal).elim
    have lowerRightZero :
        quadrupledBoxWinding p grid.lowerRight.box = 0 := by
      by_cases equal : quadrupledBoxWinding p grid.lowerRight.box = 0
      · exact equal
      · exact (lowerRightNonzero equal).elim
    intro upperRightZero
    apply state.rawWinding_ne
    rw [grid.additive]
    simp only [lowerLeftZero, upperLeftZero, lowerRightZero, upperRightZero]
    ring1
  simpa [firstNonzeroChild, lowerLeftNonzero, upperLeftNonzero,
    lowerRightNonzero] using upperRightNonzero

/-- One deterministic raw-winding-preserving safe refinement. -/
def refineOnce
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) : RawWindingState p ambient :=
  let grid := safeRawFourGrid elimination state
  let child := firstNonzeroChild grid
  { box := child.box
    refinesAmbient := child.refinesAmbient
    proper := child.proper
    clearance := child.clearance
    rawWinding_ne := firstNonzeroChild_rawWinding_ne grid }

theorem refineOnce_refines
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) :
    (refineOnce elimination state).box.Refines state.box :=
  (firstNonzeroChild (safeRawFourGrid elimination state)).refinesParent

theorem refineOnce_contracts
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) :
    (refineOnce elimination state).box.diagonalSq ≤
      (4 / 9 : Coordinate) * state.box.diagonalSq :=
  (firstNonzeroChild (safeRawFourGrid elimination state)).contracts

/-- Fixed-depth iteration of safe raw refinement. -/
def refineN
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound) :
    Nat → RawWindingState p ambient → RawWindingState p ambient
  | 0, state => state
  | depth + 1, state => refineOnce elimination (refineN elimination depth state)

theorem refineN_refines
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (depth : Nat) (state : RawWindingState p ambient) :
    (refineN elimination depth state).box.Refines state.box := by
  induction depth with
  | zero => exact RFAP.Boxes.Box.refines_refl _
  | succ depth inductionHypothesis =>
      exact (refineOnce_refines elimination
        (refineN elimination depth state)).trans inductionHypothesis

theorem refineN_diagonalSq_le
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (depth : Nat) (state : RawWindingState p ambient) :
    (refineN elimination depth state).box.diagonalSq ≤
      (4 / 9 : Coordinate) ^ depth * state.box.diagonalSq := by
  induction depth with
  | zero => simp [refineN]
  | succ depth inductionHypothesis =>
      calc
        (refineN elimination (depth + 1) state).box.diagonalSq ≤
            (4 / 9 : Coordinate) *
              (refineN elimination depth state).box.diagonalSq :=
          refineOnce_contracts elimination (refineN elimination depth state)
        _ ≤ (4 / 9 : Coordinate) *
              ((4 / 9 : Coordinate) ^ depth * state.box.diagonalSq) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            inductionHypothesis (by decide)
        _ = (4 / 9 : Coordinate) ^ (depth + 1) *
              state.box.diagonalSq := by
          rw [pow_succ]
          ring1

/--
Stack-safe fixed-depth iteration of safe raw refinement.  The state is advanced
before the recursive call, so compiled evaluation uses constant call-stack
space even when the requested finite depth is large.
-/
def refineForwardN
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound) :
    Nat → RawWindingState p ambient → RawWindingState p ambient
  | 0, state => state
  | depth + 1, state =>
      refineForwardN elimination depth (refineOnce elimination state)

theorem refineForwardN_refines
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (depth : Nat) (state : RawWindingState p ambient) :
    (refineForwardN elimination depth state).box.Refines state.box := by
  induction depth generalizing state with
  | zero => exact RFAP.Boxes.Box.refines_refl _
  | succ depth inductionHypothesis =>
      exact (inductionHypothesis (refineOnce elimination state)).trans
        (refineOnce_refines elimination state)

theorem refineForwardN_diagonalSq_le
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (depth : Nat) (state : RawWindingState p ambient) :
    (refineForwardN elimination depth state).box.diagonalSq ≤
      (4 / 9 : Coordinate) ^ depth * state.box.diagonalSq := by
  induction depth generalizing state with
  | zero => simp [refineForwardN]
  | succ depth inductionHypothesis =>
      let next := refineOnce elimination state
      have recursive := inductionHypothesis next
      calc
        (refineForwardN elimination (depth + 1) state).box.diagonalSq =
            (refineForwardN elimination depth next).box.diagonalSq := rfl
        _ ≤ (4 / 9 : Coordinate) ^ depth * next.box.diagonalSq := recursive
        _ ≤ (4 / 9 : Coordinate) ^ depth *
              ((4 / 9 : Coordinate) * state.box.diagonalSq) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (refineOnce_contracts elimination state)
            (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) depth)
        _ = (4 / 9 : Coordinate) ^ (depth + 1) *
              state.box.diagonalSq := by
          rw [pow_succ]
          ring1

def refinementDepth
    {p : GaussianPolynomial} {ambient : Box}
    (state : RawWindingState p ambient) (threshold : Coordinate) : Nat :=
  RFAP.SafeCandidates.geometricDepth
    state.box.diagonalSq threshold

/-- Total finite refinement to a requested positive squared diagonal. -/
def refineTo
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) (threshold : Coordinate) :
    RawWindingState p ambient :=
  refineForwardN elimination (refinementDepth state threshold) state

theorem refineTo_diagonalSq_le
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) {threshold : Coordinate}
    (thresholdPositive : 0 < threshold) :
    (refineTo elimination state threshold).box.diagonalSq ≤ threshold := by
  let depth := refinementDepth state threshold
  have raw := refineForwardN_diagonalSq_le elimination depth state
  have powerBound : (4 / 9 : Coordinate) ^ depth ≤
      (2 / 3 : Coordinate) ^ depth :=
    RFAP.ConstructiveFraction.pow_le_pow_direct (by decide) (by decide) depth
  have scaledPower :
      (4 / 9 : Coordinate) ^ depth * state.box.diagonalSq ≤
        (2 / 3 : Coordinate) ^ depth * state.box.diagonalSq :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      powerBound state.box.diagonalSq_nonneg
  exact raw.trans (scaledPower.trans (by
    simpa only [depth, refinementDepth] using
      RFAP.SafeCandidates.geometricDepth_sufficient
        state.box.diagonalSq_nonneg thresholdPositive))

theorem refineTo_refines
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) (threshold : Coordinate) :
    (refineTo elimination state threshold).box.Refines state.box :=
  refineForwardN_refines elimination (refinementDepth state threshold) state

end RFAP.RawSubdivision
