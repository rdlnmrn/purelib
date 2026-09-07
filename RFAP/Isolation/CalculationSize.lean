import mathlib.Tactic.QuotientFreeOmega
import RFAP.Isolation.RawSubdivision
import RFAP.Sturm.Normalized

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

namespace RFAP.IsolationCalculationSize

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev WorkingCoordinate := RFAP.NormalizedFraction.ReducedFraction
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box

open RFAP.NormalizedPolynomialResource
open RFAP.SafeCandidates

def coordinateMagnitude (source : Coordinate) : Nat :=
  rationalModel.magnitude (RFAP.NormalizedFraction.ofRational source)

private theorem normalizedAdd_le {left right : Coordinate} {bound : Nat}
    (leftBound : coordinateMagnitude left ≤ bound)
    (rightBound : coordinateMagnitude right ≤ bound) :
    coordinateMagnitude (RFAP.NormalizedFraction.normalizedAdd left right) ≤
      grow rationalModel bound 1 := by
  unfold coordinateMagnitude
  rw [RFAP.NormalizedFraction.ofRational_normalizedAdd]
  exact rationalModel.add_le leftBound rightBound

private theorem normalizedSub_le {left right : Coordinate} {bound : Nat}
    (leftBound : coordinateMagnitude left ≤ bound)
    (rightBound : coordinateMagnitude right ≤ bound) :
    coordinateMagnitude (RFAP.NormalizedFraction.normalizedSub left right) ≤
      grow rationalModel bound 1 := by
  unfold coordinateMagnitude
  rw [RFAP.NormalizedFraction.ofRational_normalizedSub]
  exact rationalModel.sub_le leftBound rightBound

private theorem normalizedMul_le {left right : Coordinate} {bound : Nat}
    (leftBound : coordinateMagnitude left ≤ bound)
    (rightBound : coordinateMagnitude right ≤ bound) :
    coordinateMagnitude (RFAP.NormalizedFraction.normalizedMul left right) ≤
      grow rationalModel bound 1 := by
  unfold coordinateMagnitude
  rw [RFAP.NormalizedFraction.ofRational_normalizedMul]
  exact rationalModel.mul_le leftBound rightBound

private theorem normalizedDiv_le {left right : Coordinate} {bound : Nat}
    (leftBound : coordinateMagnitude left ≤ bound)
    (rightBound : coordinateMagnitude right ≤ bound) :
    coordinateMagnitude (RFAP.NormalizedFraction.normalizedDiv left right) ≤
      grow rationalModel bound 1 := by
  unfold coordinateMagnitude
  rw [RFAP.NormalizedFraction.ofRational_normalizedDiv]
  exact rationalModel.div_le leftBound rightBound

def intervalSourceMagnitude (a b : Coordinate) (degreeBound : Nat) : Nat :=
  max (coordinateMagnitude a)
    (max (coordinateMagnitude b)
      (coordinateMagnitude ((max 3 (degreeBound + 2) : Nat) : Coordinate)))

private theorem left_le_intervalSource (a b : Coordinate)
    (degreeBound : Nat) :
    coordinateMagnitude a ≤ intervalSourceMagnitude a b degreeBound :=
  le_max_left _ _

private theorem right_le_intervalSource (a b : Coordinate)
    (degreeBound : Nat) :
    coordinateMagnitude b ≤ intervalSourceMagnitude a b degreeBound :=
  (le_max_left _ _).trans (le_max_right _ _)

private theorem natCast_le_intervalSource (a b : Coordinate)
    (degreeBound value : Nat) (valueBound : value ≤ max 3 (degreeBound + 2)) :
    coordinateMagnitude (value : Coordinate) ≤
      intervalSourceMagnitude a b degreeBound := by
  apply (RFAP.NormalizedFraction.componentMagnitude_natCast_mono
    valueBound).trans
  exact (le_max_right _ _).trans (le_max_right _ _)

theorem centralLower_magnitude_le (a b : Coordinate) (degreeBound : Nat) :
    coordinateMagnitude (centralLower a b) ≤
      grow rationalModel (intervalSourceMagnitude a b degreeBound) 3 := by
  let bound := intervalSourceMagnitude a b degreeBound
  have difference := normalizedSub_le
    (right_le_intervalSource a b degreeBound)
    (left_le_intervalSource a b degreeBound)
  have threeBound := (natCast_le_intervalSource a b degreeBound 3
    (le_max_left _ _)).trans (bound_le_grow rationalModel bound 1)
  have third := normalizedDiv_le difference threeBound
  have leftBound := (left_le_intervalSource a b degreeBound).trans
    (bound_le_grow rationalModel bound 2)
  have result := normalizedAdd_le leftBound third
  simpa only [centralLower, grow_add, Nat.cast_ofNat] using result

theorem centralUpper_magnitude_le (a b : Coordinate) (degreeBound : Nat) :
    coordinateMagnitude (centralUpper a b) ≤
      grow rationalModel (intervalSourceMagnitude a b degreeBound) 4 := by
  let bound := intervalSourceMagnitude a b degreeBound
  have difference := normalizedSub_le
    (right_le_intervalSource a b degreeBound)
    (left_le_intervalSource a b degreeBound)
  have threeBound := (natCast_le_intervalSource a b degreeBound 3
    (le_max_left _ _)).trans (bound_le_grow rationalModel bound 1)
  have third := normalizedDiv_le difference threeBound
  have twoBound := (natCast_le_intervalSource a b degreeBound 2
    (by omega)).trans (bound_le_grow rationalModel bound 2)
  have twice := normalizedMul_le twoBound third
  have leftBound := (left_le_intervalSource a b degreeBound).trans
    (bound_le_grow rationalModel bound 3)
  have result := normalizedAdd_le leftBound twice
  simpa only [centralUpper, grow_add, Nat.cast_ofNat] using result

private theorem interiorCandidate_magnitude_le_of_source
    (a b : Coordinate) (degreeBound : Nat)
    (index : Fin (degreeBound + 1)) (bound : Nat)
    (aBound : coordinateMagnitude a ≤ bound)
    (bBound : coordinateMagnitude b ≤ bound)
    (divisorBound : coordinateMagnitude (degreeBound + 2 : Nat) ≤ bound)
    (indexBound : coordinateMagnitude (index.val + 1 : Nat) ≤ bound) :
    coordinateMagnitude (interiorCandidate a b degreeBound index) ≤
      grow rationalModel bound 4 := by
  have difference := normalizedSub_le bBound aBound
  have divisorLift := divisorBound.trans (bound_le_grow rationalModel bound 1)
  have step := normalizedDiv_le difference divisorLift
  have indexLift := indexBound.trans (bound_le_grow rationalModel bound 2)
  have offset := normalizedMul_le indexLift step
  have aLift := aBound.trans (bound_le_grow rationalModel bound 3)
  have result := normalizedAdd_le aLift offset
  simpa only [interiorCandidate, interiorStep, grow_add] using result

theorem centralCandidate_magnitude_le (a b : Coordinate) (degreeBound : Nat)
    (index : Fin (degreeBound + 1)) :
    coordinateMagnitude
        (interiorCandidate (centralLower a b) (centralUpper a b)
          degreeBound index) ≤
      grow rationalModel (intervalSourceMagnitude a b degreeBound) 8 := by
  let source := intervalSourceMagnitude a b degreeBound
  let centralBound := grow rationalModel source 4
  have lowerBound : coordinateMagnitude (centralLower a b) ≤ centralBound :=
    (centralLower_magnitude_le a b degreeBound).trans
      (grow_mono_steps rationalModel source (by decide))
  have upperBound : coordinateMagnitude (centralUpper a b) ≤ centralBound :=
    centralUpper_magnitude_le a b degreeBound
  have divisorSource := natCast_le_intervalSource a b degreeBound
    (degreeBound + 2) (le_max_right _ _)
  have divisorBound := divisorSource.trans
    (bound_le_grow rationalModel source 4)
  have indexNatural : index.val + 1 ≤ max 3 (degreeBound + 2) := by
    exact (Nat.succ_le_of_lt index.isLt).trans
      ((Nat.succ_le_succ (Nat.le_succ degreeBound)).trans
        (le_max_right 3 (degreeBound + 2)))
  have indexSource := natCast_le_intervalSource a b degreeBound
    (index.val + 1) indexNatural
  have indexBound := indexSource.trans
    (bound_le_grow rationalModel source 4)
  have candidate := interiorCandidate_magnitude_le_of_source
    (centralLower a b) (centralUpper a b) degreeBound index centralBound
    lowerBound upperBound divisorBound indexBound
  simpa only [centralBound, grow_add] using candidate

theorem centralSearchValue_magnitude_le (p : Polynomial)
    {a b : Coordinate} (degreeBound : Nat) (less : a < b)
    (nonzero : p.isZero = false) (degree : p.natDegree ≤ degreeBound) :
    coordinateMagnitude
        (centralSearchValue p degreeBound less nonzero degree) ≤
      grow rationalModel (intervalSourceMagnitude a b degreeBound) 8 := by
  have member := interiorSearchValue_mem p degreeBound
    (centralBounds less).2.1 nonzero degree
  rw [interiorCandidates, List.mem_ofFn] at member
  rcases member with ⟨index, equal⟩
  have selectedEqual : centralSearchValue p degreeBound less nonzero degree =
      interiorCandidate (centralLower a b) (centralUpper a b)
        degreeBound index := by
    change interiorSearchValue p degreeBound (centralBounds less).2.1
      nonzero degree = _
    exact equal.symm
  rw [selectedEqual]
  exact centralCandidate_magnitude_le a b degreeBound index

/-! ## Structural counts -/

def safeCandidateEvaluationBudget (degreeBound : Nat) : Nat :=
  degreeBound + 1

theorem safeCandidate_count_eq_budget (a b : Coordinate)
    (degreeBound : Nat) :
    (interiorCandidates a b degreeBound).length =
      safeCandidateEvaluationBudget degreeBound := by
  simp only [interiorCandidates_length, safeCandidateEvaluationBudget]

/-- One winding is four edge indices; each edge constructs one normalized
signed chain and evaluates it at two endpoints. -/
def boxWindingFieldOperationBudget (p : GaussianPolynomial) (box : Box) : Nat :=
  (RFAP.Winding.boxBoundary p box).foldl
    (fun total edge => total +
      RFAP.NormalizedSturm.cauchyIndexFieldOperationBudget
        edge.realPart edge.imagPart) 0

@[simp] theorem boxBoundary_length (p : GaussianPolynomial) (box : Box) :
    (RFAP.Winding.boxBoundary p box).length = 4 := by
  rfl

/-- Two safe-coordinate scans and at most four child windings are accounted
for in every raw subdivision round. -/
def subdivisionRoundSearchBudget (degreeBound : Nat) : Nat :=
  2 * safeCandidateEvaluationBudget degreeBound + 4

def subdivisionSearchBudget (degreeBound depth : Nat) : Nat :=
  depth * subdivisionRoundSearchBudget degreeBound

theorem subdivisionSearchBudget_succ (degreeBound depth : Nat) :
    subdivisionSearchBudget degreeBound (depth + 1) =
      subdivisionSearchBudget degreeBound depth +
        subdivisionRoundSearchBudget degreeBound := by
  unfold subdivisionSearchBudget
  rw [Nat.add_mul]
  simp only [Nat.one_mul]

/-! ## Persistent box records through repeated refinement -/

def BoxWithin (box : Box) (bound : Nat) : Prop :=
  coordinateMagnitude box.xLower ≤ bound ∧
    coordinateMagnitude box.xUpper ≤ bound ∧
    coordinateMagnitude box.yLower ≤ bound ∧
    coordinateMagnitude box.yUpper ≤ bound

def boxMagnitude (box : Box) : Nat :=
  max (coordinateMagnitude box.xLower)
    (max (coordinateMagnitude box.xUpper)
      (max (coordinateMagnitude box.yLower)
        (coordinateMagnitude box.yUpper)))

theorem box_within_boxMagnitude (box : Box) :
    BoxWithin box (boxMagnitude box) :=
  ⟨le_max_left _ _,
    (le_max_left _ _).trans (le_max_right _ _),
    (le_max_left _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)),
    (le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))⟩

def safeCutSourceMagnitude (bound degreeBound : Nat) : Nat :=
  max bound
    (coordinateMagnitude ((max 3 (degreeBound + 2) : Nat) : Coordinate))

def safeCutMagnitudeEnvelope (bound degreeBound : Nat) : Nat :=
  grow rationalModel (safeCutSourceMagnitude bound degreeBound) 8

private theorem intervalSource_le_safeCutSource
    {a b : Coordinate} {bound degreeBound : Nat}
    (aBound : coordinateMagnitude a ≤ bound)
    (bBound : coordinateMagnitude b ≤ bound) :
    intervalSourceMagnitude a b degreeBound ≤
      safeCutSourceMagnitude bound degreeBound := by
  apply max_le
  · exact aBound.trans (le_max_left _ _)
  · apply max_le
    · exact bBound.trans (le_max_left _ _)
    · exact le_max_right _ _

theorem verticalSafeCoordinate_magnitude_le
    {p : GaussianPolynomial} {degreeBound bound : Nat}
    (elimination : RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (box : Box) (proper : box.Proper) (boxWithin : BoxWithin box bound) :
    coordinateMagnitude
        (RFAP.AxisSafeCuts.verticalSafeCoordinate elimination box proper) ≤
      safeCutMagnitudeEnvelope bound degreeBound := by
  have selected := centralSearchValue_magnitude_le elimination.vertical
    degreeBound proper.1 elimination.vertical_nonzero elimination.vertical_degree
  unfold RFAP.AxisSafeCuts.verticalSafeCoordinate
  exact selected.trans (grow_mono_bound rationalModel
    (intervalSource_le_safeCutSource boxWithin.1 boxWithin.2.1) 8)

theorem horizontalSafeCoordinate_magnitude_le
    {p : GaussianPolynomial} {degreeBound bound : Nat}
    (elimination : RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (box : Box) (proper : box.Proper) (boxWithin : BoxWithin box bound) :
    coordinateMagnitude
        (RFAP.AxisSafeCuts.horizontalSafeCoordinate elimination box proper) ≤
      safeCutMagnitudeEnvelope bound degreeBound := by
  have selected := centralSearchValue_magnitude_le elimination.horizontal
    degreeBound proper.2 elimination.horizontal_nonzero
      elimination.horizontal_degree
  unfold RFAP.AxisSafeCuts.horizontalSafeCoordinate
  exact selected.trans (grow_mono_bound rationalModel
    (intervalSource_le_safeCutSource boxWithin.2.2.1 boxWithin.2.2.2) 8)

private theorem bound_le_safeCutMagnitudeEnvelope (bound degreeBound : Nat) :
    bound ≤ safeCutMagnitudeEnvelope bound degreeBound :=
  (le_max_left _ _).trans
    (bound_le_grow rationalModel (safeCutSourceMagnitude bound degreeBound) 8)

private theorem clearFourGrid_children_within
    {p : GaussianPolynomial} {degreeBound bound : Nat}
    (elimination : RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (box : Box) (proper : box.Proper) (boxWithin : BoxWithin box bound) :
    let grid := RFAP.AxisSafeCuts.buildClearFourGrid elimination box proper
    BoxWithin grid.lowerLeft (safeCutMagnitudeEnvelope bound degreeBound) ∧
      BoxWithin grid.upperLeft (safeCutMagnitudeEnvelope bound degreeBound) ∧
      BoxWithin grid.lowerRight (safeCutMagnitudeEnvelope bound degreeBound) ∧
      BoxWithin grid.upperRight (safeCutMagnitudeEnvelope bound degreeBound) := by
  let grid := RFAP.AxisSafeCuts.buildClearFourGrid elimination box proper
  let outputBound := safeCutMagnitudeEnvelope bound degreeBound
  have oldBound : bound ≤ outputBound :=
    bound_le_safeCutMagnitudeEnvelope bound degreeBound
  have xCutBound : coordinateMagnitude grid.xCut ≤ outputBound := by
    change coordinateMagnitude
      (RFAP.AxisSafeCuts.verticalSafeCoordinate elimination box proper) ≤ _
    exact verticalSafeCoordinate_magnitude_le elimination box proper boxWithin
  have yCutBound : coordinateMagnitude grid.yCut ≤ outputBound := by
    change coordinateMagnitude
      (RFAP.AxisSafeCuts.horizontalSafeCoordinate elimination box proper) ≤ _
    exact horizontalSafeCoordinate_magnitude_le elimination box proper boxWithin
  have xLower := boxWithin.1.trans oldBound
  have xUpper := boxWithin.2.1.trans oldBound
  have yLower := boxWithin.2.2.1.trans oldBound
  have yUpper := boxWithin.2.2.2.trans oldBound
  change
    BoxWithin
        ((box.verticalLeft grid.xCut grid.xInside).horizontalLower
          grid.yCut grid.yInside) outputBound ∧
      BoxWithin
        ((box.verticalLeft grid.xCut grid.xInside).horizontalUpper
          grid.yCut grid.yInside) outputBound ∧
      BoxWithin
        ((box.verticalRight grid.xCut grid.xInside).horizontalLower
          grid.yCut grid.yInside) outputBound ∧
      BoxWithin
        ((box.verticalRight grid.xCut grid.xInside).horizontalUpper
          grid.yCut grid.yInside) outputBound
  exact ⟨⟨xLower, xCutBound, yLower, yCutBound⟩,
    ⟨xLower, xCutBound, yCutBound, yUpper⟩,
    ⟨xCutBound, xUpper, yLower, yCutBound⟩,
    ⟨xCutBound, xUpper, yCutBound, yUpper⟩⟩

theorem refineOnce_box_within
    {p : GaussianPolynomial} {ambient : Box} {degreeBound bound : Nat}
    (elimination : RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (state : RFAP.RawSubdivision.RawWindingState p ambient)
    (boxWithin : BoxWithin state.box bound) :
    BoxWithin (RFAP.RawSubdivision.refineOnce elimination state).box
      (safeCutMagnitudeEnvelope bound degreeBound) := by
  let grid := RFAP.RawSubdivision.safeRawFourGrid elimination state
  have children := clearFourGrid_children_within elimination state.box
    state.proper boxWithin
  have lowerLeft : BoxWithin grid.lowerLeft.box
      (safeCutMagnitudeEnvelope bound degreeBound) := by
    simpa only [grid, RFAP.RawSubdivision.safeRawFourGrid_lowerLeft_box]
      using children.1
  have upperLeft : BoxWithin grid.upperLeft.box
      (safeCutMagnitudeEnvelope bound degreeBound) := by
    simpa only [grid, RFAP.RawSubdivision.safeRawFourGrid_upperLeft_box]
      using children.2.1
  have lowerRight : BoxWithin grid.lowerRight.box
      (safeCutMagnitudeEnvelope bound degreeBound) := by
    simpa only [grid, RFAP.RawSubdivision.safeRawFourGrid_lowerRight_box]
      using children.2.2.1
  have upperRight : BoxWithin grid.upperRight.box
      (safeCutMagnitudeEnvelope bound degreeBound) := by
    simpa only [grid, RFAP.RawSubdivision.safeRawFourGrid_upperRight_box]
      using children.2.2.2
  change BoxWithin (RFAP.RawSubdivision.firstNonzeroChild grid).box _
  unfold RFAP.RawSubdivision.firstNonzeroChild
  split
  · exact lowerLeft
  · split
    · exact upperLeft
    · split
      · exact lowerRight
      · exact upperRight

def refinementMagnitudeEnvelope (degreeBound : Nat) : Nat → Nat → Nat
  | initial, 0 => initial
  | initial, depth + 1 =>
      safeCutMagnitudeEnvelope
        (refinementMagnitudeEnvelope degreeBound initial depth) degreeBound

theorem refineN_box_within
    {p : GaussianPolynomial} {ambient : Box} {degreeBound initial : Nat}
    (elimination : RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (state : RFAP.RawSubdivision.RawWindingState p ambient)
    (initialWithin : BoxWithin state.box initial) (depth : Nat) :
    BoxWithin (RFAP.RawSubdivision.refineN elimination depth state).box
      (refinementMagnitudeEnvelope degreeBound initial depth) := by
  induction depth with
  | zero => exact initialWithin
  | succ depth inductionHypothesis =>
      exact refineOnce_box_within elimination
        (RFAP.RawSubdivision.refineN elimination depth state)
        inductionHypothesis

theorem refinementMagnitudeEnvelope_after_safeCut
    (degreeBound initial depth : Nat) :
    refinementMagnitudeEnvelope degreeBound
        (safeCutMagnitudeEnvelope initial degreeBound) depth =
      refinementMagnitudeEnvelope degreeBound initial (depth + 1) := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp only [refinementMagnitudeEnvelope]
      rw [inductionHypothesis]
      rfl

theorem refineForwardN_box_within
    {p : GaussianPolynomial} {ambient : Box} {degreeBound initial : Nat}
    (elimination : RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (state : RFAP.RawSubdivision.RawWindingState p ambient)
    (initialWithin : BoxWithin state.box initial) (depth : Nat) :
    BoxWithin (RFAP.RawSubdivision.refineForwardN elimination depth state).box
      (refinementMagnitudeEnvelope degreeBound initial depth) := by
  induction depth generalizing state initial with
  | zero => exact initialWithin
  | succ depth inductionHypothesis =>
      let next := RFAP.RawSubdivision.refineOnce elimination state
      have nextWithin :
          BoxWithin next.box (safeCutMagnitudeEnvelope initial degreeBound) :=
        refineOnce_box_within elimination state initialWithin
      have recursive := inductionHypothesis next nextWithin
      rw [refinementMagnitudeEnvelope_after_safeCut] at recursive
      exact recursive

theorem refineTo_box_within
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (state : RFAP.RawSubdivision.RawWindingState p ambient)
    (threshold : Coordinate) :
    BoxWithin (RFAP.RawSubdivision.refineTo elimination state threshold).box
      (refinementMagnitudeEnvelope degreeBound (boxMagnitude state.box)
        (RFAP.RawSubdivision.refinementDepth state threshold)) := by
  exact refineForwardN_box_within elimination state (box_within_boxMagnitude state.box)
    (RFAP.RawSubdivision.refinementDepth state threshold)

end RFAP.IsolationCalculationSize
