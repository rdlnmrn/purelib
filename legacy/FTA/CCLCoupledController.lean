import FTA.CCLBranchController
import FTA.CCLCoupledTrack
import FTA.CCLEventTerminal
import FTA.CCLGuardCellClearance
import FTA.CCLPositiveEventSemantics
import FTA.CCLTerminalSeparation
import FTA.SafeCandidates

/-!
# Opening one coupled CCL controller step

This module specializes the bounded branch-family analysis to the parser
state computed from a coupled state's actual word.  The parser determinant
certificate is discharged internally.  An exact decoder-pole root is also
split into the distinguished zero terminal and the nonzero rational case,
matching the terminal variants of `CCLCoupledTrack.StepResult`.
-/

namespace FTA
namespace CCLCoupledController

open CCL
open FTA.CCLBoundaryPath
open FTA.CCLBranchCharts
open FTA.CCLBranchController
open FTA.CCLBranchCells
open FTA.CCLBranchEvidence
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLBranchPartition
open FTA.CCLBranchPlan
open FTA.CCLCompatibleCandidates
open FTA.CCLClearanceExclusion
open FTA.CCLFormulaPullback
open FTA.CCLEventTerminal
open FTA.CCLGeometry
open FTA.CCLGuardCellClearance
open FTA.CCLPathIntersection
open FTA.CCLPositiveEventSemantics
open FTA.CCLTerminalSeparation
open FTA.ProjectivePath
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-! ## Nonvanishing on nondegenerate boundary charts -/

private theorem unitIntervalProper (index : ℕ) :
    (index : ℚ) < (index : ℚ) + 1 := by
  linarith

private theorem denominatorNorm_sparse_nonzero
    (path : ProjectivePath.Path)
    (denominatorNonzero : (denominatorNorm path).isZero = false) :
    (denominatorNorm path).toPolynomial ≠ 0 :=
  FTA.ComputablePolynomial.DensePolynomial.toPolynomial_ne_zero_of_isZero_false
    denominatorNonzero

private theorem denominatorNorm_sparse_degree_le
    (path : ProjectivePath.Path)
    (denominatorNonzero : (denominatorNorm path).isZero = false) :
    (denominatorNorm path).toPolynomial.natDegree ≤
      (denominatorNorm path).natDegree := by
  rw [FTA.ComputablePolynomial.DensePolynomial.natDegree_toPolynomial
    denominatorNonzero]

/-- A computable affine parameter in the `index`th unit interval at which the
path denominator is nonzero.  The bounded search uses the denominator norm's
own degree, so it neither retries indefinitely nor needs a global resource
limit. -/
private def safePathParameter
    (path : ProjectivePath.Path)
    (denominatorNonzero : (denominatorNorm path).isZero = false)
    (index : ℕ) : ℚ :=
  FTA.SafeCandidates.centralSearchValue (denominatorNorm path)
    (denominatorNorm path).natDegree
    (a := (index : ℚ)) (b := (index : ℚ) + 1)
    (unitIntervalProper index)
    (denominatorNorm_sparse_nonzero path denominatorNonzero)
    (denominatorNorm_sparse_degree_le path denominatorNonzero)

private theorem safePathParameter_spec
    (path : ProjectivePath.Path)
    (denominatorNonzero : (denominatorNorm path).isZero = false)
    (index : ℕ) :
    (denominatorNorm path).eval
        (safePathParameter path denominatorNonzero index) ≠ 0 ∧
      (index : ℚ) < safePathParameter path denominatorNonzero index ∧
      safePathParameter path denominatorNonzero index < (index : ℚ) + 1 := by
  have specification := FTA.SafeCandidates.centralSearchValue_spec
    (denominatorNorm path) (denominatorNorm path).natDegree
    (a := (index : ℚ)) (b := (index : ℚ) + 1)
    (unitIntervalProper index)
    (denominatorNorm_sparse_nonzero path denominatorNonzero)
    (denominatorNorm_sparse_degree_le path denominatorNonzero)
  rcases specification with ⟨nonzero, lower, upper⟩
  refine ⟨nonzero, ?_, ?_⟩
  · have lower' : FTA.SafeCandidates.centralLeft
        (index : ℚ) ((index : ℚ) + 1) <
          safePathParameter path denominatorNonzero index := by
      simpa only [safePathParameter] using lower
    dsimp [FTA.SafeCandidates.centralLeft] at lower'
    linarith
  · have upper' : safePathParameter path denominatorNonzero index <
        FTA.SafeCandidates.centralRight
          (index : ℚ) ((index : ℚ) + 1) := by
      simpa only [safePathParameter] using upper
    dsimp [FTA.SafeCandidates.centralRight] at upper'
    linarith

private theorem safePathParameter_denominator_ne
    (path : ProjectivePath.Path)
    (denominatorNonzero : (denominatorNorm path).isZero = false)
    (index : ℕ) :
    path.denominator.eval (FTA.PathPolynomial.ofRat
      (safePathParameter path denominatorNonzero index)) ≠ 0 := by
  have normNonzero := (safePathParameter_spec path denominatorNonzero index).1
  intro zero
  apply normNonzero
  rw [eval_denominatorNorm, zero]
  simp [CCL.GaussianRat.normSq]

private theorem safePathParameter_injective
    (path : ProjectivePath.Path)
    (denominatorNonzero : (denominatorNorm path).isZero = false) :
    Function.Injective (safePathParameter path denominatorNonzero) := by
  apply StrictMono.injective
  intro left right less
  have leftBounds :=
    (safePathParameter_spec path denominatorNonzero left).2
  have rightBounds :=
    (safePathParameter_spec path denominatorNonzero right).2
  have separated : (left : ℚ) + 1 ≤ (right : ℚ) := by
    exact_mod_cast Nat.succ_le_of_lt less
  linarith

private theorem unitCircleParameter_of_value (parameter : ℚ) :
    (unitCircleParam parameter).im /
        (1 + (unitCircleParam parameter).re) = parameter := by
  have denominatorNonzero : 1 + parameter ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg parameter]
  simp only [unitCircleParam, unitCircleDenominator]
  field_simp [denominatorNonzero]
  ring

private theorem unitCircleParam_injective :
    Function.Injective unitCircleParam := by
  intro left right equality
  rw [← unitCircleParameter_of_value left,
    ← unitCircleParameter_of_value right, equality]

private theorem reciprocalUnitCircleParameter_of_value (parameter : ℚ) :
    (reciprocalUnitCircleParam parameter).im /
        (1 - (reciprocalUnitCircleParam parameter).re) = parameter := by
  have denominatorNonzero : 1 + parameter ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg parameter]
  simp only [reciprocalUnitCircleParam]
  field_simp [denominatorNonzero]
  ring

private theorem reciprocalUnitCircleParam_injective :
    Function.Injective reciprocalUnitCircleParam := by
  intro left right equality
  rw [← reciprocalUnitCircleParameter_of_value left,
    ← reciprocalUnitCircleParameter_of_value right, equality]

private theorem scaledCirclePath_value_injective
    (scaleValue : QI) (scaleNonzero : scaleValue ≠ 0) :
    Function.Injective (CCLBoundaryPath.scaledCirclePath scaleValue).value := by
  intro left right equality
  rw [CCLBoundaryPath.scaledCirclePath_value,
    CCLBoundaryPath.scaledCirclePath_value] at equality
  exact unitCircleParam_injective (mul_left_cancel₀ scaleNonzero equality)

private theorem reciprocalScaledCirclePath_value_injective
    (scaleValue : QI) (scaleNonzero : scaleValue ≠ 0) :
    Function.Injective
      (CCLBoundaryPath.reciprocalScaledCirclePath scaleValue).value := by
  intro left right equality
  rw [CCLBoundaryPath.reciprocalScaledCirclePath_value,
    CCLBoundaryPath.reciprocalScaledCirclePath_value] at equality
  exact reciprocalUnitCircleParam_injective
    (mul_left_cancel₀ scaleNonzero equality)

private theorem linePath_value_injective
    (base direction : QI) (directionNonzero : direction ≠ 0) :
    Function.Injective (CCLBoundaryPath.linePath base direction).value := by
  intro left right equality
  rw [CCLBoundaryPath.linePath_value,
    CCLBoundaryPath.linePath_value] at equality
  have products : CCLGeometry.ofRat left * direction =
      CCLGeometry.ofRat right * direction := add_left_cancel equality
  have parameters : CCLGeometry.ofRat left = CCLGeometry.ofRat right :=
    mul_right_cancel₀ directionNonzero products
  exact congrArg GaussianRat.re parameters

/-- Acting by an invertible adjugate preserves injectivity wherever the
acted path remains affine. -/
private theorem actedPath_value_injective
    (matrix : Mat2 QI) (path : ProjectivePath.Path)
    (determinantNonzero : determinant matrix ≠ 0)
    (sourceDenominator : ∀ parameter : ℚ,
      path.denominator.eval (FTA.PathPolynomial.ofRat parameter) ≠ 0)
    (sourceInjective : Function.Injective path.value)
    {left right : ℚ}
    (leftDenominator :
      (CCLBoundaryPath.actPath (adjugate matrix) path).denominator.eval
        (FTA.PathPolynomial.ofRat left) ≠ 0)
    (rightDenominator :
      (CCLBoundaryPath.actPath (adjugate matrix) path).denominator.eval
        (FTA.PathPolynomial.ofRat right) ≠ 0)
    (equality :
      (CCLBoundaryPath.actPath (adjugate matrix) path).value left =
        (CCLBoundaryPath.actPath (adjugate matrix) path).value right) :
    left = right := by
  have leftHomographic :=
    CCLBoundaryPath.homographic_denominator_ne_of_actPath
      (adjugate matrix) path left (sourceDenominator left) leftDenominator
  have rightHomographic :=
    CCLBoundaryPath.homographic_denominator_ne_of_actPath
      (adjugate matrix) path right (sourceDenominator right) rightDenominator
  have adjugateDeterminant : (adjugate matrix).det ≠ 0 := by
    change determinant (adjugate matrix) ≠ 0
    rw [CCLBranchPlan.determinant_adjugate]
    exact determinantNonzero
  apply sourceInjective
  apply RawParserSemantics.homographic_injective (adjugate matrix)
    adjugateDeterminant leftHomographic rightHomographic
  simpa only [CCLBoundaryPath.actPath_value _ _ _
      (sourceDenominator left),
    CCLBoundaryPath.actPath_value _ _ _ (sourceDenominator right)] using equality

/-- Each bounded parser chart is one-to-one on its affine parameters. -/
private theorem boundedChart_value_injective
    {source : BoundarySource} (chart : BoundedChart source)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (nondegenerate : source.ParametrizationNondegenerate)
    {left right : ℚ}
    (leftDenominator : chart.path.denominator.eval
      (FTA.PathPolynomial.ofRat left) ≠ 0)
    (rightDenominator : chart.path.denominator.eval
      (FTA.PathPolynomial.ofRat right) ≠ 0)
    (equality : chart.path.value left = chart.path.value right) :
    left = right := by
  cases source with
  | norm matrix scaleValue =>
      have scaleNonzero : scaleValue ≠ 0 := by
        simpa [BoundarySource.ParametrizationNondegenerate] using nondegenerate
      have member := chart.pathMember
      simp [BoundarySource.paths] at member
      rcases member with primary | reciprocal
      · rw [primary] at leftDenominator rightDenominator equality
        apply actedPath_value_injective matrix
          (CCLBoundaryPath.scaledCirclePath scaleValue) determinantNonzero
            (fun parameter => by
              simpa [CCLBoundaryPath.scaledCirclePath,
                CCLBoundaryPath.scalePath] using
                CCLBoundaryPath.unitCirclePath_denominator_ne parameter)
            (scaledCirclePath_value_injective scaleValue scaleNonzero)
            leftDenominator rightDenominator
        simpa only [CCLBoundaryPath.inverseScaledCirclePath] using equality
      · rw [reciprocal] at leftDenominator rightDenominator equality
        apply actedPath_value_injective matrix
          (CCLBoundaryPath.reciprocalScaledCirclePath scaleValue)
            determinantNonzero
            (fun parameter => by
              simpa [CCLBoundaryPath.reciprocalScaledCirclePath,
                CCLBoundaryPath.scalePath] using
                CCLBoundaryPath.reciprocalUnitCirclePath_denominator_ne
                  parameter)
            (reciprocalScaledCirclePath_value_injective scaleValue scaleNonzero)
            leftDenominator rightDenominator
        simpa only [CCLBoundaryPath.inverseReciprocalScaledCirclePath] using
          equality
  | real matrix threshold =>
      have member := chart.pathMember
      simp [BoundarySource.paths] at member
      rw [member] at leftDenominator rightDenominator equality
      apply actedPath_value_injective matrix
        (CCLBoundaryPath.linePath ⟨threshold, 0⟩ ⟨0, 1⟩)
          determinantNonzero
          (fun parameter =>
            CCLBoundaryPath.linePath_denominator_ne _ _ parameter)
          (linePath_value_injective _ _ (by
            intro zero
            have imaginary := congrArg GaussianRat.im zero
            norm_num at imaginary))
          leftDenominator rightDenominator
      simpa [CCLBoundaryPath.inverseRealBoundaryPath,
        CCLBoundaryPath.inverseLinePath] using equality
  | imag matrix threshold =>
      have member := chart.pathMember
      simp [BoundarySource.paths] at member
      rw [member] at leftDenominator rightDenominator equality
      apply actedPath_value_injective matrix
        (CCLBoundaryPath.linePath ⟨0, threshold⟩ ⟨1, 0⟩)
          determinantNonzero
          (fun parameter =>
            CCLBoundaryPath.linePath_denominator_ne _ _ parameter)
          (linePath_value_injective _ _ (by
            intro zero
            have real := congrArg GaussianRat.re zero
            norm_num at real))
          leftDenominator rightDenominator
      simpa [CCLBoundaryPath.inverseImagBoundaryPath,
        CCLBoundaryPath.inverseLinePath] using equality

/-- A nonzero univariate complex polynomial cannot vanish identically on a
nondegenerate bounded rational boundary chart.  Finite bounded searches in
successive unit intervals construct one more distinct affine root than the
polynomial's natural degree, which forces the sparse polynomial to be zero. -/
theorem BoundedChart.clearedCoordinatesNonzero
    {p : GaussianPolynomial} {source : BoundarySource}
    (chart : BoundedChart source)
    (polynomialNonzero : p.toPolynomial ≠ 0)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (nondegenerate : source.ParametrizationNondegenerate) :
    (clearedReal p chart.path).isZero = false ∨
      (clearedImag p chart.path).isZero = false := by
  by_cases realZero : (clearedReal p chart.path).isZero = true
  · by_cases imagZero : (clearedImag p chart.path).isZero = true
    · have denominatorPolynomialNonzero :
          (denominatorNorm chart.path).isZero = false :=
        chart.denominatorNorm_isZero_false determinantNonzero nondegenerate
      let degree := p.toPolynomial.natDegree
      let parameter : Fin (degree + 1) → ℚ := fun index =>
        safePathParameter chart.path denominatorPolynomialNonzero index.val
      let point : Fin (degree + 1) → QI := fun index =>
        chart.path.value (parameter index)
      have denominatorAt (index : Fin (degree + 1)) :
          chart.path.denominator.eval
            (FTA.PathPolynomial.ofRat (parameter index)) ≠ 0 := by
        exact safePathParameter_denominator_ne chart.path
          denominatorPolynomialNonzero index.val
      have pointInjective : Function.Injective point := by
        intro left right equality
        apply Fin.ext
        apply safePathParameter_injective chart.path
          denominatorPolynomialNonzero
        exact boundedChart_value_injective chart determinantNonzero
          nondegenerate (denominatorAt left) (denominatorAt right) equality
      let points := List.ofFn point
      have pointsNodup : points.Nodup :=
        List.nodup_ofFn.mpr pointInjective
      have polynomialZero : p.toPolynomial = 0 := by
        apply FTA.ComputablePolynomial.DensePolynomial.polynomial_eq_zero_of_eval_zero_on_list
          p.toPolynomial points pointsNodup
            (by simp only [points, List.length_ofFn, degree]; omega)
        intro root rootMember
        change root ∈ List.ofFn point at rootMember
        rw [List.mem_ofFn'] at rootMember
        rcases rootMember with ⟨index, rfl⟩
        have exactRoot := ProjectivePath.eval_eq_zero_of_cleared_isZero p
          chart.path (parameter index) (denominatorAt index) realZero imagZero
        rw [FTA.ComputablePolynomial.DensePolynomial.eval_toPolynomial]
        simpa only [point] using exactRoot
      exact (polynomialNonzero polynomialZero).elim
    · exact Or.inr (Bool.eq_false_of_not_eq_true imagZero)
  · exact Or.inl (Bool.eq_false_of_not_eq_true realZero)

/-- Exact roots exposed by identically-zero global event charts, independent
of parser-owner re-isolation or whether that event owns either child formula. -/
def globalIdenticallyZeroRoots
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} (state : RawParser.State)
    (separation : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    List (ExactRationalRoot p) :=
  (separatedRelevantCurveEvents p state separation).filterMap fun sourceEvent =>
    match ProjectivePath.decideClearedCoordinates p
        sourceEvent.partition.entry.chart.path with
    | .identicallyZero realZero imagZero =>
        some
          (FTA.CCLEventTerminal.RelevantCurveEvent.identicallyZeroRoot
            sourceEvent.event realZero imagZero)
    | .nonzero _ => none

/-- Exact roots exposed by identically-zero cell-local guarded event charts,
again before parser-owner re-isolation. -/
def guardedIdenticallyZeroRoots
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} (state : RawParser.State)
    (separation : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    List (ExactRationalRoot p) :=
  (separatedSourceGuardCurveEvents p state separation).filterMap fun sourceEvent =>
    match ProjectivePath.decideClearedCoordinates p
        sourceEvent.sourceCell.partition.entry.chart.path with
    | .identicallyZero realZero imagZero =>
        some
          (FTA.CCLEventTerminal.RelevantCurveEvent.identicallyZeroRoot
            sourceEvent.event realZero imagZero)
    | .nonzero _ => none

/-- First exact root from either finite event representation. -/
def firstIdenticallyZeroRoot?
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} (state : RawParser.State)
    (separation : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    Option (ExactRationalRoot p) :=
  (globalIdenticallyZeroRoots state separation ++
    guardedIdenticallyZeroRoots state separation).head?

/-- Localized counterparts of the exact-root scan.  Re-isolated input-event
cells supply a rational point strictly inside the denominator-separated root
box, so later layers retain the region that discovered the terminal. -/
def globalLocalizedIdenticallyZeroRoots
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} (state : RawParser.State)
    (separation : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    List (LocalizedExactRationalRoot p separation.state.box) :=
  (separatedInputEventCells p state separation).filterMap fun candidate =>
    match ProjectivePath.decideClearedCoordinates p
        candidate.sourceEvent.partition.entry.chart.path with
    | .identicallyZero realZero imagZero =>
        some (FTA.CCLEventTerminal.InputEventCell.identicallyZeroLocalizedRoot
          candidate.inputCell separation.state.clearance realZero imagZero)
    | .nonzero _ => none

def guardedLocalizedIdenticallyZeroRoots
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} (state : RawParser.State)
    (separation : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    List (LocalizedExactRationalRoot p separation.state.box) :=
  (separatedGuardInputEventCells p state separation).filterMap fun candidate =>
    match ProjectivePath.decideClearedCoordinates p
        candidate.sourceEvent.sourceCell.partition.entry.chart.path with
    | .identicallyZero realZero imagZero =>
        some (FTA.CCLEventTerminal.InputEventCell.identicallyZeroLocalizedRoot
          candidate.inputCell separation.state.clearance realZero imagZero)
    | .nonzero _ => none

def firstLocalizedIdenticallyZeroRoot?
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} (state : RawParser.State)
    (separation : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    Option (LocalizedExactRationalRoot p separation.state.box) :=
  (globalLocalizedIdenticallyZeroRoots state separation ++
    guardedLocalizedIdenticallyZeroRoots state separation).head?

/-- A relevant event retained by an identically-zero terminal guard cell is
visible to the event-level terminal scan.  In particular, it cannot coexist
with the `none` result retained by a no-event opening. -/
theorem firstIdenticallyZeroRoot?_ne_none_of_guard_relevant
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (separation : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (sourceCell : SourceEventGuardCell p separation.state.box)
    (sourceMember : sourceCell ∈ separatedEventGuardCells p state separation)
    (realZero : (clearedReal p
      sourceCell.partition.entry.chart.path).isZero = true)
    (imagZero : (clearedImag p
      sourceCell.partition.entry.chart.path).isZero = true)
    (event : RelevantCurveEvent p
      sourceCell.partition.entry.chart.path separation.state.box)
    (eventMember : event ∈
      CCLBranchEvent.EventGuardCell.relevantCurveEvents
        sourceCell.item.cell) :
    firstIdenticallyZeroRoot? state separation ≠ Option.none := by
  let sourceEvent : SourceGuardCurveEvent p separation.state.box :=
    ⟨sourceCell, event, eventMember⟩
  have sourceEventMember : sourceEvent ∈
      separatedSourceGuardCurveEvents p state separation := by
    simpa only [separatedSourceGuardCurveEvents, sourceEvent] using
      sourceGuardCurveEvent_mem_of_cell_event sourceCell sourceMember event
        eventMember
  let root :=
    FTA.CCLEventTerminal.RelevantCurveEvent.identicallyZeroRoot
      event realZero imagZero
  have rootMember : root ∈ guardedIdenticallyZeroRoots state separation := by
    rw [guardedIdenticallyZeroRoots, List.mem_filterMap]
    refine ⟨sourceEvent, sourceEventMember, ?_⟩
    simp [ProjectivePath.decideClearedCoordinates, realZero, imagZero,
      sourceEvent, root]
  have combinedNonempty :
      globalIdenticallyZeroRoots state separation ++
        guardedIdenticallyZeroRoots state separation ≠ [] := by
    intro empty
    have : root ∈ ([] : List (ExactRationalRoot p)) := by
      rw [← empty]
      exact List.mem_append_right _ rootMember
    simp at this
  simpa [firstIdenticallyZeroRoot?] using combinedNonempty

theorem firstLocalizedIdenticallyZeroRoot?_ne_none_of_guard_relevant
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (separation : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (sourceCell : SourceEventGuardCell p separation.state.box)
    (sourceMember : sourceCell ∈ separatedEventGuardCells p state separation)
    (realZero : (clearedReal p
      sourceCell.partition.entry.chart.path).isZero = true)
    (imagZero : (clearedImag p
      sourceCell.partition.entry.chart.path).isZero = true)
    (event : RelevantCurveEvent p
      sourceCell.partition.entry.chart.path separation.state.box)
    (eventMember : event ∈
      CCLBranchEvent.EventGuardCell.relevantCurveEvents sourceCell.item.cell) :
    firstLocalizedIdenticallyZeroRoot? state separation ≠ Option.none := by
  let sourceEvent : SourceGuardCurveEvent p separation.state.box :=
    ⟨sourceCell, event, eventMember⟩
  have sourceEventMember : sourceEvent ∈
      separatedSourceGuardCurveEvents p state separation := by
    exact sourceGuardCurveEvent_mem_of_cell_event sourceCell sourceMember event
      eventMember
  rcases separatedGuardInputEventCells_exists_of_sourceEvent_mem separation
      sourceEvent sourceEventMember with ⟨candidate, candidateMember, sourceEq⟩
  have candidateRealZero : (clearedReal p
      candidate.sourceEvent.sourceCell.partition.entry.chart.path).isZero =
        true := by
    rw [sourceEq]
    exact realZero
  have candidateImagZero : (clearedImag p
      candidate.sourceEvent.sourceCell.partition.entry.chart.path).isZero =
        true := by
    rw [sourceEq]
    exact imagZero
  let localized :=
    FTA.CCLEventTerminal.InputEventCell.identicallyZeroLocalizedRoot
      candidate.inputCell separation.state.clearance candidateRealZero
        candidateImagZero
  have rootMember :
      localized ∈
        guardedLocalizedIdenticallyZeroRoots state separation := by
    rw [guardedLocalizedIdenticallyZeroRoots, List.mem_filterMap]
    refine ⟨candidate, candidateMember, ?_⟩
    simp [ProjectivePath.decideClearedCoordinates, candidateRealZero,
      candidateImagZero, localized]
  have combinedNonempty :
      globalLocalizedIdenticallyZeroRoots state separation ++
        guardedLocalizedIdenticallyZeroRoots state separation ≠ [] := by
    intro empty
    have : localized ∈
        ([] : List (LocalizedExactRationalRoot p separation.state.box)) := by
      rw [← empty]
      exact List.mem_append_right _ rootMember
    simp at this
  simpa [firstLocalizedIdenticallyZeroRoot?] using combinedNonempty

/-- An identically-zero separated guard chart yields an exact rational root
without any relevance or owner classification.  The terminal cell's lower
endpoint clears the combined arc guard; separated-chart provenance proves the
denominator-norm polynomial is nonzero, so that endpoint is affine. -/
def exactRootOfSeparatedIdenticallyZeroGuardCell
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (separation : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (stateDeterminant : determinant state.matrix ≠ 0)
    (sourceCell : SourceEventGuardCell p separation.state.box)
    (sourceMember : sourceCell ∈ separatedEventGuardCells p state separation)
    (realZero : (clearedReal p
      sourceCell.partition.entry.chart.path).isZero = true)
    (imagZero : (clearedImag p
      sourceCell.partition.entry.chart.path).isZero = true) :
    ExactRationalRoot p := by
  have partitionMember : sourceCell.partition ∈
      separatedChartPartitions p state separation := by
    apply sourceEventGuardCell_partition_mem_of_mem
    simpa only [separatedEventGuardCells] using sourceMember
  have entryMember : sourceCell.partition.entry ∈
      separatedCharts state separation := by
    apply SourceChartPartition.entry_mem_of_mem_build
    simpa only [separatedChartPartitions] using partitionMember
  have sourceMemberPlan : sourceCell.partition.entry.source ∈
      CCLBranchPlan.inputPlan state :=
    separatedChart_source_mem_inputPlan entryMember
  have sourceDeterminant :
      determinant sourceCell.partition.entry.source.matrix ≠ 0 :=
    CCLBranchPlan.inputPlan_determinant_ne state sourceMemberPlan
      stateDeterminant
  have sourceNondegenerate :
      sourceCell.partition.entry.source.ParametrizationNondegenerate :=
    CCLBranchPlan.inputPlan_parametrizationNondegenerate state sourceMemberPlan
  have denominatorPolynomialNonzero :
      (denominatorNorm
        sourceCell.partition.entry.chart.path).isZero = false :=
    sourceCell.partition.entry.chart.denominatorNorm_isZero_false
      sourceDeterminant sourceNondegenerate
  let parameter := sourceCell.item.cell.cell.interval.lower
  have denominatorNormNonzero :
      (denominatorNorm sourceCell.partition.entry.chart.path).eval
        parameter ≠ 0 :=
    eval_ne_zero_of_mem_arcPolynomials
      (denominatorNorm_mem_arcPolynomials p
        sourceCell.partition.entry.chart.path separation.state.box)
      denominatorPolynomialNonzero
      (eventGuardCell_arcGuard_lowerClear sourceCell.item.cell)
  have pathDenominator :
      sourceCell.partition.entry.chart.path.denominator.eval
        (PathPolynomial.ofRat parameter) ≠ 0 := by
    intro zero
    apply denominatorNormNonzero
    rw [eval_denominatorNorm, zero]
    simp [CCL.GaussianRat.normSq]
  let point := sourceCell.partition.entry.chart.path.value parameter
  exact
    { point := point
      root := ProjectivePath.eval_eq_zero_of_cleared_isZero p
        sourceCell.partition.entry.chart.path parameter pathDenominator
          realZero imagZero }

/-- Every guard cell generated from a separated parser chart inherits the
chart's constructive nonvanishing result for a nonzero input polynomial. -/
theorem clearedCoordinatesNonzeroOfSeparatedGuardCell
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (separation : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (stateDeterminant : determinant state.matrix ≠ 0)
    (sourceCell : SourceEventGuardCell p separation.state.box)
    (sourceMember : sourceCell ∈ separatedEventGuardCells p state separation)
    (polynomialNonzero : p.toPolynomial ≠ 0) :
    (clearedReal p sourceCell.partition.entry.chart.path).isZero = false ∨
      (clearedImag p
        sourceCell.partition.entry.chart.path).isZero = false := by
  have partitionMember : sourceCell.partition ∈
      separatedChartPartitions p state separation := by
    apply sourceEventGuardCell_partition_mem_of_mem
    simpa only [separatedEventGuardCells] using sourceMember
  have entryMember : sourceCell.partition.entry ∈
      separatedCharts state separation := by
    apply SourceChartPartition.entry_mem_of_mem_build
    simpa only [separatedChartPartitions] using partitionMember
  have sourceMemberPlan : sourceCell.partition.entry.source ∈
      CCLBranchPlan.inputPlan state :=
    separatedChart_source_mem_inputPlan entryMember
  have sourceDeterminant :
      determinant sourceCell.partition.entry.source.matrix ≠ 0 :=
    CCLBranchPlan.inputPlan_determinant_ne state sourceMemberPlan
      stateDeterminant
  have sourceNondegenerate :
      sourceCell.partition.entry.source.ParametrizationNondegenerate :=
    CCLBranchPlan.inputPlan_parametrizationNondegenerate state sourceMemberPlan
  exact FTA.CCLCoupledController.BoundedChart.clearedCoordinatesNonzero
    sourceCell.partition.entry.chart polynomialNonzero sourceDeterminant
      sourceNondegenerate

/-- Fully specialized opening result for the current coupled word.  Only the
three geometric branches remain; parser construction, invertibility, and the
zero/nonzero terminal split are no longer caller obligations. -/
inductive Decision
    (p : GaussianPolynomial) (ambient : RatBox)
    (current : CCLCoupledTrack.State p ambient) where
  | zero (root : p.eval 0 = 0)
  | terminalPole (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0)
      (contains : current.numerical.box.Contains point)
      (strict : current.numerical.box.StrictContains point)
      (denominatorZero :
        (adjugate (RawParser.parse current.word).matrix).c * point +
          (adjugate (RawParser.parse current.word).matrix).d = 0)
  | eventOwner
      (separation : CCLDenominator.SeparationOutput p ambient
        current.numerical
        (adjugate (RawParser.parse current.word).matrix))
      (selected : SelectedEventCount separation)
  | guardEventOwner
      (separation : CCLDenominator.SeparationOutput p ambient
        current.numerical
        (adjugate (RawParser.parse current.word).matrix))
      (selected : SelectedGuardEventCount separation)
  | noEventOwner
      (separation : CCLDenominator.SeparationOutput p ambient
        current.numerical
        (adjugate (RawParser.parse current.word).matrix))
      (none : ∀ candidate ∈ separatedInputEventCells p
        (RawParser.parse current.word) separation,
        candidate.inputCell.ownerChecks = (false, false))
      (guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
        (RawParser.parse current.word) separation,
        candidate.inputCell.ownerChecks = (false, false))
      (clear : ClearRefinementDecision p ambient current.numerical
        (RawParser.parse current.word) separation)

/-- Run the complete finite opening analysis at a coupled state. -/
def analyze
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient)
    (current : CCLCoupledTrack.State p ambient)
    (clearOwnerLabel : Bool) : Decision p ambient current :=
  match analyzeBranchFamilies track current.numerical
      (RawParser.parse current.word) (by
        simpa only [determinant, Mat2.det] using
          RawParser.parse_det_ne current.word) clearOwnerLabel with
  | .terminalPole point root contains strict denominatorZero => by
      by_cases zero : point = 0
      · subst point
        exact .zero root
      · exact .terminalPole point root zero contains strict denominatorZero
  | .eventOwner separation selected =>
      .eventOwner separation selected
  | .guardEventOwner separation selected =>
      .guardEventOwner separation selected
  | .noEventOwner separation allNone guardNone clear =>
      .noEventOwner separation allNone guardNone clear

/-- Opening result with every exact decoder-pole root already converted to
the terminal payload consumed by `Machine.step`.  Only the two geometric
branches remain pending. -/
inductive Opening
    (p : GaussianPolynomial) (ambient : RatBox)
    (current : CCLCoupledTrack.State p ambient) where
  | ready (result : CCLCoupledTrack.StepResult current)
  | eventOwner
      (separation : CCLDenominator.SeparationOutput p ambient
        current.numerical
        (adjugate (RawParser.parse current.word).matrix))
      (selected : SelectedEventCount separation)
  | guardEventOwner
      (separation : CCLDenominator.SeparationOutput p ambient
        current.numerical
        (adjugate (RawParser.parse current.word).matrix))
      (selected : SelectedGuardEventCount separation)
  | noEventOwner
      (separation : CCLDenominator.SeparationOutput p ambient
        current.numerical
        (adjugate (RawParser.parse current.word).matrix))
      (none : ∀ candidate ∈ separatedInputEventCells p
        (RawParser.parse current.word) separation,
        candidate.inputCell.ownerChecks = (false, false))
      (guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
        (RawParser.parse current.word) separation,
        candidate.inputCell.ownerChecks = (false, false))
      (noIdenticallyZero : firstIdenticallyZeroRoot?
        (RawParser.parse current.word) separation = Option.none)
      (arcs : List (BoundaryArc p)) (evidence : AllClear p arcs)
      (alignment : ClearFamilyAlignment p separation.state.box
        (separatedRelevantClearCells p (RawParser.parse current.word)
          separation) arcs)
      (guardCurve : GuardCurveFamilyDecision p separation.state.box
        (separatedEventGuardCells p (RawParser.parse current.word) separation))
      (terminal : CCLTerminalSeparation.SeparationOutput p ambient
        (RawParser.parse current.word) separation.state [false, true])
      (output : RefinementOutput p ambient terminal.numerical evidence)
  | guardClear
      (separation : CCLDenominator.SeparationOutput p ambient
        current.numerical
        (adjugate (RawParser.parse current.word).matrix))
      (none : ∀ candidate ∈ separatedInputEventCells p
        (RawParser.parse current.word) separation,
        candidate.inputCell.ownerChecks = (false, false))
      (guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
        (RawParser.parse current.word) separation,
        candidate.inputCell.ownerChecks = (false, false))
      (noIdenticallyZero : firstIdenticallyZeroRoot?
        (RawParser.parse current.word) separation = Option.none)
      (arcs : List (BoundaryArc p)) (evidence : AllClear p arcs)
      (alignment : ClearFamilyAlignment p separation.state.box
        (separatedRelevantClearCells p (RawParser.parse current.word)
          separation) arcs)
      (terminal : CCLTerminalSeparation.SeparationOutput p ambient
        (RawParser.parse current.word) separation.state [false, true])
      (output : RefinementOutput p ambient terminal.numerical evidence)
      (guardEvidence : AllGuardClear p separation.state.box
        (separatedEventGuardCells p (RawParser.parse current.word) separation))
      (guardOutput : GuardRefinementOutput p ambient output.state guardEvidence)

/-- Execute the opening analysis and finish both exact terminal variants.
A nonzero terminal carries its independently computed complete encoder word;
terminal discovery does not pretend to consume an additional branch bit. -/
def openStep
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient)
    (current : CCLCoupledTrack.State p ambient)
    (clearOwnerLabel : Bool) : Opening p ambient current :=
  match analyze track current clearOwnerLabel with
  | .zero root => .ready (.zero root)
  | .terminalPole point root nonzero _contains _strict _denominatorZero =>
      .ready (.terminal point root nonzero
        (RationalEncoder.encode point nonzero) rfl)
  | .eventOwner separation selected =>
      match selected.decision with
      | .identicallyZero realZero imagZero => by
          let exactRoot :=
            FTA.CCLEventTerminal.InputEventCell.identicallyZeroRoot
              selected.candidate.inputCell realZero imagZero
          by_cases zero : exactRoot.point = 0
          · exact .ready (.zero (by simpa only [zero] using exactRoot.root))
          · exact .ready (.terminal exactRoot.point exactRoot.root zero
              (RationalEncoder.encode exactRoot.point zero) rfl)
      | .positive _evidence =>
          .eventOwner separation selected
  | .guardEventOwner separation selected =>
      match selected.decision with
      | .identicallyZero realZero imagZero => by
          let exactRoot :=
            FTA.CCLEventTerminal.InputEventCell.identicallyZeroRoot
              selected.candidate.inputCell realZero imagZero
          by_cases zero : exactRoot.point = 0
          · exact .ready (.zero (by simpa only [zero] using exactRoot.root))
          · exact .ready (.terminal exactRoot.point exactRoot.root zero
              (RationalEncoder.encode exactRoot.point zero) rfl)
      | .positive _evidence =>
          .guardEventOwner separation selected
  | .noEventOwner separation allNone guardNone clear =>
      match clear with
      | .terminal point _contains root => by
          by_cases zero : point = 0
          · subst point
            exact .ready (.zero root)
          · exact .ready (.terminal point root zero
              (RationalEncoder.encode point zero) rfl)
      | .refined arcs evidence alignment _output =>
          match rootCheck : firstIdenticallyZeroRoot?
              (RawParser.parse current.word) separation with
          | some exactRoot => by
              by_cases zero : exactRoot.point = 0
              · exact .ready (.zero (by
                  simpa only [zero] using exactRoot.root))
              · exact .ready (.terminal exactRoot.point exactRoot.root zero
                  (RationalEncoder.encode exactRoot.point zero) rfl)
          | none =>
              match CCLTerminalSeparation.separate track
                  (RawParser.parse current.word) separation.state with
              | .terminal point root _contains => by
                  by_cases zero : point = 0
                  · subst point
                    exact .ready (.zero root)
                  · exact .ready (.terminal point root zero
                      (RationalEncoder.encode point zero) rfl)
              | .separated terminal =>
                  let output := refineForClearance track terminal.numerical evidence
                  let guardCurve := decideSeparatedGuardCurveFamily
                    (RawParser.parse current.word) separation (by
                      simpa only [determinant, Mat2.det] using
                        RawParser.parse_det_ne current.word)
                  .noEventOwner separation allNone guardNone rootCheck arcs
                    evidence alignment guardCurve terminal output

/-- The aligned all-clear output excludes the chart segment of every source
cell retained by the separated finite pipeline.  This is the coverage fact
that was unavailable when the controller remembered only equal list lengths. -/
theorem alignedClearCell_excluded
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {arcs : List (BoundaryArc p)} {evidence : AllClear p arcs}
    (alignment : ClearFamilyAlignment p separation.state.box
      (separatedRelevantClearCells p (RawParser.parse current.word)
        separation) arcs)
    (output : RefinementOutput p ambient separation.state evidence)
    {candidate : SourceRelevantClearCell p separation.state.box}
    (member : candidate ∈ separatedRelevantClearCells p
      (RawParser.parse current.word) separation) :
    ¬∃ t : ℚ,
      candidate.relevant.cell.interval.lower ≤ t ∧
      t ≤ candidate.relevant.cell.interval.upper ∧
      output.state.box.Contains
        (candidate.sourceCell.partition.entry.chart.path.value t) := by
  rcases alignment.source_arc_of_mem member with
    ⟨arc, arcMember, _formEq, pathEq, intervalEq⟩
  have excluded := output.no_arc_intersection_of_mem arcMember
  simpa only [pathEq, intervalEq] using excluded

/-- Reverse boundary coverage closes the complete all-interior half: after
the aligned clearance refinement, any rational point of a parser-planned
boundary that remains in the winding box must be covered by an explicit
guarded event cell.  Thus no chart, partition, or relevance-filter gap is
left in the all-clear argument. -/
theorem alignedAllClear_boundary_point_has_guard_event
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {arcs : List (BoundaryArc p)} {evidence : AllClear p arcs}
    (alignment : ClearFamilyAlignment p separation.state.box
      (separatedRelevantClearCells p (RawParser.parse current.word)
        separation) arcs)
    (output : RefinementOutput p ambient separation.state evidence)
    (source : CCLBranchPlan.BoundarySource)
    (sourceMember : source ∈
      CCLBranchPlan.inputPlan (RawParser.parse current.word))
    (point : QI) (contains : output.state.box.Contains point)
    (boundary : source.form.eval point = 0) :
    ∃ sourceCell ∈ separatedEventGuardCells p
        (RawParser.parse current.word) separation,
      sourceCell.partition.entry.source = source ∧
      ∃ t : ℚ,
        sourceCell.partition.entry.chart.path.denominator.eval
          (PathPolynomial.ofRat t) ≠ 0 ∧
        sourceCell.partition.entry.chart.path.value t = point ∧
        sourceCell.item.cell.cell.interval.lower ≤ t ∧
        t ≤ sourceCell.item.cell.cell.interval.upper := by
  have stateDeterminant :
      determinant (RawParser.parse current.word).matrix ≠ 0 := by
    simpa only [determinant, Mat2.det] using
      RawParser.parse_det_ne current.word
  have containsSeparation : separation.state.box.Contains point :=
    output.refines.contains contains
  rcases separatedChartPartitions_guardCoverage_boundary_point
      stateDeterminant separation source sourceMember point
      containsSeparation boundary with
    ⟨partition, partitionMember, sourceEquality, t, pathDenominator,
      pathValue, coverage⟩
  cases coverage with
  | clear cell cellMember lower upper =>
      have holds :
          (boxConditions partition.entry.chart.path
            separation.state.box).HoldsAt t :=
        (contains_value_iff_holdsAt partition.entry.chart.path
          separation.state.box t pathDenominator).mp (by
            rw [pathValue]
            exact containsSeparation)
      rcases relevantClearCellsOfSourcePartitions_cover_of_clear
          (separatedChartPartitions p (RawParser.parse current.word)
            separation) partition partitionMember cell cellMember lower upper
          holds with
        ⟨candidate, candidateMember, partitionEquality, candidateLower,
          candidateUpper⟩
      have excluded := alignedClearCell_excluded alignment output
        candidateMember
      exact (excluded ⟨t, candidateLower, candidateUpper, by
        rw [partitionEquality, pathValue]
        exact contains⟩).elim
  | event planEquality cell cellMember lower upper =>
      let eventCoverage : GuardEventCoverage partition.plan t :=
        .event planEquality cell cellMember lower upper
      rcases eventCoverage.mem_eventGuardCellsOfSourcePartitions
          partitionMember with
        ⟨sourceCell, sourceCellMember, partitionEquality, eventLower,
          eventUpper⟩
      refine ⟨sourceCell, ?_, ?_, t, ?_, ?_, eventLower, eventUpper⟩
      · simpa only [separatedEventGuardCells] using sourceCellMember
      · rw [partitionEquality]
        exact sourceEquality
      · rw [partitionEquality]
        exact pathDenominator
      · rw [partitionEquality]
        exact pathValue

/-- Once the terminal guard cells themselves all carry zero-count clearance,
one additional finite guard refinement removes every parser-planned boundary
from the winding box.  Reverse chart coverage supplies the exact source cell
and parameter; the source-indexed guard certificate then gives the
quantitative contradiction directly. -/
theorem alignedAllClear_guardClear_excludes_boundary
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {arcs : List (BoundaryArc p)} {evidence : AllClear p arcs}
    (alignment : ClearFamilyAlignment p separation.state.box
      (separatedRelevantClearCells p (RawParser.parse current.word)
        separation) arcs)
    (output : RefinementOutput p ambient separation.state evidence)
    (guardEvidence : AllGuardClear p separation.state.box
      (separatedEventGuardCells p (RawParser.parse current.word) separation))
    (guardOutput : GuardRefinementOutput p ambient output.state guardEvidence)
    (source : CCLBranchPlan.BoundarySource)
    (sourceMember : source ∈
      CCLBranchPlan.inputPlan (RawParser.parse current.word))
    (point : QI) (contains : guardOutput.state.box.Contains point)
    (boundary : source.form.eval point = 0) : False := by
  have containsOutput : output.state.box.Contains point :=
    guardOutput.refines.contains contains
  rcases alignedAllClear_boundary_point_has_guard_event alignment output
      source sourceMember point containsOutput boundary with
    ⟨sourceCell, sourceCellMember, _sourceEquality, t, denominator,
      pathValue, lower, upper⟩
  obtain ⟨i, equality⟩ := List.mem_iff_get.mp sourceCellMember
  have pathContains : guardOutput.state.box.Contains
      (sourceCell.partition.entry.chart.path.value t) := by
    rw [pathValue]
    exact contains
  have excluded := guardOutput.excludes_guard_point i (t := t)
  rw [equality] at excluded
  have separationContains : separation.state.box.Contains
      (sourceCell.partition.entry.chart.path.value t) :=
    output.refines.contains (guardOutput.refines.contains pathContains)
  exact excluded lower upper denominator separationContains pathContains

/-- Pointwise nonvanishing form of the complete clear-family conclusion. -/
theorem alignedAllClear_guardClear_source_ne_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {arcs : List (BoundaryArc p)} {evidence : AllClear p arcs}
    (alignment : ClearFamilyAlignment p separation.state.box
      (separatedRelevantClearCells p (RawParser.parse current.word)
        separation) arcs)
    (output : RefinementOutput p ambient separation.state evidence)
    (guardEvidence : AllGuardClear p separation.state.box
      (separatedEventGuardCells p (RawParser.parse current.word) separation))
    (guardOutput : GuardRefinementOutput p ambient output.state guardEvidence)
    {source : CCLBranchPlan.BoundarySource}
    (sourceMember : source ∈
      CCLBranchPlan.inputPlan (RawParser.parse current.word))
    {point : QI} (contains : guardOutput.state.box.Contains point) :
    source.form.eval point ≠ 0 := by
  intro boundary
  exact alignedAllClear_guardClear_excludes_boundary alignment output
    guardEvidence guardOutput source sourceMember point contains boundary

/-- The all-`neither` owner certificate has its exact pointwise meaning on any
non-identically-zero rational chart root retained by the separated pipeline:
neither proposed child formula holds at that affine root. -/
theorem noEventOwner_rejects_nonzero_chart_root
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (none : ∀ candidate ∈ separatedInputEventCells p
      (RawParser.parse current.word) separation,
      candidate.inputCell.ownerChecks = (false, false))
    (partition : SourceChartPartition p separation.state.box)
    (partitionMember : partition ∈ separatedChartPartitions p
      (RawParser.parse current.word) separation)
    {t : ℚ} (lower : partition.entry.chart.interval.lower ≤ t)
    (upper : t ≤ partition.entry.chart.interval.upper)
    (clearedNonzero :
      (clearedReal p partition.entry.chart.path).isZero = false ∨
      (clearedImag p partition.entry.chart.path).isZero = false)
    (pathDenominator : partition.entry.chart.path.denominator.eval
      (PathPolynomial.ofRat t) ≠ 0)
    (polynomialZero : p.eval (partition.entry.chart.path.value t) = 0)
    (contains : separation.state.box.Contains
      (partition.entry.chart.path.value t)) :
    ∀ bit, ¬(inputAdvanceFormula (RawParser.parse current.word) bit).Holds
      (partition.entry.chart.path.value t) := by
  rcases separatedInputEventCells_covers_chart_root_nonzero partition
    partitionMember lower upper clearedNonzero pathDenominator polynomialZero
    contains with
    ⟨candidate, candidateMember, sourcePartition, cellLower, cellUpper,
      cellZero⟩
  subst partition
  have checks := none candidate candidateMember
  intro bit
  cases bit with
  | false =>
      intro holds
      have selected := (candidate.inputCell.false_ownerCheck_iff
        cellLower cellUpper cellZero).mpr holds
      rw [checks] at selected
      contradiction
  | true =>
      intro holds
      have selected := (candidate.inputCell.true_ownerCheck_iff
        cellLower cellUpper cellZero).mpr holds
      rw [checks] at selected
      contradiction

/-- A selected owner cell with an exact rational event parameter is already a
terminal polynomial root.  This removes rational boundary intersections from
the geometric owner-perturbation branch instead of manufacturing a spurious
additional bit. -/
def terminalOfSelectedRationalEvent
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventCount separation) (t : ℚ)
    (lower : (selected.candidate.inputCell.branch.computeEventSigns
      selected.candidate.inputCell.parent).refined.interval.lower ≤ t)
    (upper : t ≤ (selected.candidate.inputCell.branch.computeEventSigns
      selected.candidate.inputCell.parent).refined.interval.upper)
    (eventZero :
      selected.candidate.inputCell.branch.factor.polynomial.eval t = 0) :
    CCLCoupledTrack.StepResult current := by
  let point :=
    selected.candidate.sourceEvent.partition.entry.chart.path.value t
  have root : p.eval point = 0 :=
    selected.candidate.inputCell.polynomial_eval_eq_zero eventZero
  have _contains : separation.state.box.Contains point :=
    selected.candidate.inputCell.contains lower upper eventZero
  by_cases zero : point = 0
  · exact .zero (by simpa only [zero] using root)
  · exact .terminal point root zero (RationalEncoder.encode point zero) rfl

/-- One constructive owner-cell witness in a displayed nested winding box.
Besides representing the extended word, it retains the finite strict-sign
neighbourhood that makes the whole prefix stable under the next owner-grid
perturbation. -/
structure OwnerInputSample
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (bit : Bool) (numerical : WindingOneState p ambient)
    (domain : RatBox) where
  outcome : CCLCoupledTrack.StableRepresentedOutcome
    (current.word ++ [bit]) numerical.box domain

/-- Persistent form of Lemma 10.3 for one selected algebraic owner cell.  The
geometric construction must work in every later nested winding box, exactly
matching the strengthened coupled-state invariant. -/
structure PersistentOwnerSamples
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventCount separation) where
  sample : (next : WindingOneState p ambient) →
    next.box.Refines separation.state.box →
      OwnerInputSample current selected.bit next separation.state.box
  sample_priors : ∀ next nextRefines,
    (sample next nextRefines).outcome.priors =
      (sample separation.state
        (RatBox.refines_refl separation.state.box)).outcome.priors
  sample_sameSigns : ∀ next nextRefines form,
    form ∈ (sample separation.state
      (RatBox.refines_refl separation.state.box)).outcome.priors →
      0 < form.eval (sample separation.state
          (RatBox.refines_refl separation.state.box)).outcome.point *
        form.eval (sample next nextRefines).outcome.point

/-- Persistent owner samples indexed by the common global/guarded event
payload.  The sampling invariant depends only on the selected bit; source
provenance remains available in the payload for the geometric construction. -/
structure PersistentEventOwnerSamples
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation) where
  sample : (next : WindingOneState p ambient) →
    next.box.Refines separation.state.box →
      OwnerInputSample current selected.bit next separation.state.box
  sample_priors : ∀ next nextRefines,
    (sample next nextRefines).outcome.priors =
      (sample separation.state
        (RatBox.refines_refl separation.state.box)).outcome.priors
  sample_sameSigns : ∀ next nextRefines form,
    form ∈ (sample separation.state
      (RatBox.refines_refl separation.state.box)).outcome.priors →
      0 < form.eval (sample separation.state
          (RatBox.refines_refl separation.state.box)).outcome.point *
        form.eval (sample next nextRefines).outcome.point

def PersistentOwnerSamples.toEventPayload
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventCount separation}
    (samples : PersistentOwnerSamples current separation selected) :
    PersistentEventOwnerSamples current separation
      selected.toPayload.toIncrementalPayload :=
  { sample := samples.sample
    sample_priors := samples.sample_priors
    sample_sameSigns := samples.sample_sameSigns }

abbrev PersistentGuardOwnerSamples
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedGuardEventCount separation) :=
  PersistentEventOwnerSamples current separation
    selected.toPayload.toIncrementalPayload

/-- Package a stable represented result into the concrete nonterminal coupled
successor required by `Machine.step`. -/
def nextOfStableRepresentedOutcome
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient) (bit : Bool)
    (numerical : WindingOneState p ambient)
    (refines : numerical.box.Refines current.numerical.box)
    (sample : CCLCoupledTrack.StableRepresentedOutcome
      (current.word ++ [bit]) numerical.box numerical.box)
    (sampleInRefinement : (next : WindingOneState p ambient) →
      next.box.Refines numerical.box →
        CCLCoupledTrack.StableRepresentedOutcome
          (current.word ++ [bit]) next.box numerical.box)
    (sampleInRefinement_priors : ∀ next nextRefines,
      (sampleInRefinement next nextRefines).priors = sample.priors)
    (sampleInRefinement_sameSigns : ∀ next nextRefines form,
      form ∈ sample.priors →
        0 < form.eval sample.point *
          form.eval (sampleInRefinement next nextRefines).point) :
    CCLCoupledTrack.StepResult current :=
  .next bit
    { numerical := numerical
      word := current.word ++ [bit]
      sample := sample.point
      sampleInside := sample.inside
      sampleNonzero := sample.nonzero
      sampleRepresented := sample.semantics
      priors := sample.priors
      samplePriorsNonzero := sample.priorsNonzero
      sampleInRefinement := sampleInRefinement
      sampleInRefinement_priors := sampleInRefinement_priors
      sampleInRefinement_sameSigns := sampleInRefinement_sameSigns }
    refines rfl

/-- Close a genuine equality-owned event once its persistent finite owner-grid
sampler is available.  The owner grid itself supplies the represented point
and preserves its strict history branch; the independent height-bounded
search theorem remains the finite executable verification of compatibility. -/
def nextOfPersistentEventPayload
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (samples : PersistentEventOwnerSamples current separation selected) :
    CCLCoupledTrack.StepResult current := by
  let input := samples.sample separation.state
    (RatBox.refines_refl separation.state.box)
  let sampleInRefinement : (next : WindingOneState p ambient) →
      next.box.Refines separation.state.box →
        CCLCoupledTrack.StableRepresentedOutcome
          (current.word ++ [selected.bit]) next.box separation.state.box := by
    intro next nextRefines
    exact (samples.sample next nextRefines).outcome
  exact nextOfStableRepresentedOutcome current selected.bit separation.state
    separation.refines input.outcome sampleInRefinement
    samples.sample_priors samples.sample_sameSigns

def nextOfPersistentEventOwner
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventCount separation)
    (samples : PersistentOwnerSamples current separation selected) :
    CCLCoupledTrack.StepResult current :=
  nextOfPersistentEventPayload current separation
    selected.toPayload.toIncrementalPayload
    samples.toEventPayload

def nextOfPersistentGuardEventOwner
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedGuardEventCount separation)
    (samples : PersistentGuardOwnerSamples current separation selected) :
    CCLCoupledTrack.StepResult current :=
  nextOfPersistentEventPayload current separation
    selected.toPayload.toIncrementalPayload samples

/-- Extend a stable old-prefix sample through a child formula that is true
throughout the separated box.  No new prior form is needed: whenever the old
strict signs are preserved, the old word is represented and the uniform child
formula extends it by the selected bit. -/
def stableAfterUniformFormula
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (output : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (bit : Bool)
    (selected : ∀ {input : QI}, output.state.box.Contains input →
      (inputAdvanceFormula (RawParser.parse current.word) bit).Holds input)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines output.state.box)
    (prior : CCLCoupledTrack.StableRepresentedOutcome
      current.word next.box current.numerical.box) :
    CCLCoupledTrack.StableRepresentedOutcome
      (current.word ++ [bit]) next.box output.state.box where
  point := prior.point
  inside := prior.inside
  nonzero := prior.nonzero
  semantics := CCLBranchSampling.represented_append_of_inputFormula
    current.word prior.point bit
    (separation_denominator_ne output (nextRefines.contains prior.inside))
    prior.semantics (selected (nextRefines.contains prior.inside))
  priors := prior.priors
  priorsNonzero := prior.priorsNonzero
  stable := by
    intro point inside preserved
    have represented := prior.stable (output.refines.contains inside) preserved
    exact CCLBranchSampling.represented_append_of_inputFormula
      current.word point bit
      (separation_denominator_ne output inside)
      represented (selected inside)

/-- Close a denominator-separated strict-cell branch all the way to a machine
step while retaining the old prefix's strict-sign neighbourhood. -/
def nextOfResolvedCell
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (output : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (bit : Bool)
    (selected : ∀ {input : QI}, output.state.box.Contains input →
      (inputAdvanceFormula (RawParser.parse current.word) bit).Holds input) :
    CCLCoupledTrack.StepResult current := by
  let prior := current.sampleInRefinement output.state output.refines
  let sample := stableAfterUniformFormula current output bit selected
    output.state (RatBox.refines_refl output.state.box) prior
  let sampleInRefinement : (next : WindingOneState p ambient) →
      next.box.Refines output.state.box →
        CCLCoupledTrack.StableRepresentedOutcome
          (current.word ++ [bit]) next.box output.state.box := by
    intro next nextRefines
    let nextPrior := current.sampleInRefinement next
      (nextRefines.trans output.refines)
    exact stableAfterUniformFormula current output bit selected next nextRefines
      nextPrior
  exact nextOfStableRepresentedOutcome current bit output.state output.refines
    sample sampleInRefinement (by
      intro next nextRefines
      have samplePriors := current.sampleInRefinement_priors output.state
        output.refines
      have nextPriors := current.sampleInRefinement_priors next
        (nextRefines.trans output.refines)
      simpa only [sample, sampleInRefinement, stableAfterUniformFormula,
        prior] using nextPriors.trans samplePriors.symm) (by
      intro next nextRefines form member
      have samplePriors := current.sampleInRefinement_priors output.state
        output.refines
      have formMember : form ∈ current.priors := by
        rw [← samplePriors]
        simpa only [sample, stableAfterUniformFormula, prior] using member
      have first := current.sampleInRefinement_sameSigns output.state
        output.refines form formMember
      have second := current.sampleInRefinement_sameSigns next
        (nextRefines.trans output.refines) form formMember
      simpa only [sample, sampleInRefinement, stableAfterUniformFormula,
        prior] using CCLCoupledTrack.sameSign_of_common_anchor first second)

/-- A whole-box formula decision closes directly to a persistent machine step:
the coupled-state invariant supplies the old-word witness in the separated
box, so callers need not manufacture or retain an accidental current sample. -/
def nextOfUniformFormula
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (output : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (bit : Bool)
    (selected : ∀ {input : QI}, output.state.box.Contains input →
      (inputAdvanceFormula (RawParser.parse current.word) bit).Holds input) :
    CCLCoupledTrack.StepResult current :=
  nextOfResolvedCell current output bit selected

/-- Run the exact whole-box two-formula evaluator with the represented witness
supplied by coupled-state persistence.  Parser uniqueness removes the
formally possible two-child result. -/
def resolveSeparatedCell
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (output : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)) :
    ResolvedCellOutcome (RawParser.parse current.word) output.state.box := by
  let prior := current.sampleInRefinement output.state output.refines
  have determinantNonzero :
      determinant (RawParser.parse current.word).matrix ≠ 0 := by
    simpa only [determinant, Mat2.det] using
      RawParser.parse_det_ne current.word
  have inverseDenominator :
      (adjugate (RawParser.parse current.word).matrix).c * prior.point +
        (adjugate (RawParser.parse current.word).matrix).d ≠ 0 :=
    separation_denominator_ne output prior.inside
  let witness : CellWitness (RawParser.parse current.word)
      output.state.box :=
    { input := prior.point
      contains := prior.inside
      inverseDenominator := inverseDenominator
      holds := by
        rcases prior.semantics with ⟨tail, represents⟩
        rw [CCLBranchSampling.inverse_tail_eq_of_represents
          (RawParser.parse current.word) prior.point tail determinantNonzero
          inverseDenominator represents]
        exact represents.2.2 }
  exact CCLBranchEvidence.resolveCell (RawParser.parse current.word)
    output.state.box determinantNonzero witness

/-- Once both finite terminal images have been separated from the track,
failure of both child formulas cannot hold throughout any later nested box.
The persistent represented sample supplies a concrete current-state witness
inside that box, while terminal separation excludes exactly such a witness. -/
theorem no_uniform_terminal_after_separation
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (terminal : CCLTerminalSeparation.SeparationOutput p ambient
      (RawParser.parse current.word) separation.state [false, true])
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines terminal.numerical.box)
    (none : ∀ {input : QI}, next.box.Contains input →
      ∀ bit, ¬(inputAdvanceFormula (RawParser.parse current.word) bit).Holds
        input) :
    False := by
  have nextRefinesCurrent : next.box.Refines current.numerical.box :=
    nextRefines.trans (terminal.refines.trans separation.refines)
  let prior := current.sampleInRefinement next nextRefinesCurrent
  have determinantNonzero :
      determinant (RawParser.parse current.word).matrix ≠ 0 := by
    simpa only [determinant, Mat2.det] using
      RawParser.parse_det_ne current.word
  have inverseDenominator :
      (adjugate (RawParser.parse current.word).matrix).c * prior.point +
        (adjugate (RawParser.parse current.word).matrix).d ≠ 0 :=
    separation_denominator_ne separation
      ((nextRefines.trans terminal.refines).contains prior.inside)
  have currentHolds : (RawParser.parse current.word).Holds
      (RatBox.homographic
        (adjugate (RawParser.parse current.word).matrix) prior.point) := by
    rcases prior.semantics with ⟨tail, represents⟩
    rw [CCLBranchSampling.inverse_tail_eq_of_represents
      (RawParser.parse current.word) prior.point tail determinantNonzero
      inverseDenominator represents]
    exact represents.2.2
  have excluded := terminal.excludes_no_children prior.point
    determinantNonzero inverseDenominator currentHolds (none prior.inside)
  exact excluded (nextRefines.contains prior.inside)

/-- Exact whole-box outcome after terminal candidates have already been
removed.  Only interval refinement or a unique strict child can remain. -/
inductive PostTerminalCellOutcome (state : RawParser.State) (box : RatBox) where
  | unresolved
  | next (bit : Bool)
      (selectedStrict : CCLHermitianBox.Formula.strictOnBox
        (inputAdvanceFormula state bit) box = true)
      (otherStrict : CCLHermitianBox.Formula.strictOnBox
        (inputAdvanceFormula state (!bit)) box = true)
      (holds : ∀ {input : QI}, box.Contains input →
        (inputAdvanceFormula state bit).Holds input)
      (otherFails : ∀ {input : QI}, box.Contains input →
        ¬(inputAdvanceFormula state (!bit)).Holds input)

/-- Run the formula evaluator on a refinement of a terminal-separated state
and remove its now-impossible terminal constructor constructively. -/
def resolvePostTerminalCell
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (terminal : CCLTerminalSeparation.SeparationOutput p ambient
      (RawParser.parse current.word) separation.state [false, true])
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines terminal.numerical.box) :
    PostTerminalCellOutcome (RawParser.parse current.word) next.box := by
  let restricted := separation.restrict next
    (nextRefines.trans terminal.refines)
  match resolveSeparatedCell current restricted with
  | .unresolved => exact .unresolved
  | .terminal _falseStrict _trueStrict noChild =>
      exact (no_uniform_terminal_after_separation current separation terminal
        next nextRefines noChild).elim
  | .next bit selectedStrict otherStrict holds otherFails =>
      exact .next bit selectedStrict otherStrict holds otherFails

/-- Executable strict-side closure.  `none` precisely records that direct box
arithmetic is still unresolved or that both child formulas are false; the
positive result is already a persistent concrete `StepResult`. -/
def nextOfSeparatedCell?
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (output : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)) :
    Option (CCLCoupledTrack.StepResult current) :=
  match resolveSeparatedCell current output with
  | .unresolved | .terminal _ _ _ => none
  | .next bit _selectedStrict _otherStrict selected _otherFails =>
      some (nextOfUniformFormula current output bit selected)

/-- Discharge the strict-side case in either pending geometric opening.  The
all-clear branch evaluates on its actual two-stage refinement, carrying the
existing decoder-denominator margin into that nested box.  All geometric
evidence is retained unchanged when direct box arithmetic still cannot
resolve a child. -/
def Opening.resolveStrictCell
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient} :
    Opening p ambient current → Opening p ambient current
  | .ready result => .ready result
  | .eventOwner separation selected =>
      match nextOfSeparatedCell? current separation with
      | some result => .ready result
      | none => .eventOwner separation selected
  | .guardEventOwner separation selected =>
      match nextOfSeparatedCell? current separation with
      | some result => .ready result
      | none => .guardEventOwner separation selected
  | .noEventOwner separation allNeither guardNone noIdenticallyZero arcs
      evidence alignment guardCurve terminal output =>
      let refinedSeparation := separation.restrict output.state
        (output.refines.trans terminal.refines)
      match resolvePostTerminalCell current separation terminal output.state
          output.refines with
      | .next bit _selectedStrict _otherStrict selected _otherFails =>
          .ready (nextOfUniformFormula current refinedSeparation bit selected)
      | .unresolved =>
          .noEventOwner separation allNeither guardNone noIdenticallyZero arcs
            evidence alignment guardCurve terminal output
  | .guardClear separation allNeither guardNone noIdenticallyZero arcs
      evidence alignment terminal output guardEvidence guardOutput =>
      let refinedSeparation := separation.restrict guardOutput.state
        (guardOutput.refines.trans
          (output.refines.trans terminal.refines))
      match resolvePostTerminalCell current separation terminal
          guardOutput.state (guardOutput.refines.trans output.refines) with
      | .next bit _selectedStrict _otherStrict selected _otherFails =>
          .ready (nextOfUniformFormula current refinedSeparation bit selected)
      | .unresolved =>
          .guardClear separation allNeither guardNone noIdenticallyZero arcs
            evidence alignment terminal output guardEvidence guardOutput

/-- Complete opening analysis followed by the executable strict-cell closure.
The only remaining non-ready constructors are genuine boundary cases. -/
def openStrictStep
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient)
    (current : CCLCoupledTrack.State p ambient)
    (clearOwnerLabel : Bool) : Opening p ambient current :=
  (openStep track current clearOwnerLabel).resolveStrictCell

/-- Execute the finite guard-cell trichotomy in a pending all-clear opening.
An all-clear guarded family receives its own quantitative refinement and is
then re-evaluated immediately.  Positive and identically-zero guard cells are
retained explicitly for the remaining relevance analysis. -/
def Opening.resolveGuardClearance
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    (track : WindingOneTrack p ambient) :
    Opening p ambient current → Opening p ambient current
  | .ready result => .ready result
  | .eventOwner separation selected => .eventOwner separation selected
  | .guardEventOwner separation selected =>
      .guardEventOwner separation selected
  | .guardClear separation allNeither guardNone noIdenticallyZero arcs
      evidence alignment terminal output guardEvidence guardOutput =>
      (Opening.guardClear separation allNeither guardNone noIdenticallyZero arcs
        evidence alignment terminal output guardEvidence guardOutput).resolveStrictCell
  | .noEventOwner separation allNeither guardNone noIdenticallyZero arcs
      evidence alignment guardCurve terminal output =>
      match guardCurve with
      | .allClear guardEvidence =>
          let guardOutput := refineForGuardClearance track output.state
            guardEvidence
          (Opening.guardClear separation allNeither guardNone noIdenticallyZero arcs
            evidence alignment terminal output guardEvidence
              guardOutput).resolveStrictCell
      | .identicallyZero sourceCell member realZero imagZero _relevance =>
          by
            let exactRoot := exactRootOfSeparatedIdenticallyZeroGuardCell
              separation (by
                simpa only [determinant, Mat2.det] using
                  RawParser.parse_det_ne current.word)
                sourceCell member realZero imagZero
            by_cases zero : exactRoot.point = 0
            · exact .ready (.zero (by
                simpa only [zero] using exactRoot.root))
            · exact .ready (.terminal exactRoot.point exactRoot.root zero
                (RationalEncoder.encode exactRoot.point zero) rfl)
      | .positive sourceCell member clearedNonzero countPositive event
          eventMember =>
          .noEventOwner separation allNeither guardNone noIdenticallyZero arcs
            evidence alignment
              (.positive sourceCell member clearedNonzero countPositive
                event eventMember)
                terminal output

/-- Opening analysis with both ordinary and terminal-guard zero-count
refinements executed whenever their finite decisions permit it. -/
def openGuardStep
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient)
    (current : CCLCoupledTrack.State p ambient)
    (clearOwnerLabel : Bool) : Opening p ambient current :=
  (openStrictStep track current clearOwnerLabel).resolveGuardClearance track

end CCLCoupledController
end FTA
