import FTA.CCLActiveMetricTrack

/-!
# History-free geometry of a positive active boundary event

The residual active-controller branch contains a positive source-labelled
guard event but no incremental owner.  This module extracts its fixed
count-one path cell and a derivative-oriented family of rational
approximations.  None of these constructions requires whole-box prefix
wrapping or a historical parser formula.
-/

namespace FTA
namespace CCLActiveMetricTrack

open CCL CCL.GaussianRat
open FTA.AxisSafeCuts
open FTA.CCLActiveBoxCoupling
open FTA.CCLActiveEventGrid
open FTA.CCLActiveMetricTrack
open FTA.CCLBoundaryPreservingOwner
open FTA.CCLBoxCylinderIncrementalEventGrid
open FTA.CCLBranchController
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLBranchEvidence
open FTA.CCLBranchPartition
open FTA.CCLBranchPlan
open FTA.CCLCanonicalEvent
open FTA.CCLCountOneClassification
open FTA.CCLCoupledTrack
open FTA.CCLEventExtraction
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLIntersectionEventSigns
open FTA.CCLPathIntersection
open FTA.CCLNextBitFormula
open FTA.CCLParserGeometry
open FTA.CCLPositiveEventConvergence
open FTA.CCLPositiveEventApproximation
open FTA.CCLPositiveEventLocalization
open FTA.CCLPositiveEventSemantics
open FTA.CCLPositiveEventTrack
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.DenseDerivative
open FTA.LocalExtraction
open FTA.PathPolynomial
open FTA.ProjectivePath
open FTA.RationalPolynomialBounds
open FTA.RootCountDivisibility
open FTA.RootTrackSeparation
open FTA.CCLStrictChildSemantics

theorem ActivePositiveGuardData.source_partition_mem_separated
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current) :
    data.sourceCell.partition ∈ separatedChartPartitions p
      (RawParser.parse current.core.word) data.separation := by
  apply sourceEventGuardCell_partition_mem_of_mem
  simpa only [separatedEventGuardCells] using data.member

theorem ActivePositiveGuardData.source_entry_mem_separated
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current) :
    data.sourceCell.partition.entry ∈
      separatedCharts (RawParser.parse current.core.word) data.separation := by
  apply SourceChartPartition.entry_mem_of_mem_build
  simpa only [separatedChartPartitions] using
    data.source_partition_mem_separated

theorem ActivePositiveGuardData.source_mem_inputPlan
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current) :
    data.sourceCell.partition.entry.source ∈
      inputPlan (RawParser.parse current.core.word) :=
  separatedChart_source_mem_inputPlan data.source_entry_mem_separated

theorem ActivePositiveGuardData.source_determinant_ne
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (stateDeterminant :
      determinant (RawParser.parse current.core.word).matrix ≠ 0) :
    determinant data.sourceCell.partition.entry.source.matrix ≠ 0 :=
  separatedChart_determinant_ne stateDeterminant
    data.source_entry_mem_separated

/-- On every unary parser phase, a newly planned comparison boundary lies
inside the current active radial region.  Sector phases are excluded because
their current angular cone needs the separate finite owner-cone argument. -/
private theorem localPlan_boundary_active_of_nonsector
    (phase : RawParser.Phase) (source : BoundarySource)
    (member : source ∈ localPlan phase) (value : QI)
    (boundary : source.form.eval value = 0)
    (nonsector : ¬∃ kind exponent bits,
      phase = .sector kind exponent bits) :
    RawParser.activeHolds phase value := by
  cases phase with
  | initial => trivial
  | highUnary count =>
      have formMember : source.form ∈ localForms (.highUnary count) :=
        List.mem_map.mpr ⟨source, member, rfl⟩
      have formEquality : source.form =
          affineNormComparisonForm ((2 : ℚ) ^ (count + 1)) := by
        simpa using formMember
      have equality : normSq value = (2 : ℚ) ^ (count + 1) := by
        rw [formEquality, CCLParserGeometry.eval_affineNormComparisonForm]
          at boundary
        linarith
      rw [RawParser.activeHolds, equality, pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℚ) < 2) count]
  | lowUnary count =>
      cases count with
      | zero =>
          have formMember : source.form ∈ localForms (.lowUnary 0) :=
            List.mem_map.mpr ⟨source, member, rfl⟩
          have formEquality : source.form = affineNormComparisonForm 1 := by
            simpa using formMember
          have equality : normSq value = 1 := by
            rw [formEquality,
              CCLParserGeometry.eval_affineNormComparisonForm] at boundary
            linarith
          norm_num [RawParser.activeHolds, equality]
      | succ count =>
          have formMember : source.form ∈
              localForms (.lowUnary (count + 1)) :=
            List.mem_map.mpr ⟨source, member, rfl⟩
          have formEquality : source.form = affineNormComparisonForm
              (1 / (2 : ℚ) ^ (count + 1)) := by
            simpa using formMember
          have equality : normSq value = 1 / (2 : ℚ) ^ (count + 1) := by
            rw [formEquality,
              CCLParserGeometry.eval_affineNormComparisonForm] at boundary
            linarith
          rw [RawParser.activeHolds, equality, pow_succ]
          have powerPositive : (0 : ℚ) < 2 ^ count :=
            pow_pos (by norm_num) count
          field_simp
          nlinarith
  | loopUnary count =>
      have formMember : source.form ∈ localForms (.loopUnary count) :=
        List.mem_map.mpr ⟨source, member, rfl⟩
      have formEquality : source.form =
          affineNormComparisonForm ((2 : ℚ) ^ (count + 1)) := by
        simpa using formMember
      have equality : normSq value = (2 : ℚ) ^ (count + 1) := by
        rw [formEquality, CCLParserGeometry.eval_affineNormComparisonForm]
          at boundary
        linarith
      rw [RawParser.activeHolds, equality, pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℚ) < 2) count]
  | sector kind exponent bits =>
      exact (nonsector ⟨kind, exponent, bits, rfl⟩).elim

/-- A bit read outside an angular sector cannot jump directly to the
two-bit sector phase in which the next call waits for the third bit. -/
private theorem rawParser_step_not_completed_of_nonsector
    (state : RawParser.State) (bit : Bool)
    (nonsector : ¬∃ kind exponent bits,
      state.phase = .sector kind exponent bits) :
    ¬∃ kind exponent first second,
      (RawParser.step state bit).phase =
        .sector kind exponent (.two first second) := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial => cases bit <;> simp [RawParser.step]
  | highUnary count => cases bit <;> simp [RawParser.step]
  | lowUnary count => cases bit <;> simp [RawParser.step]
  | loopUnary count => cases bit <;> simp [RawParser.step]
  | sector kind exponent bits =>
      exact (nonsector ⟨kind, exponent, bits, rfl⟩).elim

/-- Repackage the retained positive guard as its exact source-labelled
algebraic event. -/
def ActivePositiveGuardData.sourceEvent
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current) :
    SourceGuardCurveEvent p data.separation.state.box :=
  ⟨data.sourceCell, data.event, data.eventMember⟩

/-- Select the first finite parser-cell refinement of the retained event.
This is an executable head of a proved-nonempty list, not a choice axiom. -/
def ActivePositiveGuardData.boundaryCandidate
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current) :
    SourceGuardInputEventCell p data.separation.state.box
      (RawParser.parse current.core.word) :=
  (sourceGuardInputEventCells (RawParser.parse current.core.word)
    data.sourceEvent).head
  (sourceGuardInputEventCells_ne_nil
    (RawParser.parse current.core.word) data.sourceEvent)

theorem ActivePositiveGuardData.boundaryCandidate_sourceEvent
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current) :
    data.boundaryCandidate.sourceEvent = data.sourceEvent := by
  have member : data.boundaryCandidate ∈ sourceGuardInputEventCells
      (RawParser.parse current.core.word) data.sourceEvent :=
    List.head_mem (sourceGuardInputEventCells_ne_nil
      (RawParser.parse current.core.word) data.sourceEvent)
  rw [sourceGuardInputEventCells, List.mem_map] at member
  rcases member with ⟨cell, _cellMember, equality⟩
  exact (congrArg (fun candidate => candidate.sourceEvent) equality).symm

/-- Add the squarefree event derivative as a coprime sign condition so every
later approximation approaches the isolated parameter from the same side. -/
def ActivePositiveGuardData.boundaryDerivativeCondition
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current) :
    CoprimeCondition
      data.boundaryCandidate.inputCell.branch.factor.polynomial where
  polynomial := derivative
    data.boundaryCandidate.inputCell.branch.factor.polynomial
  coprime := data.boundaryCandidate.inputCell.branch.factor.input.squarefree

def ActivePositiveGuardData.boundaryDerivativeSigns
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current) :
    CommonEventSigns
      data.boundaryCandidate.inputCell.branch.factor.input
      [data.boundaryDerivativeCondition]
      data.boundaryCandidate.inputCell.parent :=
  computeCommonEventSigns
    data.boundaryCandidate.inputCell.branch.factor.input
    [data.boundaryDerivativeCondition]
    data.boundaryCandidate.inputCell.parent

/-- The derivative-oriented event cell retains the original parser condition
relations and event divisibility. -/
def ActivePositiveGuardData.boundaryOrientedInputCell
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current) :
    InputEventCell (RawParser.parse current.core.word)
      data.boundaryCandidate.sourceEvent.event where
  branch := data.boundaryCandidate.inputCell.branch
  divides := data.boundaryCandidate.inputCell.divides
  parent := data.boundaryDerivativeSigns.refined
  refines := FTA.SturmTransducer.RationalInterval.refines_trans
    data.boundaryDerivativeSigns.refines
      data.boundaryCandidate.inputCell.refines

def ActivePositiveGuardData.boundaryDerivativeSign
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current) :
    IntervalSignCertificate
      (derivative data.boundaryOrientedInputCell.branch.factor.polynomial)
      data.boundaryOrientedInputCell.parent.interval.lower
      data.boundaryOrientedInputCell.parent.interval.upper :=
  data.boundaryDerivativeSigns.signs data.boundaryDerivativeCondition (by simp)

/-- Fixed rational projective path interval underlying the residual boundary
mode. -/
def ActivePositiveGuardData.boundaryPathCylinder
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current) : RationalPathCylinder where
  path :=
    data.boundaryCandidate.sourceEvent.sourceCell.partition.entry.chart.path
  interval := (data.boundaryOrientedInputCell.branch.computeEventSigns
    data.boundaryOrientedInputCell.parent).refined.interval
  denominator_ne := by
    intro parameter lower upper
    exact data.boundaryOrientedInputCell.path_denominator_ne_on_cell lower upper

theorem ActivePositiveGuardData.boundaryPathCylinder_path
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current) :
    data.boundaryPathCylinder.path =
      data.sourceCell.partition.entry.chart.path := by
  change
    data.boundaryCandidate.sourceEvent.sourceCell.partition.entry.chart.path =
      data.sourceCell.partition.entry.chart.path
  rw [data.boundaryCandidate_sourceEvent]
  rfl

/-- Proof-bearing lower-side approximation with a residual cap that keeps
the rational source point distinct from zero. -/
def activeBoundaryApproximation
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    NarrowEventApproximation
      data.boundaryOrientedInputCell.branch.factor.input
      (data.boundaryOrientedInputCell.branch.computeEventSigns
        data.boundaryOrientedInputCell.parent).refined
      (eventSourceApproximationWidth data.boundaryOrientedInputCell squarefree
        (localizedClearance data.separation
          (cappedClearanceState next (checkpointBoundaryCap p)
            (checkpointBoundaryCap_pos p zeroNonzero)))) :=
  data.boundaryOrientedInputCell.clearedApproximation
    (eventSourceApproximationWidth data.boundaryOrientedInputCell squarefree
      (localizedClearance data.separation
        (cappedClearanceState next (checkpointBoundaryCap p)
          (checkpointBoundaryCap_pos p zeroNonzero))))
    (eventSourceApproximationWidth_pos data.boundaryOrientedInputCell
      squarefree (localizedClearance data.separation
        (cappedClearanceState next (checkpointBoundaryCap p)
          (checkpointBoundaryCap_pos p zeroNonzero))))

def activeBoundaryParameter
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR)) : ℚ :=
  (activeBoundaryApproximation data squarefree zeroNonzero next).refined.interval.lower

/-- Canonical rational point on the retained path in an arbitrary later
winding-one box. -/
def activeBoundaryPoint
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR)) : QI :=
  localizedCellPoint data.separation data.boundaryOrientedInputCell squarefree
    (cappedClearanceState next (checkpointBoundaryCap p)
      (checkpointBoundaryCap_pos p zeroNonzero))

theorem activeBoundaryPoint_eq_pathValue
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    activeBoundaryPoint data squarefree zeroNonzero next =
      data.boundaryPathCylinder.path.value
        (activeBoundaryParameter data squarefree zeroNonzero next) := rfl

theorem activeBoundaryParameter_derivative_mul_neg
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    data.boundaryOrientedInputCell.branch.factor.polynomial.eval
          (activeBoundaryParameter data squarefree zeroNonzero next) *
        (derivative
          data.boundaryOrientedInputCell.branch.factor.polynomial).eval
          (activeBoundaryParameter data squarefree zeroNonzero next) < 0 := by
  exact narrowEventApproximation_lower_derivative_mul_neg
    data.boundaryOrientedInputCell.branch.factor.input
    (data.boundaryOrientedInputCell.branch.computeEventSigns
      data.boundaryOrientedInputCell.parent).refined
    (eventSourceApproximationWidth data.boundaryOrientedInputCell squarefree
      (localizedClearance data.separation
        (cappedClearanceState next (checkpointBoundaryCap p)
          (checkpointBoundaryCap_pos p zeroNonzero))))
    (eventSourceApproximationWidth_pos data.boundaryOrientedInputCell
      squarefree (localizedClearance data.separation
        (cappedClearanceState next (checkpointBoundaryCap p)
          (checkpointBoundaryCap_pos p zeroNonzero))))

/-- All independently localized parameters approach the event from the same
derivative-oriented side. -/
theorem activeBoundaryEventFactor_mul_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    0 < data.boundaryOrientedInputCell.branch.factor.polynomial.eval
          (activeBoundaryParameter data squarefree zeroNonzero
            data.output.state) *
        data.boundaryOrientedInputCell.branch.factor.polynomial.eval
          (activeBoundaryParameter data squarefree zeroNonzero next) := by
  let cell := data.boundaryOrientedInputCell
  let signs := cell.branch.computeEventSigns cell.parent
  let baseApproximation := activeBoundaryApproximation data squarefree
    zeroNonzero data.output.state
  let nextApproximation := activeBoundaryApproximation data squarefree
    zeroNonzero next
  have baseLower : cell.parent.interval.lower ≤
      activeBoundaryParameter data squarefree zeroNonzero data.output.state :=
    signs.refines.1.trans baseApproximation.refines.1
  have baseUpper : activeBoundaryParameter data squarefree zeroNonzero
      data.output.state ≤ cell.parent.interval.upper :=
    baseApproximation.refined.proper.le.trans
      (baseApproximation.refines.2.trans signs.refines.2)
  have nextLower : cell.parent.interval.lower ≤
      activeBoundaryParameter data squarefree zeroNonzero next :=
    signs.refines.1.trans nextApproximation.refines.1
  have nextUpper : activeBoundaryParameter data squarefree zeroNonzero next ≤
      cell.parent.interval.upper :=
    nextApproximation.refined.proper.le.trans
      (nextApproximation.refines.2.trans signs.refines.2)
  have derivativeAligned := data.boundaryDerivativeSign.eval_mul_pos_between
    baseLower baseUpper nextLower nextUpper
  exact mul_pos_of_mul_neg_of_orienters_mul_pos
    (activeBoundaryParameter_derivative_mul_neg data squarefree zeroNonzero
      data.output.state)
    (activeBoundaryParameter_derivative_mul_neg data squarefree zeroNonzero
      next)
    derivativeAligned

/-- A canonically nonzero current decision form keeps its cleared sign at all
oriented boundary approximations. -/
theorem activeBoundaryClearedForm_mul_pos_of_canonicalNonzero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (form : HermitianForm)
    (member : form ∈ inputDecisionForms (RawParser.parse current.core.word))
    (canonicalNonzero :
      inputEventCanonicalValue data.boundaryOrientedInputCell form ≠ 0) :
    0 < (clearedForm form data.boundaryPathCylinder.path).eval
          (activeBoundaryParameter data squarefree zeroNonzero
            data.output.state) *
        (clearedForm form data.boundaryPathCylinder.path).eval
          (activeBoundaryParameter data squarefree zeroNonzero next) := by
  let cell := data.boundaryOrientedInputCell
  let signs := cell.branch.computeEventSigns cell.parent
  let baseApproximation := activeBoundaryApproximation data squarefree
    zeroNonzero data.output.state
  let nextApproximation := activeBoundaryApproximation data squarefree
    zeroNonzero next
  have polynomialMember :
      clearedForm form data.boundaryPathCylinder.path ∈
        inputEventPolynomials (RawParser.parse current.core.word)
          data.boundaryPathCylinder.path :=
    clearedForm_mem_inputEventPolynomials_of_inputDecisionForm
      (RawParser.parse current.core.word) data.boundaryPathCylinder.path form
        member
  have baseSign :=
    ConditionRelations.canonicalEventValue_mul_eval_pos
      cell.branch.relations cell.parent signs polynomialMember (by
        simpa only [inputEventCanonicalValue,
          ActivePositiveGuardData.boundaryPathCylinder, cell, signs] using
          canonicalNonzero)
      baseApproximation.refines.1
      (baseApproximation.refined.proper.le.trans
        baseApproximation.refines.2)
  have nextSign :=
    ConditionRelations.canonicalEventValue_mul_eval_pos
      cell.branch.relations cell.parent signs polynomialMember (by
        simpa only [inputEventCanonicalValue,
          ActivePositiveGuardData.boundaryPathCylinder, cell, signs] using
          canonicalNonzero)
      nextApproximation.refines.1
      (nextApproximation.refined.proper.le.trans
        nextApproximation.refines.2)
  exact CCLCoupledTrack.sameSign_of_common_anchor baseSign nextSign

private theorem activeBoundary_mul_pos_of_positive_scales
    {leftScale rightScale left right : ℚ}
    (scaled : 0 < (leftScale * left) * (rightScale * right))
    (leftScalePositive : 0 < leftScale)
    (rightScalePositive : 0 < rightScale) :
    0 < left * right := by
  have scalesPositive : 0 < leftScale * rightScale :=
    mul_pos leftScalePositive rightScalePositive
  have rearranged : 0 < (leftScale * rightScale) * (left * right) := by
    calc
      0 < (leftScale * left) * (rightScale * right) := scaled
      _ = (leftScale * rightScale) * (left * right) := by ring
  exact (mul_pos_iff_of_pos_left scalesPositive).mp rearranged

theorem activeBoundaryForm_mul_pos_of_clearedForm_mul_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (form : HermitianForm)
    (clearedSign :
      0 < (clearedForm form data.boundaryPathCylinder.path).eval
            (activeBoundaryParameter data squarefree zeroNonzero
              data.output.state) *
          (clearedForm form data.boundaryPathCylinder.path).eval
            (activeBoundaryParameter data squarefree zeroNonzero next)) :
    0 < form.eval (activeBoundaryPoint data squarefree zeroNonzero
          data.output.state) *
        form.eval (activeBoundaryPoint data squarefree zeroNonzero next) := by
  let baseApproximation := activeBoundaryApproximation data squarefree
    zeroNonzero data.output.state
  let nextApproximation := activeBoundaryApproximation data squarefree
    zeroNonzero next
  have baseDenominator :=
    data.boundaryOrientedInputCell.path_denominator_ne_on_cell
      baseApproximation.refines.1
      (baseApproximation.refined.proper.le.trans
        baseApproximation.refines.2)
  have nextDenominator :=
    data.boundaryOrientedInputCell.path_denominator_ne_on_cell
      nextApproximation.refines.1
      (nextApproximation.refined.proper.le.trans
        nextApproximation.refines.2)
  rw [eval_clearedForm form data.boundaryPathCylinder.path
        (activeBoundaryParameter data squarefree zeroNonzero
          data.output.state) baseDenominator,
      eval_clearedForm form data.boundaryPathCylinder.path
        (activeBoundaryParameter data squarefree zeroNonzero next)
        nextDenominator] at clearedSign
  have baseScalePositive : 0 <
      (denominatorNorm data.boundaryPathCylinder.path).eval
        (activeBoundaryParameter data squarefree zeroNonzero
          data.output.state) :=
    eval_denominatorNorm_pos data.boundaryPathCylinder.path _ baseDenominator
  have nextScalePositive : 0 <
      (denominatorNorm data.boundaryPathCylinder.path).eval
        (activeBoundaryParameter data squarefree zeroNonzero next) :=
    eval_denominatorNorm_pos data.boundaryPathCylinder.path _ nextDenominator
  rw [activeBoundaryPoint_eq_pathValue, activeBoundaryPoint_eq_pathValue]
  exact activeBoundary_mul_pos_of_positive_scales clearedSign
    baseScalePositive nextScalePositive

theorem activeBoundaryForm_mul_pos_of_canonicalNonzero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (form : HermitianForm)
    (member : form ∈ inputDecisionForms (RawParser.parse current.core.word))
    (canonicalNonzero :
      inputEventCanonicalValue data.boundaryOrientedInputCell form ≠ 0) :
    0 < form.eval (activeBoundaryPoint data squarefree zeroNonzero
          data.output.state) *
        form.eval (activeBoundaryPoint data squarefree zeroNonzero next) := by
  apply activeBoundaryForm_mul_pos_of_clearedForm_mul_pos data squarefree
    zeroNonzero next form
  exact activeBoundaryClearedForm_mul_pos_of_canonicalNonzero data squarefree
    zeroNonzero next form member canonicalNonzero

theorem activeBoundaryEventFactor_dvd_of_canonicalZero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (form : HermitianForm)
    (member : form ∈ inputDecisionForms (RawParser.parse current.core.word))
    (canonicalZero :
      inputEventCanonicalValue data.boundaryOrientedInputCell form = 0) :
    data.boundaryOrientedInputCell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm form data.boundaryPathCylinder.path).toPolynomial := by
  let cell := data.boundaryOrientedInputCell
  let signs := cell.branch.computeEventSigns cell.parent
  have polynomialMember :
      clearedForm form data.boundaryPathCylinder.path ∈
        inputEventPolynomials (RawParser.parse current.core.word)
          data.boundaryPathCylinder.path :=
    clearedForm_mem_inputEventPolynomials_of_inputDecisionForm
      (RawParser.parse current.core.word) data.boundaryPathCylinder.path form
        member
  apply ConditionRelations.dvd_of_canonicalEventValue_eq_zero
    cell.branch.relations cell.parent signs polynomialMember
  simpa only [inputEventCanonicalValue,
    ActivePositiveGuardData.boundaryPathCylinder, cell, signs] using
      canonicalZero

theorem ActivePositiveGuardData.output_refines_separation
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current) :
    data.output.state.box.Refines data.separation.state.box :=
  data.output.refines.trans data.terminal.refines

/-- Every active boundary sample lies on the one rational path cylinder
selected by the positive curve-count event. -/
theorem activeBoundaryPoint_supported
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    data.boundaryPathCylinder.Contains
      (activeBoundaryPoint data squarefree zeroNonzero next) := by
  let cap := checkpointBoundaryCap p
  let capPositive := checkpointBoundaryCap_pos p zeroNonzero
  let capped := cappedClearanceState next cap capPositive
  let cell := data.boundaryOrientedInputCell
  let clearance := localizedClearance data.separation capped
  let approximation := cell.clearedApproximation
    (eventSourceApproximationWidth cell squarefree clearance)
    (eventSourceApproximationWidth_pos cell squarefree clearance)
  let parameter := approximation.refined.interval.lower
  refine ⟨parameter, approximation.refines.1,
    approximation.refined.proper.le.trans approximation.refines.2, ?_⟩
  rfl

theorem activeBoundaryPoint_strictContains
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines data.separation.state.box) :
    next.box.StrictContains
      (activeBoundaryPoint data squarefree zeroNonzero next) := by
  let cap := checkpointBoundaryCap p
  let capPositive := checkpointBoundaryCap_pos p zeroNonzero
  let capped := cappedClearanceState next cap capPositive
  have cappedRefines : capped.box.Refines data.separation.state.box := by
    simpa only [capped, cappedClearanceState_box] using nextRefines
  simpa only [activeBoundaryPoint, cap, capPositive, capped,
    cappedClearanceState_box] using
      localizedCellPoint_strictContains data.separation
        data.boundaryOrientedInputCell squarefree degreeNonzero elimination
        capped cappedRefines

theorem activeBoundaryPoint_ne_zero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    activeBoundaryPoint data squarefree zeroNonzero next ≠ 0 := by
  let cap := checkpointBoundaryCap p
  let capPositive := checkpointBoundaryCap_pos p zeroNonzero
  let capped := cappedClearanceState next cap capPositive
  have residual := localizedCellPoint_residual_lt data.separation
    data.boundaryOrientedInputCell squarefree capped
  have clearanceLe : capped.clearance.bound / 8 ≤ cap / 8 := by
    gcongr
    simpa only [capped] using
      cappedClearanceState_clearance_le next cap capPositive
  have capDivLe : cap / 8 ≤ normSq (p.eval 0) := by
    apply (div_le_self capPositive.le (by norm_num : (1 : ℚ) ≤ 8)).trans
    exact checkpointBoundaryCap_le_zeroResidual p
  intro zero
  have pointZero : localizedCellPoint data.separation
      data.boundaryOrientedInputCell squarefree capped = 0 := by
    simpa only [activeBoundaryPoint, cap, capPositive, capped] using zero
  rw [pointZero] at residual
  exact (not_lt_of_ge (clearanceLe.trans capDivLe)) residual

/-- Geometric core of active exact-boundary stability.  Every phase-local
input form keeps one strict sign between the base boundary sample and any
later sample, or is exact equality at both. -/
def ActiveBoundaryDecisionFormsStable
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0) : Prop :=
  ∀ (next : WindingOneState p (RatBox.symmetric R hR))
    (_nextRefines : next.box.Refines data.output.state.box)
    (form : HermitianForm)
    (_member : form ∈ inputDecisionForms (RawParser.parse current.core.word)),
    SameSignOrBothZero
      (form.eval (activeBoundaryPoint data squarefree zeroNonzero
        data.output.state))
      (form.eval (activeBoundaryPoint data squarefree zeroNonzero next))

/-- The nonzero path restrictions in active exact-boundary stability retain a
strict side between lower event approximations. -/
def ActiveBoundaryDecisionCrossingFormsStable
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0) : Prop :=
  ∀ (next : WindingOneState p (RatBox.symmetric R hR))
    (_nextRefines : next.box.Refines data.output.state.box)
    (form : HermitianForm)
    (_member : form ∈ inputDecisionForms (RawParser.parse current.core.word)),
    (clearedForm form data.boundaryPathCylinder.path).isZero = false →
      0 < form.eval (activeBoundaryPoint data squarefree zeroNonzero
          data.output.state) *
        form.eval (activeBoundaryPoint data squarefree zeroNonzero next)

/-- The shared-factor subcase for a nonzero active decision form: an exact
multiple of the selected event factor keeps its oriented one-sided sign. -/
def ActiveBoundarySharedDecisionFormsStable
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0) : Prop :=
  ∀ (next : WindingOneState p (RatBox.symmetric R hR))
    (_nextRefines : next.box.Refines data.output.state.box)
    (form : HermitianForm)
    (_member : form ∈ inputDecisionForms (RawParser.parse current.core.word)),
    (clearedForm form data.boundaryPathCylinder.path).isZero = false →
    inputEventCanonicalValue data.boundaryOrientedInputCell form = 0 →
      0 < form.eval (activeBoundaryPoint data squarefree zeroNonzero
          data.output.state) *
        form.eval (activeBoundaryPoint data squarefree zeroNonzero next)

/-- Affineness of current decision forms turns exact event-factor
divisibility into the required shared-factor sign stability. -/
theorem activeBoundarySharedDecisionFormsStable
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0) :
    ActiveBoundarySharedDecisionFormsStable data squarefree zeroNonzero := by
  intro next _nextRefines form member nonzero canonicalZero
  have stateDeterminant :
      determinant (RawParser.parse current.core.word).matrix ≠ 0 := by
    simpa only [determinant, Mat2.det] using
      RawParser.parse_det_ne current.core.word
  have sourceNondegenerate :
      data.sourceCell.partition.entry.source.ParametrizationNondegenerate :=
    inputPlan_parametrizationNondegenerate
      (RawParser.parse current.core.word) data.source_mem_inputPlan
  have degree :
      (clearedForm form data.boundaryPathCylinder.path).natDegree ≤ 1 := by
    rw [data.boundaryPathCylinder_path] at nonzero ⊢
    exact inputDecisionForm_clearedForm_natDegree_le_one
      (RawParser.parse current.core.word) data.source_mem_inputPlan
      data.sourceCell.partition.entry.chart
      (data.source_determinant_ne stateDeterminant) sourceNondegenerate form
      member nonzero
  have clearedSign := evals_mul_pos_of_dvd_natDegree_le_one
    data.boundaryOrientedInputCell.branch.factor.input nonzero degree
    (activeBoundaryEventFactor_dvd_of_canonicalZero data form member
      canonicalZero)
    (activeBoundaryEventFactor_mul_pos data squarefree zeroNonzero next)
  exact activeBoundaryForm_mul_pos_of_clearedForm_mul_pos data squarefree
    zeroNonzero next form clearedSign

/-- Canonically nonzero forms use their classified sign; canonically zero
forms use the shared event-factor argument. -/
theorem activeBoundaryDecisionCrossingFormsStable_of_shared
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (shared : ActiveBoundarySharedDecisionFormsStable data squarefree
      zeroNonzero) :
    ActiveBoundaryDecisionCrossingFormsStable data squarefree
      zeroNonzero := by
  intro next nextRefines form member nonzero
  by_cases canonicalZero :
      inputEventCanonicalValue data.boundaryOrientedInputCell form = 0
  · exact shared next nextRefines form member nonzero canonicalZero
  · exact activeBoundaryForm_mul_pos_of_canonicalNonzero data squarefree
      zeroNonzero next form member canonicalZero

/-- Exact path equalities remain zero; all other current decision forms use
the strict crossing-form argument. -/
theorem activeBoundaryDecisionFormsStable_of_crossingForms
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (crossing : ActiveBoundaryDecisionCrossingFormsStable data squarefree
      zeroNonzero) :
    ActiveBoundaryDecisionFormsStable data squarefree zeroNonzero := by
  intro next nextRefines form member
  cases zero : (clearedForm form data.boundaryPathCylinder.path).isZero with
  | false =>
      exact Or.inl (crossing next nextRefines form member zero)
  | true =>
      right
      rcases activeBoundaryPoint_supported data squarefree zeroNonzero
          data.output.state with ⟨baseParameter, baseLower, baseUpper, baseEq⟩
      rcases activeBoundaryPoint_supported data squarefree zeroNonzero next with
        ⟨nextParameter, nextLower, nextUpper, nextEq⟩
      have equalityMember : form ∈ pathEqualityForms
          (inputDecisionForms (RawParser.parse current.core.word))
          data.boundaryPathCylinder.path := by
        exact (mem_pathEqualityForms_iff _ _ _).2 ⟨member, zero⟩
      constructor
      · rw [baseEq]
        exact eval_eq_zero_of_mem_pathEqualityForms _ _ equalityMember
          baseParameter
          (data.boundaryPathCylinder.denominator_ne baseLower baseUpper)
      · rw [nextEq]
        exact eval_eq_zero_of_mem_pathEqualityForms _ _ equalityMember
          nextParameter
          (data.boundaryPathCylinder.denominator_ne nextLower nextUpper)

/-- Every phase-local input decision form is stable at all active boundary
samples, using only the selected event cell and no historical box wrapping. -/
theorem activeBoundaryDecisionFormsStable
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0) :
    ActiveBoundaryDecisionFormsStable data squarefree zeroNonzero :=
  activeBoundaryDecisionFormsStable_of_crossingForms data squarefree
    zeroNonzero
      (activeBoundaryDecisionCrossingFormsStable_of_shared data squarefree
        zeroNonzero
          (activeBoundarySharedDecisionFormsStable data squarefree
            zeroNonzero))

/-! ## The fixed equality-convention bit -/

/-- The deterministic local CCL discriminator evaluated on the base
derivative-oriented boundary sample.  This is the equality-convention bit;
it does not assert that the unperturbed boundary point already satisfies the
whole incremental child formula. -/
def activeBoundarySelectedBit
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0) : Bool :=
  inputLocalBit (RawParser.parse current.core.word)
    (activeBoundaryPoint data squarefree zeroNonzero data.output.state)

/-- The source-labelled equality convention selects the same raw bit on
every later derivative-oriented sample of the retained positive event. -/
theorem activeBoundarySelectedBit_eq_localBit
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines data.output.state.box) :
    inputLocalBit (RawParser.parse current.core.word)
        (activeBoundaryPoint data squarefree zeroNonzero next) =
      activeBoundarySelectedBit data squarefree zeroNonzero := by
  let state := RawParser.parse current.core.word
  let basePoint := activeBoundaryPoint data squarefree zeroNonzero
    data.output.state
  let nextPoint := activeBoundaryPoint data squarefree zeroNonzero next
  have baseInsideOutput :=
    (activeBoundaryPoint_strictContains data squarefree degreeNonzero
      zeroNonzero elimination data.output.state
        data.output_refines_separation).contains
  have baseInsideSeparation : data.separation.state.box.Contains basePoint :=
    data.output_refines_separation.contains baseInsideOutput
  have nextInside :=
    (activeBoundaryPoint_strictContains data squarefree degreeNonzero
      zeroNonzero elimination next
        (nextRefines.trans data.output_refines_separation)).contains
  have nextInsideSeparation : data.separation.state.box.Contains nextPoint :=
    data.output_refines_separation.contains (nextRefines.contains nextInside)
  have baseDenominator := separation_denominator_ne data.separation
    baseInsideSeparation
  have nextDenominator := separation_denominator_ne data.separation
    nextInsideSeparation
  have sameBit := inputLocalBit_eq_of_inputDecisionForms_sameSignOrBothZero
    state basePoint nextPoint baseDenominator nextDenominator
      (activeBoundaryDecisionFormsStable data squarefree zeroNonzero next
        nextRefines)
  exact sameBit.symm

/-- Every oriented rational approximation remains exactly on the retained
source comparison curve. -/
theorem activeBoundaryPoint_on_source
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    data.sourceCell.partition.entry.source.form.eval
      (activeBoundaryPoint data squarefree zeroNonzero next) = 0 := by
  rcases activeBoundaryPoint_supported data squarefree zeroNonzero next with
    ⟨parameter, lower, upper, pointEquality⟩
  have pathDenominator :
      data.sourceCell.partition.entry.chart.path.denominator.eval
        (PathPolynomial.ofRat parameter) ≠ 0 := by
    rw [← data.boundaryPathCylinder_path]
    exact data.boundaryPathCylinder.denominator_ne lower upper
  have stateDeterminant :
      determinant (RawParser.parse current.core.word).matrix ≠ 0 := by
    simpa only [determinant, Mat2.det] using
      RawParser.parse_det_ne current.core.word
  rw [pointEquality, data.boundaryPathCylinder_path]
  exact data.sourceCell.partition.entry.onBoundary
    (data.source_determinant_ne stateDeterminant) pathDenominator

/-- Unary and initial comparison boundaries are themselves contained in the
current active radial region.  Thus their equality-convention bit needs no
multi-owner angular perturbation. -/
theorem activeBoundaryPoint_active_of_nonsector
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines data.output.state.box)
    (nonsector : ¬∃ kind exponent bits,
      (RawParser.parse current.core.word).phase =
        .sector kind exponent bits) :
    (inputActiveFormula (RawParser.parse current.core.word)).Holds
      (activeBoundaryPoint data squarefree zeroNonzero next) := by
  let state := RawParser.parse current.core.word
  let point := activeBoundaryPoint data squarefree zeroNonzero next
  have inside :=
    (activeBoundaryPoint_strictContains data squarefree degreeNonzero
      zeroNonzero elimination next
        (nextRefines.trans data.output_refines_separation)).contains
  have denominator := separation_denominator_ne data.separation
    (data.output_refines_separation.contains
      (nextRefines.contains inside))
  rcases List.mem_map.mp data.source_mem_inputPlan with
    ⟨localSource, localMember, sourceEquality⟩
  have pulledZero :
      (pullbackForm (adjugate state.matrix) localSource.form).eval point = 0 := by
    rw [← localSource.form_pullback, sourceEquality]
    exact activeBoundaryPoint_on_source data squarefree zeroNonzero next
  rw [eval_pullbackForm (adjugate state.matrix) localSource.form point
    denominator] at pulledZero
  have localZero : localSource.form.eval
      (RatBox.homographic (adjugate state.matrix) point) = 0 :=
    (mul_eq_zero.mp pulledZero).resolve_left (normSq_pos denominator).ne'
  apply (inputActiveFormula_iff state point denominator).2
  exact localPlan_boundary_active_of_nonsector state.phase localSource
    localMember (RatBox.homographic (adjugate state.matrix) point) localZero
      nonsector

/-- A residual active boundary occurs outside the only phase in which the
history-erased parser can terminate at an exact sector representative. -/
theorem ActivePositiveGuardData.notTerminalSectorAt
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (_data : ActivePositiveGuardData p R hR current)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse current.core.word).phase =
        .sector kind exponent (.two first second))
    (tail : QI) :
    ¬CCL.EncoderParserBridge.TerminalSectorAt
      (RawParser.parse current.core.word) tail := by
  intro terminal
  rcases terminal with
    ⟨kind, exponent, first, second, _third, phase, _full, _residual⟩
  exact notCompleted ⟨kind, exponent, first, second, phase⟩

/-- Once an oriented boundary sample is known to retain the current active
phase, its fixed equality-convention bit satisfies the complete history-free
incremental predicate.  The remaining owner-cone argument is precisely what
must construct such active samples at multiple intersections. -/
theorem activeBoundarySelectedBit_incremental_of_active
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse current.core.word).phase =
        .sector kind exponent (.two first second))
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines data.output.state.box)
    (active : (inputActiveFormula (RawParser.parse current.core.word)).Holds
      (activeBoundaryPoint data squarefree zeroNonzero next)) :
    (inputIncrementalAdvanceFormula (RawParser.parse current.core.word)
      (activeBoundarySelectedBit data squarefree zeroNonzero)).Holds
        (activeBoundaryPoint data squarefree zeroNonzero next) := by
  let state := RawParser.parse current.core.word
  let point := activeBoundaryPoint data squarefree zeroNonzero next
  have inside :=
    (activeBoundaryPoint_strictContains data squarefree degreeNonzero
      zeroNonzero elimination next
        (nextRefines.trans data.output_refines_separation)).contains
  have denominator := separation_denominator_ne data.separation
    (data.output_refines_separation.contains
      (nextRefines.contains inside))
  have notTerminal :
      ¬CCL.EncoderParserBridge.TerminalSectorAt state
        (RatBox.homographic (adjugate state.matrix) point) :=
    ActivePositiveGuardData.notTerminalSectorAt data notCompleted
      (RatBox.homographic (adjugate state.matrix) point)
  have incrementalHolds :=
    inputIncremental_holds_localBit_of_active_notTerminal state
    point denominator active notTerminal
  have chosenBit := activeBoundarySelectedBit_eq_localBit data squarefree
    degreeNonzero zeroNonzero elimination next nextRefines
  rw [chosenBit] at incrementalHolds
  exact incrementalHolds

/-- Every nonsector exact-boundary residue therefore already advances by its
fixed equality-convention bit.  Only the two unfinished angular-sector phases
remain for the finite tangent-cone construction. -/
theorem activeBoundarySelectedBit_incremental_of_nonsector
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines data.output.state.box)
    (nonsector : ¬∃ kind exponent bits,
      (RawParser.parse current.core.word).phase =
        .sector kind exponent bits) :
    (inputIncrementalAdvanceFormula (RawParser.parse current.core.word)
      (activeBoundarySelectedBit data squarefree zeroNonzero)).Holds
        (activeBoundaryPoint data squarefree zeroNonzero next) :=
  activeBoundarySelectedBit_incremental_of_active data squarefree
    degreeNonzero zeroNonzero elimination (by
      rintro ⟨kind, exponent, first, second, phase⟩
      exact nonsector ⟨kind, exponent, .two first second, phase⟩)
      next nextRefines
      (activeBoundaryPoint_active_of_nonsector data squarefree degreeNonzero
        zeroNonzero elimination next nextRefines nonsector)

/-- Persistent active representatives for a solved nonsector boundary event.
Every later winding refinement obtains a fresh point on the same oriented
source path, while the fixed equality-convention bit and both decoder
denominators are retained constructively. -/
def persistentActiveSamplesOfNonsectorBoundary
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (nonsector : ¬∃ kind exponent bits,
      (RawParser.parse current.core.word).phase =
        .sector kind exponent bits)
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR) data.output.state
      (adjugate (RawParser.step (RawParser.parse current.core.word)
        (activeBoundarySelectedBit data squarefree zeroNonzero)).matrix)) :
    PersistentActiveSamples
      (current.core.word ++
        [activeBoundarySelectedBit data squarefree zeroNonzero])
      successorSeparation.state where
  sample next nextRefines := by
    let bit := activeBoundarySelectedBit data squarefree zeroNonzero
    let point := activeBoundaryPoint data squarefree zeroNonzero next
    have nextRefinesOutput : next.box.Refines data.output.state.box :=
      nextRefines.trans successorSeparation.refines
    have inside :=
      (activeBoundaryPoint_strictContains data squarefree degreeNonzero
        zeroNonzero elimination next
          (nextRefinesOutput.trans data.output_refines_separation)).contains
    have oldDenominator := separation_denominator_ne data.separation
      (data.output_refines_separation.contains
        (nextRefinesOutput.contains inside))
    have newDenominator := separation_denominator_ne successorSeparation
      (nextRefines.contains inside)
    exact ActiveBoxSample.ofIncrementalStep bit point inside oldDenominator
      newDenominator
        (activeBoundarySelectedBit_incremental_of_nonsector data squarefree
          degreeNonzero zeroNonzero elimination next nextRefinesOutput
            nonsector)

/-- Install the solved nonsector boundary bit as a repeatable active state.
Its successor cannot yet be a completed two-bit sector, so the phase-indexed
canonical-event obligation is vacuous. -/
def nextOfNonsectorBoundary
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR))
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (nonsector : ¬∃ kind exponent bits,
      (RawParser.parse current.core.word).phase =
        .sector kind exponent bits)
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR) data.output.state
      (adjugate (RawParser.step (RawParser.parse current.core.word)
        (activeBoundarySelectedBit data squarefree zeroNonzero)).matrix)) :
    CCLActiveMetricTrack.State p (RatBox.symmetric R hR) where
  core :=
    { numerical := successorSeparation.state
      word := current.core.word ++
        [activeBoundarySelectedBit data squarefree zeroNonzero] }
  samples := persistentActiveSamplesOfNonsectorBoundary data squarefree
    degreeNonzero zeroNonzero elimination nonsector successorSeparation
  observations := persistentObservationsOfNoncompletedStep current
    successorSeparation.state
      (successorSeparation.refines.trans
        (data.output_refines_separation.trans data.separation.refines))
      (activeBoundarySelectedBit data squarefree zeroNonzero) (by
        rintro ⟨kind, exponent, first, second, phase⟩
        exact nonsector ⟨kind, exponent, .two first second, phase⟩)
  completedSector := .canonical (by
    intro completed
    rw [rawParser_parse_append_singleton] at completed
    exact (rawParser_step_not_completed_of_nonsector
      (RawParser.parse current.core.word)
      (activeBoundarySelectedBit data squarefree zeroNonzero) nonsector
        completed).elim)

theorem nextOfNonsectorBoundary_refines
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR))
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (nonsector : ¬∃ kind exponent bits,
      (RawParser.parse current.core.word).phase =
        .sector kind exponent bits)
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR) data.output.state
      (adjugate (RawParser.step (RawParser.parse current.core.word)
        (activeBoundarySelectedBit data squarefree zeroNonzero)).matrix)) :
    (nextOfNonsectorBoundary current data squarefree degreeNonzero
      zeroNonzero elimination nonsector successorSeparation).core.numerical.box.Refines
        current.core.numerical.box :=
  successorSeparation.refines.trans
    (data.output_refines_separation.trans data.separation.refines)

/-- Execute denominator separation after the solved nonsector boundary bit,
returning either the exact rational terminal or a repeatable active successor. -/
def resolveNonsectorBoundary
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR))
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (nonsector : ¬∃ kind exponent bits,
      (RawParser.parse current.core.word).phase =
        .sector kind exponent bits) : StepResult current := by
  let bit := activeBoundarySelectedBit data squarefree zeroNonzero
  let parser := RawParser.step (RawParser.parse current.core.word) bit
  have parserDeterminant : determinant parser.matrix ≠ 0 := by
    simpa only [parser, determinant, Mat2.det] using
      RawParser.step_det_ne (RawParser.parse current.core.word) bit
        (RawParser.parse_det_ne current.core.word)
  exact match CCLDenominator.decide track data.output.state
      (adjugate parser.matrix)
      (CCLBranchEvidence.adjugate_lowerRow_ne parser.matrix
        parserDeterminant) with
  | CCLDenominator.Decision.terminal point root contains _strict
      _denominatorZero => by
        if zero : point = 0 then
          exact .zero (by simpa only [zero] using root)
        else
          exact .terminal point root zero
            (CCL.RationalEncoder.encode point zero) rfl
            ((data.output_refines_separation.trans data.separation.refines).contains
              contains)
  | CCLDenominator.Decision.separated successorSeparation =>
      let next := nextOfNonsectorBoundary current data squarefree
        degreeNonzero zeroNonzero elimination nonsector successorSeparation
      .next bit next
        (nextOfNonsectorBoundary_refines current data squarefree
          degreeNonzero zeroNonzero elimination nonsector
            successorSeparation) rfl

/-- Finish every exact-boundary residue outside an angular sector.  The only
remaining boundary constructors after this pass have phase `.sector`; all
initial and unary phases have become ordinary repeatable controller steps. -/
def StepOrBoundary.resolveNonsector
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLActiveMetricTrack.State p (RatBox.symmetric R hR)}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    StepOrBoundary current → StepOrBoundary current
  | .ready result => .ready result
  | .boundary data => by
      let state := RawParser.parse current.core.word
      match phaseEquality : state.phase with
      | .initial =>
          exact .ready (resolveNonsectorBoundary track current data squarefree
            degreeNonzero zeroNonzero elimination (by
              rintro ⟨kind, exponent, bits, equality⟩
              simp [state, phaseEquality] at equality))
      | .highUnary count =>
          exact .ready (resolveNonsectorBoundary track current data squarefree
            degreeNonzero zeroNonzero elimination (by
              rintro ⟨kind, exponent, bits, equality⟩
              simp [state, phaseEquality] at equality))
      | .lowUnary count =>
          exact .ready (resolveNonsectorBoundary track current data squarefree
            degreeNonzero zeroNonzero elimination (by
              rintro ⟨kind, exponent, bits, equality⟩
              simp [state, phaseEquality] at equality))
      | .loopUnary count =>
          exact .ready (resolveNonsectorBoundary track current data squarefree
            degreeNonzero zeroNonzero elimination (by
              rintro ⟨kind, exponent, bits, equality⟩
              simp [state, phaseEquality] at equality))
      | .sector kind exponent bits => exact .boundary data

end CCLActiveMetricTrack
end FTA
