import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import CCL.Persistent.ProfileResidual

/-!
# Complete finite refinement families for profile events

`SturmNonzeroEvent.request` deliberately follows one nonzero child.  That is
the right interface for one persistent algebraic event, but it is not a
complete refinement when the starting cell has several nonzero children.
This module builds the full finite binary refinement at a requested width,
filters all and only the nonzero-count children, and retains pointwise
coverage for every supplied displayed rational profile zero.

The construction uses only finite subdivision trees and integer event counts.
In particular, nonzero count is never converted into a root-existence claim.
-/

namespace CCL.PersistentCCLProfileRequestFamily

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm
abbrev BoundedChart := CCL.CCLBoundaryCharts.BoundedChart
abbrev SquarefreeFactorAnalysis :=
  CCL.CCLBoundaryCharts.SquarefreeFactorAnalysis
abbrev ProfileAnalysis
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) :=
  CCL.PersistentCCLProfileResidual.ProfileAnalysis factorAnalysis
abbrev ProfileEventLeaf
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) :=
  CCL.PersistentCCLProfileResidual.ProfileEventLeaf analysis
abbrev Cell := RFAP.SturmEventPartition.Cell
abbrev CurveBoundary := CCL.PersistentCCLDispatch.CurveBoundary
abbrev BoundaryProfileEventEntry
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom) :=
  CCL.PersistentCCLProfileResidual.BoundaryProfileEventEntry
    boundary

section Profile

variable {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
variable {chart : BoundedChart form}
variable {data : CCL.CurveEvents.Nontrivial p
  chart.parameterization.curve}
variable {gcdDegreePositive : 0 <
  (CCL.CurveClear.gcdPolynomial p
    chart.parameterization.curve).natDegree}
variable {factorAnalysis : SquarefreeFactorAnalysis p box chart data
  gcdDegreePositive}
variable {analysis : ProfileAnalysis factorAnalysis}

/-- Finite common-cut depth sufficient for the requested rational width. -/
def completeRequestDepth (leaf : ProfileEventLeaf analysis)
    (epsilon : Coordinate) : Nat :=
  RFAP.SafeCandidates.geometricDepth leaf.cell.interval.width
    epsilon

/-- Full aligned binary subdivision of one original nonzero profile leaf. -/
def completeRequestSubdivision (leaf : ProfileEventLeaf analysis)
    (epsilon : Coordinate) :=
  CCL.CurveBoxEventPartition.Subdivision.build
    analysis.profile.factor.polynomial analysis.profile.factor.nonzero
      chart.parameterization.curve box (completeRequestDepth leaf epsilon)
        leaf.cell

theorem completeRequestCell_refines_leaf
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate)
    {cell : Cell}
    (member : cell ∈ (completeRequestSubdivision leaf epsilon).leaves) :
    cell.interval.Refines leaf.cell.interval :=
  CCL.CurveBoxEventPartition.Subdivision.build_leaf_refines
    analysis.profile.factor.polynomial analysis.profile.factor.nonzero
      chart.parameterization.curve box (completeRequestDepth leaf epsilon)
        leaf.cell member

theorem completeRequestCell_refines_chart
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate)
    {cell : Cell}
    (member : cell ∈ (completeRequestSubdivision leaf epsilon).leaves) :
    cell.interval.Refines chart.cell.interval :=
  RFAP.SturmNonzeroEvent.intervalRefines_trans
    (completeRequestCell_refines_leaf leaf epsilon member)
    leaf.cell_refines_chart

theorem completeRequestCell_width_le
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate)
    (positive : 0 < epsilon) {cell : Cell}
    (member : cell ∈ (completeRequestSubdivision leaf epsilon).leaves) :
    cell.interval.width ≤ epsilon := by
  have geometric :=
    RFAP.SafeCandidates.geometricDepth_sufficient
      leaf.cell.interval.width_nonneg positive
  exact
    (CCL.CurveBoxEventPartition.Subdivision.build_leaf_width_le
      analysis.profile.factor.polynomial analysis.profile.factor.nonzero
        chart.parameterization.curve box (completeRequestDepth leaf epsilon)
          leaf.cell member).trans (by
            simpa only [completeRequestDepth] using geometric)

/-- One retained nonzero-count child from the complete requested
subdivision. -/
structure CompleteRequestLeaf (leaf : ProfileEventLeaf analysis)
    (epsilon : Coordinate) where
  cell : Cell
  member : cell ∈ (completeRequestSubdivision leaf epsilon).leaves
  countNonzero :
    RFAP.SturmRootCount.sturmRootCount2
      analysis.profile.factor.polynomial cell.interval.lower
        cell.interval.upper ≠ 0

namespace CompleteRequestLeaf

def state {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) :
    RFAP.SturmNonzeroEvent.State
      analysis.profile.factor.polynomial :=
  { cell := entry.cell
    countNonzero := entry.countNonzero }

theorem refines_leaf {leaf : ProfileEventLeaf analysis}
    {epsilon : Coordinate} (entry : CompleteRequestLeaf leaf epsilon) :
    entry.cell.interval.Refines leaf.cell.interval :=
  completeRequestCell_refines_leaf leaf epsilon entry.member

theorem refines_chart {leaf : ProfileEventLeaf analysis}
    {epsilon : Coordinate} (entry : CompleteRequestLeaf leaf epsilon) :
    entry.cell.interval.Refines chart.cell.interval :=
  completeRequestCell_refines_chart leaf epsilon entry.member

theorem width_le {leaf : ProfileEventLeaf analysis}
    {epsilon : Coordinate} (entry : CompleteRequestLeaf leaf epsilon)
    (positive : 0 < epsilon) : entry.cell.interval.width ≤ epsilon :=
  completeRequestCell_width_le leaf epsilon positive entry.member

/-- Follow this retained child itself, rather than restarting a later request
from its original profile parent.  This is the persistent finite event branch
used after an owner has been selected. -/
def request {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (target : Coordinate) :
    RFAP.SturmNonzeroEvent.State
      analysis.profile.factor.polynomial :=
  RFAP.SturmNonzeroEvent.request
    analysis.profile.factor.polynomial analysis.profile.factor.nonzero
      entry.state target

theorem request_refines
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (target : Coordinate) :
    (entry.request target).cell.interval.Refines entry.cell.interval := by
  simpa only [request, state] using
    RFAP.SturmNonzeroEvent.request_refines
      analysis.profile.factor.polynomial analysis.profile.factor.nonzero
        entry.state target

theorem request_refines_chart
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (target : Coordinate) :
    (entry.request target).cell.interval.Refines chart.cell.interval :=
  RFAP.SturmNonzeroEvent.intervalRefines_trans
    (entry.request_refines target) entry.refines_chart

theorem request_width_le
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (target : Coordinate)
    (positive : 0 < target) :
    (entry.request target).cell.interval.width ≤ target := by
  simpa only [request, state] using
    RFAP.SturmNonzeroEvent.request_width_le
      analysis.profile.factor.polynomial analysis.profile.factor.nonzero
        entry.state target positive

end CompleteRequestLeaf

/-- Decide whether one child of the complete subdivision carries a nonzero
doubled Sturm event. -/
def completeRequestLeaf?
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate)
    (cell : Cell)
    (member : cell ∈ (completeRequestSubdivision leaf epsilon).leaves) :
    Option (CompleteRequestLeaf leaf epsilon) := by
  if countNonzero :
      RFAP.SturmRootCount.sturmRootCount2
        analysis.profile.factor.polynomial cell.interval.lower
          cell.interval.upper ≠ 0 then
    exact some ⟨cell, member, countNonzero⟩
  else
    exact none

/-- Complete finite list of every nonzero child at the requested width. -/
def completeRequestFamily
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate) :
    List (CompleteRequestLeaf leaf epsilon) :=
  (completeRequestSubdivision leaf epsilon).leaves.attach.filterMap fun entry =>
    completeRequestLeaf? leaf epsilon entry.1 entry.2

theorem completeRequestLeaf?_eq_some
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) :
    completeRequestLeaf? leaf epsilon entry.cell entry.member = some entry := by
  simp only [completeRequestLeaf?, dif_pos entry.countNonzero]

theorem mem_completeRequestFamily
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) :
    entry ∈ completeRequestFamily leaf epsilon := by
  rw [completeRequestFamily, QuotientFreeList.mem_filterMap]
  refine ⟨⟨entry.cell, entry.member⟩, QuotientFreeList.mem_attach _ _, ?_⟩
  exact completeRequestLeaf?_eq_some entry

/-- The complete requested family is nonempty because the exact finite sum
of all child counts equals the parent's retained nonzero count.  This proves
only existence of a nonzero child, never existence of a root. -/
theorem completeRequestFamily_nonempty
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate) :
    completeRequestFamily leaf epsilon ≠ [] := by
  intro familyEmpty
  let event := analysis.profile.factor.polynomial
  let cells := (completeRequestSubdivision leaf epsilon).leaves
  have allCountsZero : ∀ cell ∈ cells,
      CCL.CurveBoxEventPartition.Subdivision.cellEventCount
        event cell = 0 := by
    intro cell member
    by_cases countNonzero :
        RFAP.SturmRootCount.sturmRootCount2 event
          cell.interval.lower cell.interval.upper ≠ 0
    · let entry : CompleteRequestLeaf leaf epsilon :=
        { cell := cell
          member := by simpa only [cells] using member
          countNonzero := by simpa only [event] using countNonzero }
      have retained := mem_completeRequestFamily entry
      rw [familyEmpty] at retained
      exact (List.not_mem_nil retained).elim
    · unfold CCL.CurveBoxEventPartition.Subdivision.cellEventCount
      exact Decidable.not_not.mp countNonzero
  have sumZeroOfAllZero : ∀ values : List Cell,
      (∀ cell ∈ values,
        CCL.CurveBoxEventPartition.Subdivision.cellEventCount
          event cell = 0) →
      (values.map
        (CCL.CurveBoxEventPartition.Subdivision.cellEventCount
          event)).sum = 0 := by
    intro values allZero
    induction values with
    | nil => simp
    | cons head tail inductionHypothesis =>
        rw [List.map_cons, List.sum_cons, allZero head List.mem_cons_self]
        simpa only [Int.zero_add] using
          inductionHypothesis fun cell member =>
            allZero cell (List.mem_cons_of_mem head member)
  have sumZero :
      (cells.map
        (CCL.CurveBoxEventPartition.Subdivision.cellEventCount
          event)).sum = 0 :=
    sumZeroOfAllZero cells allCountsZero
  have parentCountNonzero :
      CCL.CurveBoxEventPartition.Subdivision.cellEventCount
        event leaf.cell ≠ 0 := by
    simpa only [event,
      CCL.CurveBoxEventPartition.Subdivision.cellEventCount,
      leaf.state_cell] using leaf.state.countNonzero
  apply parentCountNonzero
  rw [CCL.CurveBoxEventPartition.Subdivision.build_cellEventCount_sum
    event analysis.profile.factor.nonzero chart.parameterization.curve box
      (completeRequestDepth leaf epsilon) leaf.cell]
  simpa only [cells, event, completeRequestSubdivision] using sumZero

/-- Finite Cauchy--Sturm resolution for any cell in the complete requested
subdivision. -/
def completeRequestResolution
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate)
    (cell : Cell)
    (member : cell ∈ (completeRequestSubdivision leaf epsilon).leaves) :
    RFAP.CauchyCells.CauchyEventResolution
      (RFAP.SturmRootCount.reducedNumerator
        (RFAP.ComputableDerivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial)
      (RFAP.SturmRootCount.reducedDenominator
        (RFAP.ComputableDerivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial)
      cell.interval := by
  apply
    CCL.CurveBoxEventPartition.polynomialEventResolutionOfBounds
      analysis.profile.factor.polynomial chart.cell cell
  · exact completeRequestCell_refines_chart leaf epsilon member
  · have childLeaf := completeRequestCell_refines_leaf leaf epsilon member
    have childWidth : cell.interval.width ≤ leaf.cell.interval.width :=
      RFAP.ConstructiveFraction.sub_le_sub_direct childLeaf.2 childLeaf.1
    have leafWidthSmall : leaf.cell.interval.width <
        CCL.CurveBoxEventPartition.squarefreeLeafWidth
          analysis.profile.factor.polynomial
            analysis.profile.factor.squarefree
              chart.parameterization.curve box chart.cell := by
      simpa only [leaf.classification_cell] using
        leaf.classification.widthSmall
    exact childWidth.trans_lt
      (leafWidthSmall.trans_le
        ((CCL.CurveBoxEventPartition.squarefreeLeafWidth_le_common
          analysis.profile.factor.polynomial
            analysis.profile.factor.squarefree
              chart.parameterization.curve box chart.cell).trans
          (CCL.CurveBoxEventPartition.commonLeafWidth_le_event
            analysis.profile.factor.polynomial chart.parameterization.curve
              box chart.cell)))

/-- Finite Cauchy--Sturm resolution along the deterministic descendant path
of one already retained child.  The construction preserves only its explicit
nonzero integer count and rational interval refinements. -/
def CompleteRequestLeaf.requestResolution
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (target : Coordinate) :
    RFAP.CauchyCells.CauchyEventResolution
      (RFAP.SturmRootCount.reducedNumerator
        (RFAP.ComputableDerivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial)
      (RFAP.SturmRootCount.reducedDenominator
        (RFAP.ComputableDerivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial)
      (entry.request target).cell.interval := by
  apply
    CCL.CurveBoxEventPartition.polynomialEventResolutionOfBounds
      analysis.profile.factor.polynomial chart.cell
        (entry.request target).cell
  · exact entry.request_refines_chart target
  · have requestEntry :
        (entry.request target).cell.interval.Refines entry.cell.interval :=
      entry.request_refines target
    have requestLeaf :
        (entry.request target).cell.interval.Refines leaf.cell.interval :=
      RFAP.SturmNonzeroEvent.intervalRefines_trans requestEntry
        entry.refines_leaf
    have requestWidth : (entry.request target).cell.interval.width ≤
        leaf.cell.interval.width :=
      RFAP.ConstructiveFraction.sub_le_sub_direct requestLeaf.2 requestLeaf.1
    have leafWidthSmall : leaf.cell.interval.width <
        CCL.CurveBoxEventPartition.squarefreeLeafWidth
          analysis.profile.factor.polynomial analysis.profile.factor.squarefree
            chart.parameterization.curve box chart.cell := by
      simpa only [leaf.classification_cell] using
        leaf.classification.widthSmall
    exact requestWidth.trans_lt
      (leafWidthSmall.trans_le
        ((CCL.CurveBoxEventPartition.squarefreeLeafWidth_le_common
          analysis.profile.factor.polynomial
            analysis.profile.factor.squarefree
              chart.parameterization.curve box chart.cell).trans
          (CCL.CurveBoxEventPartition.commonLeafWidth_le_event
            analysis.profile.factor.polynomial chart.parameterization.curve
              box chart.cell)))

namespace CompleteRequestLeaf

/-- The reduced profile polynomial remains uniformly small on every later
deterministic request from this retained child. -/
theorem request_reduced_eval_sq_le
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (target : Coordinate)
    (positive : 0 < target) (parameter : Coordinate)
    (inside : (entry.request target).cell.interval.Contains parameter) :
    (RFAP.SturmRootCount.reducedDenominator
        (RFAP.ComputableDerivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial).eval parameter ^ 2 ≤
      CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.reducedResidualCoefficient
        analysis * target ^ 2 := by
  let event := analysis.profile.factor.polynomial
  let reduced := RFAP.SturmRootCount.reducedDenominator
    (RFAP.ComputableDerivative.derivative event) event
  let localLipschitz :=
    RFAP.IntervalSign.denseEvalSqLipschitzBound reduced
      (entry.request target).cell.interval
  let chartLipschitz :=
    RFAP.IntervalSign.denseEvalSqLipschitzBound reduced
      chart.cell.interval
  have localBound :=
    (entry.requestResolution target).denominator_eval_sq_le
      (entry.request target).countNonzero parameter inside
  have lipschitzLe : localLipschitz ≤ chartLipschitz := by
    simpa only [localLipschitz, chartLipschitz, reduced] using
      RFAP.IntervalSign.denseEvalSqLipschitzBound_le_of_refines
        reduced (entry.request_refines_chart target)
  have chartNonnegative : 0 ≤ chartLipschitz := by
    simpa only [chartLipschitz] using
      (RFAP.IntervalSign.denseHornerSqBounds_nonneg reduced
        chart.cell.interval).2
  have coefficientLe : 4 * localLipschitz ≤ 4 * chartLipschitz :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct lipschitzLe
      (show (0 : Coordinate) ≤ 4 by decide)
  have widthSqLe : (entry.request target).cell.interval.width ^ 2 ≤
      target ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (entry.request target).cell.interval.width_nonneg
        (entry.request_width_le target positive) 2
  change reduced.eval parameter ^ 2 ≤
    (4 * chartLipschitz) * target ^ 2
  exact localBound.trans
    (RFAP.ConstructiveFraction.mul_le_mul_direct coefficientLe widthSqLe
      (RFAP.ConstructiveFraction.sq_nonneg_direct
        (entry.request target).cell.interval.width)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        chartNonnegative))

/-- The profile factor itself stays uniformly small along the selected
descendant event branch. -/
theorem request_factor_eval_sq_le
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (target : Coordinate)
    (positive : 0 < target) (parameter : Coordinate)
    (inside : (entry.request target).cell.interval.Contains parameter) :
    analysis.profile.factor.polynomial.eval parameter ^ 2 ≤
      CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.factorResidualCoefficient
        analysis * target ^ 2 := by
  let event := analysis.profile.factor.polynomial
  let common := RFAP.ComputableGCD.gcd
    (RFAP.ComputableDerivative.derivative event) event
  let reduced := RFAP.SturmRootCount.reducedDenominator
    (RFAP.ComputableDerivative.derivative event) event
  let commonBound := RFAP.PathClearance.evalSqBound common
    chart.cell.interval
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨(entry.request_refines_chart target).1.trans inside.1,
      inside.2.trans (entry.request_refines_chart target).2⟩
  have commonEvalBound : common.eval parameter ^ 2 ≤ commonBound :=
    RFAP.PathClearance.eval_sq_le_evalSqBound common
      chart.cell.interval parameterInsideChart
  have reducedEvalBound : reduced.eval parameter ^ 2 ≤
      CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.reducedResidualCoefficient
        analysis * target ^ 2 := by
    simpa only [event, reduced] using
      entry.request_reduced_eval_sq_le target positive parameter inside
  have productBound :
      common.eval parameter ^ 2 * reduced.eval parameter ^ 2 ≤
        commonBound *
          (CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.reducedResidualCoefficient
            analysis * target ^ 2) :=
    RFAP.ConstructiveFraction.mul_le_mul_direct commonEvalBound
      reducedEvalBound
      (RFAP.ConstructiveFraction.sq_nonneg_direct (reduced.eval parameter))
      (RFAP.PathClearance.evalSqBound_nonneg common
        chart.cell.interval)
  have identity : event.eval parameter =
      common.eval parameter * reduced.eval parameter := by
    simpa only [event, common, reduced,
      RFAP.SturmRootCount.reducedDenominator] using
      RFAP.ComputableGCD.rightFactor_eval_identity
        (RFAP.ComputableDerivative.derivative event) event parameter
  rw [identity, mul_pow]
  change common.eval parameter ^ 2 * reduced.eval parameter ^ 2 ≤
    (commonBound *
      CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.reducedResidualCoefficient
        analysis) * target ^ 2
  exact productBound.trans_eq (by ring1)

/-- Lift the selected descendant's residual through the exact profile
cofactor to the source squarefree curve factor. -/
theorem request_source_factor_eval_sq_le
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (target : Coordinate)
    (positive : 0 < target) (parameter : Coordinate)
    (inside : (entry.request target).cell.interval.Contains parameter) :
    factorAnalysis.factor.polynomial.eval parameter ^ 2 ≤
      CCL.PersistentCCLProfileResidual.sourceFactorResidualCoefficient
        analysis * target ^ 2 := by
  let cofactorBound := RFAP.PathClearance.evalSqBound
    analysis.profile.cofactor chart.cell.interval
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨(entry.request_refines_chart target).1.trans inside.1,
      inside.2.trans (entry.request_refines_chart target).2⟩
  have profileBound :=
    entry.request_factor_eval_sq_le target positive parameter inside
  have cofactorEvalBound : analysis.profile.cofactor.eval parameter ^ 2 ≤
      cofactorBound :=
    RFAP.PathClearance.eval_sq_le_evalSqBound
      analysis.profile.cofactor chart.cell.interval parameterInsideChart
  have productBound :
      analysis.profile.factor.polynomial.eval parameter ^ 2 *
          analysis.profile.cofactor.eval parameter ^ 2 ≤
        (CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.factorResidualCoefficient
            analysis * target ^ 2) * cofactorBound :=
    RFAP.ConstructiveFraction.mul_le_mul_direct profileBound
      cofactorEvalBound
      (RFAP.ConstructiveFraction.sq_nonneg_direct
        (analysis.profile.cofactor.eval parameter))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.factorResidualCoefficient_nonneg
          analysis)
        (RFAP.ConstructiveFraction.sq_nonneg_direct target))
  have identity : factorAnalysis.factor.polynomial.eval parameter =
      analysis.profile.factor.polynomial.eval parameter *
        analysis.profile.cofactor.eval parameter :=
    CCL.CoordinateFactorization.eval_factorization
      analysis.profile.factorization parameter
  rw [identity, mul_pow]
  change analysis.profile.factor.polynomial.eval parameter ^ 2 *
      analysis.profile.cofactor.eval parameter ^ 2 ≤
    (CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.factorResidualCoefficient
        analysis * cofactorBound) * target ^ 2
  exact productBound.trans_eq (by ring1)

/-- Lift the selected descendant through the remaining finite curve-gcd
factors. -/
theorem request_gcd_eval_sq_le
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (target : Coordinate)
    (positive : 0 < target) (parameter : Coordinate)
    (inside : (entry.request target).cell.interval.Contains parameter) :
    (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 ≤
      CCL.PersistentCCLProfileResidual.profileGCDResidualCoefficient
        analysis * target ^ 2 := by
  let decomposition := CCL.CurveEvents.eventDecomposition data
    gcdDegreePositive
  let cofactor :=
    CCL.PersistentCCLCurveEvents.EventLeaf.curveGCDCofactor
      factorAnalysis
  let cofactorBound := RFAP.PathClearance.evalSqBound cofactor
    chart.cell.interval
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨(entry.request_refines_chart target).1.trans inside.1,
      inside.2.trans (entry.request_refines_chart target).2⟩
  have sourceBound :=
    entry.request_source_factor_eval_sq_le target positive parameter inside
  have cofactorEvalBound : cofactor.eval parameter ^ 2 ≤ cofactorBound :=
    RFAP.PathClearance.eval_sq_le_evalSqBound cofactor
      chart.cell.interval parameterInsideChart
  have productBound :
      factorAnalysis.factor.polynomial.eval parameter ^ 2 *
          cofactor.eval parameter ^ 2 ≤
        (CCL.PersistentCCLProfileResidual.sourceFactorResidualCoefficient
            analysis * target ^ 2) * cofactorBound :=
    RFAP.ConstructiveFraction.mul_le_mul_direct sourceBound
      cofactorEvalBound
      (RFAP.ConstructiveFraction.sq_nonneg_direct (cofactor.eval parameter))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (CCL.PersistentCCLProfileResidual.sourceFactorResidualCoefficient_nonneg
          analysis)
        (RFAP.ConstructiveFraction.sq_nonneg_direct target))
  have identity :
      (CCL.CurveClear.gcdPolynomial p
          chart.parameterization.curve).eval parameter =
        factorAnalysis.factor.polynomial.eval parameter *
          cofactor.eval parameter := by
    calc
      (CCL.CurveClear.gcdPolynomial p
          chart.parameterization.curve).eval parameter =
          (CCL.CoordinateFactorization.factorProduct
            decomposition.factors).eval parameter :=
        decomposition.evalIdentity parameter
      _ = factorAnalysis.factor.polynomial.eval parameter *
          (CCL.CoordinateFactorization.factorCofactor
            factorAnalysis.factor.polynomial decomposition.factors).eval
              parameter :=
        CCL.CoordinateFactorization.factorProduct_eval_eq_factor_mul_cofactor
          factorAnalysis.factor decomposition.factors factorAnalysis.member
            parameter
      _ = factorAnalysis.factor.polynomial.eval parameter *
          cofactor.eval parameter := by rfl
  rw [identity, mul_pow]
  change factorAnalysis.factor.polynomial.eval parameter ^ 2 *
      cofactor.eval parameter ^ 2 ≤
    (CCL.PersistentCCLProfileResidual.sourceFactorResidualCoefficient
      analysis * cofactorBound) * target ^ 2
  exact productBound.trans_eq (by ring1)

/-- Lift the descendant residual through both displayed cofactors of the
denominator-cleared rational curve. -/
theorem request_cleared_coordinate_norm_sq_le
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (target : Coordinate)
    (positive : 0 < target) (parameter : Coordinate)
    (inside : (entry.request target).cell.interval.Contains parameter) :
    (CCL.CurveClear.realPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 +
      (CCL.CurveClear.imaginaryPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 ≤
      CCL.PersistentCCLProfileResidual.clearedProfileResidualCoefficient
        analysis * target ^ 2 := by
  let real := CCL.CurveClear.realPolynomial p
    chart.parameterization.curve
  let imaginary := CCL.CurveClear.imaginaryPolynomial p
    chart.parameterization.curve
  let common := CCL.CurveClear.gcdPolynomial p
    chart.parameterization.curve
  let left := RFAP.ComputableGCD.leftFactor real imaginary
  let right := RFAP.ComputableGCD.rightFactor real imaginary
  let liftBound :=
    CCL.PersistentCCLCurveEvents.EventLeaf.curveGCDLiftCoefficient
      p chart
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨(entry.request_refines_chart target).1.trans inside.1,
      inside.2.trans (entry.request_refines_chart target).2⟩
  have commonEvalBound : common.eval parameter ^ 2 ≤
      CCL.PersistentCCLProfileResidual.profileGCDResidualCoefficient
        analysis * target ^ 2 := by
    simpa only [common] using
      entry.request_gcd_eval_sq_le target positive parameter inside
  have leftEvalBound : left.eval parameter ^ 2 ≤
      RFAP.PathClearance.evalSqBound left chart.cell.interval :=
    RFAP.PathClearance.eval_sq_le_evalSqBound left
      chart.cell.interval parameterInsideChart
  have rightEvalBound : right.eval parameter ^ 2 ≤
      RFAP.PathClearance.evalSqBound right chart.cell.interval :=
    RFAP.PathClearance.eval_sq_le_evalSqBound right
      chart.cell.interval parameterInsideChart
  have cofactorSumBound :
      left.eval parameter ^ 2 + right.eval parameter ^ 2 ≤ liftBound := by
    simpa only [left, right, real, imaginary, liftBound,
      CCL.PersistentCCLCurveEvents.EventLeaf.curveGCDLiftCoefficient] using
        add_le_add leftEvalBound rightEvalBound
  have productBound :
      common.eval parameter ^ 2 *
          (left.eval parameter ^ 2 + right.eval parameter ^ 2) ≤
        (CCL.PersistentCCLProfileResidual.profileGCDResidualCoefficient
            analysis * target ^ 2) * liftBound :=
    RFAP.ConstructiveFraction.mul_le_mul_direct commonEvalBound
      cofactorSumBound
      (add_nonneg
        (RFAP.ConstructiveFraction.sq_nonneg_direct (left.eval parameter))
        (RFAP.ConstructiveFraction.sq_nonneg_direct (right.eval parameter)))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (CCL.PersistentCCLProfileResidual.profileGCDResidualCoefficient_nonneg
          analysis)
        (RFAP.ConstructiveFraction.sq_nonneg_direct target))
  have realIdentity : real.eval parameter =
      common.eval parameter * left.eval parameter := by
    simpa only [real, imaginary, common, left,
      CCL.CurveClear.gcdPolynomial] using
      RFAP.ComputableGCD.leftFactor_eval_identity real imaginary parameter
  have imaginaryIdentity : imaginary.eval parameter =
      common.eval parameter * right.eval parameter := by
    simpa only [real, imaginary, common, right,
      CCL.CurveClear.gcdPolynomial] using
      RFAP.ComputableGCD.rightFactor_eval_identity real imaginary parameter
  change real.eval parameter ^ 2 + imaginary.eval parameter ^ 2 ≤
    (CCL.PersistentCCLProfileResidual.profileGCDResidualCoefficient
      analysis * liftBound) * target ^ 2
  rw [realIdentity, imaginaryIdentity, mul_pow, mul_pow]
  calc
    common.eval parameter ^ 2 * left.eval parameter ^ 2 +
        common.eval parameter ^ 2 * right.eval parameter ^ 2 =
      common.eval parameter ^ 2 *
        (left.eval parameter ^ 2 + right.eval parameter ^ 2) := by ring1
    _ ≤ (CCL.PersistentCCLProfileResidual.profileGCDResidualCoefficient
        analysis * target ^ 2) * liftBound := productBound
    _ = (CCL.PersistentCCLProfileResidual.profileGCDResidualCoefficient
        analysis * liftBound) * target ^ 2 := by ring1

/-- Gaussian form of the descendant's cleared-coordinate residual. -/
theorem request_normSq_clearedEval_le
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (target : Coordinate)
    (positive : 0 < target) (parameter : Coordinate)
    (inside : (entry.request target).cell.interval.Contains parameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((CCL.RationalCurve.clearedEval p
          chart.parameterization.curve).eval
            (RFAP.PathPolynomial.ofCoordinate parameter)) ≤
      CCL.PersistentCCLProfileResidual.clearedProfileResidualCoefficient
        analysis * target ^ 2 := by
  simpa only [CCL.CurveClear.realPolynomial,
    CCL.CurveClear.imaginaryPolynomial,
    CCL.RationalCurve.clearedReal,
    CCL.RationalCurve.clearedImag,
    RFAP.PathPolynomial.eval_realPart,
    RFAP.PathPolynomial.eval_imagPart,
    RFAP.ConstructiveGaussian.Gaussian.normSq] using
      entry.request_cleared_coordinate_norm_sq_le target positive parameter
        inside

/-- Every affine point on the selected descendant branch that lies in a
displayed target box has original-polynomial residual of order `target²`. -/
theorem request_normSq_eval_point_le_of_inside
    {targetBox : Box} {leaf : ProfileEventLeaf analysis}
    {epsilon : Coordinate} (entry : CompleteRequestLeaf leaf epsilon)
    (target : Coordinate) (positive : 0 < target) (parameter : Coordinate)
    (parameterInside :
      (entry.request target).cell.interval.Contains parameter)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (pointInside : targetBox.Contains
      (chart.parameterization.curve.point parameter)) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval (chart.parameterization.curve.point parameter)) ≤
      CCL.PersistentCCLProfileResidual.affineProfileResidualCoefficient
          (targetBox := targetBox) analysis * target ^ 2 := by
  let curve := chart.parameterization.curve
  let power :=
    (CCL.RationalCurve.clearingState p curve).denominatorPower.eval
      (RFAP.PathPolynomial.ofCoordinate parameter)
  let lower := chart.affineDenominatorPowerNormSqLower p targetBox
  let residual := RFAP.ConstructiveGaussian.Gaussian.normSq
    (p.eval (curve.point parameter))
  have lowerPositive : 0 < lower := by
    simpa only [lower, curve] using
      chart.affineDenominatorPowerNormSqLower_pos p targetBox
  have powerLower : lower ≤
      RFAP.ConstructiveGaussian.Gaussian.normSq power := by
    simpa only [lower, power, curve] using
      chart.affineDenominatorPowerNormSqLower_le p targetBox parameter
        denominatorNonzero pointInside
  have clearedBound := entry.request_normSq_clearedEval_le target positive
    parameter parameterInside
  have semantics := CCL.RationalCurve.eval_clearedEval p curve
    parameter denominatorNonzero
  have clearedProductBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq power * residual ≤
        CCL.PersistentCCLProfileResidual.clearedProfileResidualCoefficient
          analysis * target ^ 2 := by
    simpa only [curve, power, residual, semantics,
      RFAP.ConstructiveGaussian.Gaussian.normSq_mul] using clearedBound
  have lowerProductBound : lower * residual ≤
      RFAP.ConstructiveGaussian.Gaussian.normSq power * residual :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct powerLower
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
  change residual ≤
    (CCL.PersistentCCLProfileResidual.clearedProfileResidualCoefficient
      analysis / lower) * target ^ 2
  calc
    residual ≤
        (CCL.PersistentCCLProfileResidual.clearedProfileResidualCoefficient
          analysis * target ^ 2) / lower := by
      apply (RFAP.ConstructiveFraction.le_div_iff_pos lowerPositive).2
      calc
        residual * lower = lower * residual :=
          RFAP.ConstructiveFraction.mul_comm _ _
        _ ≤ RFAP.ConstructiveGaussian.Gaussian.normSq power * residual :=
          lowerProductBound
        _ ≤ CCL.PersistentCCLProfileResidual.clearedProfileResidualCoefficient
          analysis * target ^ 2 := clearedProductBound
    _ =
        (CCL.PersistentCCLProfileResidual.clearedProfileResidualCoefficient
          analysis / lower) * target ^ 2 := by
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      rw [RFAP.ConstructiveFraction.mul_assoc,
        RFAP.ConstructiveFraction.mul_comm (target ^ 2),
        ← RFAP.ConstructiveFraction.mul_assoc]

/-- The gcd-reduced profile polynomial is uniformly small throughout every
retained child, not only along the formerly selected request path. -/
theorem reduced_eval_sq_le
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (positive : 0 < epsilon)
    (parameter : Coordinate)
    (inside : entry.cell.interval.Contains parameter) :
    (RFAP.SturmRootCount.reducedDenominator
        (RFAP.ComputableDerivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial).eval parameter ^ 2 ≤
      CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.reducedResidualCoefficient
        analysis * epsilon ^ 2 := by
  let event := analysis.profile.factor.polynomial
  let reduced := RFAP.SturmRootCount.reducedDenominator
    (RFAP.ComputableDerivative.derivative event) event
  let localLipschitz :=
    RFAP.IntervalSign.denseEvalSqLipschitzBound reduced
      entry.cell.interval
  let chartLipschitz :=
    RFAP.IntervalSign.denseEvalSqLipschitzBound reduced
      chart.cell.interval
  have localBound :=
    (completeRequestResolution leaf epsilon entry.cell entry.member).denominator_eval_sq_le
      entry.countNonzero parameter inside
  have lipschitzLe : localLipschitz ≤ chartLipschitz := by
    simpa only [localLipschitz, chartLipschitz, reduced] using
      RFAP.IntervalSign.denseEvalSqLipschitzBound_le_of_refines
        reduced entry.refines_chart
  have chartNonnegative : 0 ≤ chartLipschitz := by
    simpa only [chartLipschitz] using
      (RFAP.IntervalSign.denseHornerSqBounds_nonneg reduced
        chart.cell.interval).2
  have coefficientLe : 4 * localLipschitz ≤ 4 * chartLipschitz :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct lipschitzLe
      (show (0 : Coordinate) ≤ 4 by decide)
  have widthSqLe : entry.cell.interval.width ^ 2 ≤ epsilon ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      entry.cell.interval.width_nonneg (entry.width_le positive) 2
  change reduced.eval parameter ^ 2 ≤
    (4 * chartLipschitz) * epsilon ^ 2
  exact localBound.trans
    (RFAP.ConstructiveFraction.mul_le_mul_direct coefficientLe widthSqLe
      (RFAP.ConstructiveFraction.sq_nonneg_direct entry.cell.interval.width)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        chartNonnegative))

/-- The profile factor itself is uniformly small throughout every retained
child. -/
theorem factor_eval_sq_le
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (positive : 0 < epsilon)
    (parameter : Coordinate)
    (inside : entry.cell.interval.Contains parameter) :
    analysis.profile.factor.polynomial.eval parameter ^ 2 ≤
      CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.factorResidualCoefficient
        analysis * epsilon ^ 2 := by
  let event := analysis.profile.factor.polynomial
  let common := RFAP.ComputableGCD.gcd
    (RFAP.ComputableDerivative.derivative event) event
  let reduced := RFAP.SturmRootCount.reducedDenominator
    (RFAP.ComputableDerivative.derivative event) event
  let commonBound := RFAP.PathClearance.evalSqBound common
    chart.cell.interval
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨entry.refines_chart.1.trans inside.1,
      inside.2.trans entry.refines_chart.2⟩
  have commonEvalBound : common.eval parameter ^ 2 ≤ commonBound :=
    RFAP.PathClearance.eval_sq_le_evalSqBound common
      chart.cell.interval parameterInsideChart
  have reducedEvalBound : reduced.eval parameter ^ 2 ≤
      CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.reducedResidualCoefficient
        analysis * epsilon ^ 2 := by
    simpa only [event, reduced] using
      entry.reduced_eval_sq_le positive parameter inside
  have productBound :
      common.eval parameter ^ 2 * reduced.eval parameter ^ 2 ≤
        commonBound *
          (CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.reducedResidualCoefficient
            analysis * epsilon ^ 2) :=
    RFAP.ConstructiveFraction.mul_le_mul_direct commonEvalBound
      reducedEvalBound
      (RFAP.ConstructiveFraction.sq_nonneg_direct (reduced.eval parameter))
      (RFAP.PathClearance.evalSqBound_nonneg common
        chart.cell.interval)
  have identity : event.eval parameter =
      common.eval parameter * reduced.eval parameter := by
    simpa only [event, common, reduced,
      RFAP.SturmRootCount.reducedDenominator] using
      RFAP.ComputableGCD.rightFactor_eval_identity
        (RFAP.ComputableDerivative.derivative event) event parameter
  rw [identity, mul_pow]
  change common.eval parameter ^ 2 * reduced.eval parameter ^ 2 ≤
    (commonBound *
      CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.reducedResidualCoefficient
        analysis) * epsilon ^ 2
  exact productBound.trans_eq (by ring1)

/-- Fixed finite coefficient carrying a profile-factor residual through an
equality-owned condition's retained cofactor. -/
def equalityConditionResidualCoefficient
    (analysis : ProfileAnalysis factorAnalysis)
    (cofactor : CCL.CoordinateFactorization.Polynomial) :
    Coordinate :=
  CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.factorResidualCoefficient
      analysis *
    RFAP.PathClearance.evalSqBound cofactor chart.cell.interval

theorem equalityConditionResidualCoefficient_nonneg
    (analysis : ProfileAnalysis factorAnalysis)
    (cofactor : CCL.CoordinateFactorization.Polynomial) :
    0 ≤ equalityConditionResidualCoefficient analysis cofactor :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.factorResidualCoefficient_nonneg
      analysis)
    (RFAP.PathClearance.evalSqBound_nonneg cofactor
      chart.cell.interval)

/-- Equality ownership remains quantitative without naming a factor root:
throughout a requested event, the condition residual is bounded by the
profile residual times the explicit equality cofactor bound. -/
theorem equality_condition_eval_sq_le
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (positive : 0 < epsilon)
    (condition cofactor :
      CCL.CoordinateFactorization.Polynomial)
    (factorization : CCL.CoordinateFactorization.Factorization
      condition analysis.profile.factor.polynomial cofactor)
    (parameter : Coordinate)
    (inside : entry.cell.interval.Contains parameter) :
    condition.eval parameter ^ 2 ≤
      equalityConditionResidualCoefficient analysis cofactor * epsilon ^ 2 := by
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨entry.refines_chart.1.trans inside.1,
      inside.2.trans entry.refines_chart.2⟩
  have factorBound := entry.factor_eval_sq_le positive parameter inside
  have cofactorBound :=
    RFAP.PathClearance.eval_sq_le_evalSqBound cofactor
      chart.cell.interval parameterInsideChart
  rw [CCL.CoordinateFactorization.eval_factorization factorization
    parameter, mul_pow]
  exact
    (RFAP.ConstructiveFraction.mul_le_mul_direct factorBound cofactorBound
      (RFAP.ConstructiveFraction.sq_nonneg_direct
        (cofactor.eval parameter))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.factorResidualCoefficient_nonneg
          analysis)
        (RFAP.ConstructiveFraction.sq_nonneg_direct epsilon))).trans_eq (by
          simp only [equalityConditionResidualCoefficient]
          ring1)

/-- Positive event width forcing one equality-owned condition residual below
an arbitrary supplied rational target. -/
def equalityConditionWidth
    (analysis : ProfileAnalysis factorAnalysis)
    (cofactor : CCL.CoordinateFactorization.Polynomial)
    (target : Coordinate) : Coordinate :=
  CCL.PersistentCCLRegionSeparation.shrinkingWidth
    (equalityConditionResidualCoefficient analysis cofactor) target

theorem equalityConditionWidth_pos
    (analysis : ProfileAnalysis factorAnalysis)
    (cofactor : CCL.CoordinateFactorization.Polynomial)
    {target : Coordinate} (targetPositive : 0 < target) :
    0 < equalityConditionWidth analysis cofactor target :=
  CCL.PersistentCCLRegionSeparation.shrinkingWidth_pos
    (equalityConditionResidualCoefficient_nonneg analysis cofactor)
    targetPositive

/-- At every narrower requested width, the explicit equality cofactor turns
the profile-factor approximation into the requested strict condition bound. -/
theorem equality_condition_eval_sq_lt
    {leaf : ProfileEventLeaf analysis} {epsilon target : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (positive : 0 < epsilon)
    (condition cofactor :
      CCL.CoordinateFactorization.Polynomial)
    (factorization : CCL.CoordinateFactorization.Factorization
      condition analysis.profile.factor.polynomial cofactor)
    (epsilonLe : epsilon ≤ equalityConditionWidth analysis cofactor target)
    (targetPositive : 0 < target)
    (parameter : Coordinate)
    (inside : entry.cell.interval.Contains parameter) :
    condition.eval parameter ^ 2 < target := by
  have widthSquareLe : epsilon ^ 2 ≤
      equalityConditionWidth analysis cofactor target ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct positive.le epsilonLe 2
  have scaled :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct widthSquareLe
      (equalityConditionResidualCoefficient_nonneg analysis cofactor)
  exact (entry.equality_condition_eval_sq_le positive condition cofactor
      factorization parameter inside).trans_lt
    (scaled.trans_lt
      (CCL.PersistentCCLRegionSeparation.coefficient_mul_shrinkingWidth_sq_lt
        (equalityConditionResidualCoefficient_nonneg analysis cofactor)
        targetPositive))

/-- The same equality-cofactor estimate on a later deterministic request from
an already retained child.  The conclusion concerns every supplied rational
parameter of that descendant and does not assert a factor zero. -/
theorem request_equality_condition_eval_sq_lt
    {leaf : ProfileEventLeaf analysis} {epsilon target bound : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon)
    (positive : 0 < target)
    (condition cofactor :
      CCL.CoordinateFactorization.Polynomial)
    (factorization : CCL.CoordinateFactorization.Factorization
      condition analysis.profile.factor.polynomial cofactor)
    (targetLe : target ≤ equalityConditionWidth analysis cofactor bound)
    (boundPositive : 0 < bound)
    (parameter : Coordinate)
    (inside : (entry.request target).cell.interval.Contains parameter) :
    condition.eval parameter ^ 2 < bound := by
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨(entry.request_refines_chart target).1.trans inside.1,
      inside.2.trans (entry.request_refines_chart target).2⟩
  have factorBound := entry.request_factor_eval_sq_le target positive
    parameter inside
  have cofactorBound :=
    RFAP.PathClearance.eval_sq_le_evalSqBound cofactor
      chart.cell.interval parameterInsideChart
  have conditionBound : condition.eval parameter ^ 2 ≤
      equalityConditionResidualCoefficient analysis cofactor * target ^ 2 := by
    rw [CCL.CoordinateFactorization.eval_factorization
      factorization parameter, mul_pow]
    exact
      (RFAP.ConstructiveFraction.mul_le_mul_direct factorBound cofactorBound
        (RFAP.ConstructiveFraction.sq_nonneg_direct (cofactor.eval parameter))
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          (CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.factorResidualCoefficient_nonneg
            analysis)
          (RFAP.ConstructiveFraction.sq_nonneg_direct target))).trans_eq (by
            simp only [equalityConditionResidualCoefficient]
            ring1)
  have targetSquareLe : target ^ 2 ≤
      equalityConditionWidth analysis cofactor bound ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct positive.le targetLe 2
  have scaled :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct targetSquareLe
      (equalityConditionResidualCoefficient_nonneg analysis cofactor)
  exact conditionBound.trans_lt
    (scaled.trans_lt
      (CCL.PersistentCCLRegionSeparation.coefficient_mul_shrinkingWidth_sq_lt
        (equalityConditionResidualCoefficient_nonneg analysis cofactor)
        boundPositive))

/-- The source squarefree factor containing the profile is uniformly small
throughout every retained child. -/
theorem source_factor_eval_sq_le
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (positive : 0 < epsilon)
    (parameter : Coordinate)
    (inside : entry.cell.interval.Contains parameter) :
    factorAnalysis.factor.polynomial.eval parameter ^ 2 ≤
      CCL.PersistentCCLProfileResidual.sourceFactorResidualCoefficient
        analysis * epsilon ^ 2 := by
  let cofactorBound := RFAP.PathClearance.evalSqBound
    analysis.profile.cofactor chart.cell.interval
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨entry.refines_chart.1.trans inside.1,
      inside.2.trans entry.refines_chart.2⟩
  have profileBound := entry.factor_eval_sq_le positive parameter inside
  have cofactorEvalBound : analysis.profile.cofactor.eval parameter ^ 2 ≤
      cofactorBound :=
    RFAP.PathClearance.eval_sq_le_evalSqBound
      analysis.profile.cofactor chart.cell.interval parameterInsideChart
  have productBound :
      analysis.profile.factor.polynomial.eval parameter ^ 2 *
          analysis.profile.cofactor.eval parameter ^ 2 ≤
        (CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.factorResidualCoefficient
            analysis * epsilon ^ 2) * cofactorBound :=
    RFAP.ConstructiveFraction.mul_le_mul_direct profileBound
      cofactorEvalBound
      (RFAP.ConstructiveFraction.sq_nonneg_direct
        (analysis.profile.cofactor.eval parameter))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.factorResidualCoefficient_nonneg
          analysis)
        (RFAP.ConstructiveFraction.sq_nonneg_direct epsilon))
  have identity : factorAnalysis.factor.polynomial.eval parameter =
      analysis.profile.factor.polynomial.eval parameter *
        analysis.profile.cofactor.eval parameter :=
    CCL.CoordinateFactorization.eval_factorization
      analysis.profile.factorization parameter
  rw [identity, mul_pow]
  change analysis.profile.factor.polynomial.eval parameter ^ 2 *
      analysis.profile.cofactor.eval parameter ^ 2 ≤
    (CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.factorResidualCoefficient
        analysis * cofactorBound) * epsilon ^ 2
  exact productBound.trans_eq (by ring1)

/-- The complete curve gcd is uniformly small throughout every retained
profile child. -/
theorem gcd_eval_sq_le
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (positive : 0 < epsilon)
    (parameter : Coordinate)
    (inside : entry.cell.interval.Contains parameter) :
    (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 ≤
      CCL.PersistentCCLProfileResidual.profileGCDResidualCoefficient
        analysis * epsilon ^ 2 := by
  let decomposition := CCL.CurveEvents.eventDecomposition data
    gcdDegreePositive
  let cofactor :=
    CCL.PersistentCCLCurveEvents.EventLeaf.curveGCDCofactor
      factorAnalysis
  let cofactorBound := RFAP.PathClearance.evalSqBound cofactor
    chart.cell.interval
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨entry.refines_chart.1.trans inside.1,
      inside.2.trans entry.refines_chart.2⟩
  have sourceBound := entry.source_factor_eval_sq_le positive parameter inside
  have cofactorEvalBound : cofactor.eval parameter ^ 2 ≤ cofactorBound :=
    RFAP.PathClearance.eval_sq_le_evalSqBound cofactor
      chart.cell.interval parameterInsideChart
  have productBound :
      factorAnalysis.factor.polynomial.eval parameter ^ 2 *
          cofactor.eval parameter ^ 2 ≤
        (CCL.PersistentCCLProfileResidual.sourceFactorResidualCoefficient
            analysis * epsilon ^ 2) * cofactorBound :=
    RFAP.ConstructiveFraction.mul_le_mul_direct sourceBound
      cofactorEvalBound
      (RFAP.ConstructiveFraction.sq_nonneg_direct (cofactor.eval parameter))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (CCL.PersistentCCLProfileResidual.sourceFactorResidualCoefficient_nonneg
          analysis)
        (RFAP.ConstructiveFraction.sq_nonneg_direct epsilon))
  have identity :
      (CCL.CurveClear.gcdPolynomial p
          chart.parameterization.curve).eval parameter =
        factorAnalysis.factor.polynomial.eval parameter *
          cofactor.eval parameter := by
    calc
      (CCL.CurveClear.gcdPolynomial p
          chart.parameterization.curve).eval parameter =
          (CCL.CoordinateFactorization.factorProduct
            decomposition.factors).eval parameter :=
        decomposition.evalIdentity parameter
      _ = factorAnalysis.factor.polynomial.eval parameter *
          (CCL.CoordinateFactorization.factorCofactor
            factorAnalysis.factor.polynomial decomposition.factors).eval
              parameter :=
        CCL.CoordinateFactorization.factorProduct_eval_eq_factor_mul_cofactor
          factorAnalysis.factor decomposition.factors factorAnalysis.member
            parameter
      _ = factorAnalysis.factor.polynomial.eval parameter *
          cofactor.eval parameter := by rfl
  rw [identity, mul_pow]
  change factorAnalysis.factor.polynomial.eval parameter ^ 2 *
      cofactor.eval parameter ^ 2 ≤
    (CCL.PersistentCCLProfileResidual.sourceFactorResidualCoefficient
      analysis * cofactorBound) * epsilon ^ 2
  exact productBound.trans_eq (by ring1)

/-- Both denominator-cleared coordinates of the original polynomial are
uniformly small throughout every retained profile child. -/
theorem cleared_coordinate_norm_sq_le
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (positive : 0 < epsilon)
    (parameter : Coordinate)
    (inside : entry.cell.interval.Contains parameter) :
    (CCL.CurveClear.realPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 +
      (CCL.CurveClear.imaginaryPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 ≤
      CCL.PersistentCCLProfileResidual.clearedProfileResidualCoefficient
        analysis * epsilon ^ 2 := by
  let real := CCL.CurveClear.realPolynomial p
    chart.parameterization.curve
  let imaginary := CCL.CurveClear.imaginaryPolynomial p
    chart.parameterization.curve
  let common := CCL.CurveClear.gcdPolynomial p
    chart.parameterization.curve
  let left := RFAP.ComputableGCD.leftFactor real imaginary
  let right := RFAP.ComputableGCD.rightFactor real imaginary
  let liftBound :=
    CCL.PersistentCCLCurveEvents.EventLeaf.curveGCDLiftCoefficient
      p chart
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨entry.refines_chart.1.trans inside.1,
      inside.2.trans entry.refines_chart.2⟩
  have commonEvalBound : common.eval parameter ^ 2 ≤
      CCL.PersistentCCLProfileResidual.profileGCDResidualCoefficient
        analysis * epsilon ^ 2 := by
    simpa only [common] using entry.gcd_eval_sq_le positive parameter inside
  have leftEvalBound : left.eval parameter ^ 2 ≤
      RFAP.PathClearance.evalSqBound left chart.cell.interval :=
    RFAP.PathClearance.eval_sq_le_evalSqBound left
      chart.cell.interval parameterInsideChart
  have rightEvalBound : right.eval parameter ^ 2 ≤
      RFAP.PathClearance.evalSqBound right chart.cell.interval :=
    RFAP.PathClearance.eval_sq_le_evalSqBound right
      chart.cell.interval parameterInsideChart
  have cofactorSumBound :
      left.eval parameter ^ 2 + right.eval parameter ^ 2 ≤ liftBound := by
    simpa only [left, right, real, imaginary, liftBound,
      CCL.PersistentCCLCurveEvents.EventLeaf.curveGCDLiftCoefficient] using
        add_le_add leftEvalBound rightEvalBound
  have productBound :
      common.eval parameter ^ 2 *
          (left.eval parameter ^ 2 + right.eval parameter ^ 2) ≤
        (CCL.PersistentCCLProfileResidual.profileGCDResidualCoefficient
            analysis * epsilon ^ 2) * liftBound :=
    RFAP.ConstructiveFraction.mul_le_mul_direct commonEvalBound
      cofactorSumBound
      (add_nonneg
        (RFAP.ConstructiveFraction.sq_nonneg_direct (left.eval parameter))
        (RFAP.ConstructiveFraction.sq_nonneg_direct (right.eval parameter)))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (CCL.PersistentCCLProfileResidual.profileGCDResidualCoefficient_nonneg
          analysis)
        (RFAP.ConstructiveFraction.sq_nonneg_direct epsilon))
  have realIdentity : real.eval parameter =
      common.eval parameter * left.eval parameter := by
    simpa only [real, imaginary, common, left,
      CCL.CurveClear.gcdPolynomial] using
      RFAP.ComputableGCD.leftFactor_eval_identity real imaginary parameter
  have imaginaryIdentity : imaginary.eval parameter =
      common.eval parameter * right.eval parameter := by
    simpa only [real, imaginary, common, right,
      CCL.CurveClear.gcdPolynomial] using
      RFAP.ComputableGCD.rightFactor_eval_identity real imaginary parameter
  change real.eval parameter ^ 2 + imaginary.eval parameter ^ 2 ≤
    (CCL.PersistentCCLProfileResidual.profileGCDResidualCoefficient
      analysis * liftBound) * epsilon ^ 2
  rw [realIdentity, imaginaryIdentity, mul_pow, mul_pow]
  calc
    common.eval parameter ^ 2 * left.eval parameter ^ 2 +
        common.eval parameter ^ 2 * right.eval parameter ^ 2 =
      common.eval parameter ^ 2 *
        (left.eval parameter ^ 2 + right.eval parameter ^ 2) := by ring1
    _ ≤ (CCL.PersistentCCLProfileResidual.profileGCDResidualCoefficient
        analysis * epsilon ^ 2) * liftBound := productBound
    _ = (CCL.PersistentCCLProfileResidual.profileGCDResidualCoefficient
        analysis * liftBound) * epsilon ^ 2 := by ring1

/-- Gaussian form of the retained child's cleared-coordinate residual. -/
theorem normSq_clearedEval_le
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (positive : 0 < epsilon)
    (parameter : Coordinate)
    (inside : entry.cell.interval.Contains parameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((CCL.RationalCurve.clearedEval p
          chart.parameterization.curve).eval
            (RFAP.PathPolynomial.ofCoordinate parameter)) ≤
      CCL.PersistentCCLProfileResidual.clearedProfileResidualCoefficient
        analysis * epsilon ^ 2 := by
  simpa only [CCL.CurveClear.realPolynomial,
    CCL.CurveClear.imaginaryPolynomial,
    CCL.RationalCurve.clearedReal,
    CCL.RationalCurve.clearedImag,
    RFAP.PathPolynomial.eval_realPart,
    RFAP.PathPolynomial.eval_imagPart,
    RFAP.ConstructiveGaussian.Gaussian.normSq] using
      entry.cleared_coordinate_norm_sq_le positive parameter inside

/-- Every affine point where a retained child meets a displayed box has a
uniformly small original-polynomial residual. -/
theorem normSq_eval_point_le_of_inside
    {targetBox : Box} {leaf : ProfileEventLeaf analysis}
    {epsilon : Coordinate} (entry : CompleteRequestLeaf leaf epsilon)
    (positive : 0 < epsilon) (parameter : Coordinate)
    (parameterInside : entry.cell.interval.Contains parameter)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (pointInside : targetBox.Contains
      (chart.parameterization.curve.point parameter)) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval (chart.parameterization.curve.point parameter)) ≤
      CCL.PersistentCCLProfileResidual.affineProfileResidualCoefficient
          (targetBox := targetBox) analysis * epsilon ^ 2 := by
  let curve := chart.parameterization.curve
  let power :=
    (CCL.RationalCurve.clearingState p curve).denominatorPower.eval
      (RFAP.PathPolynomial.ofCoordinate parameter)
  let lower := chart.affineDenominatorPowerNormSqLower p targetBox
  let residual := RFAP.ConstructiveGaussian.Gaussian.normSq
    (p.eval (curve.point parameter))
  have lowerPositive : 0 < lower := by
    simpa only [lower, curve] using
      chart.affineDenominatorPowerNormSqLower_pos p targetBox
  have powerLower : lower ≤
      RFAP.ConstructiveGaussian.Gaussian.normSq power := by
    simpa only [lower, power, curve] using
      chart.affineDenominatorPowerNormSqLower_le p targetBox parameter
        denominatorNonzero pointInside
  have clearedBound := entry.normSq_clearedEval_le positive parameter
    parameterInside
  have semantics := CCL.RationalCurve.eval_clearedEval p curve
    parameter denominatorNonzero
  have clearedProductBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq power * residual ≤
        CCL.PersistentCCLProfileResidual.clearedProfileResidualCoefficient
          analysis * epsilon ^ 2 := by
    simpa only [curve, power, residual, semantics,
      RFAP.ConstructiveGaussian.Gaussian.normSq_mul] using clearedBound
  have lowerProductBound : lower * residual ≤
      RFAP.ConstructiveGaussian.Gaussian.normSq power * residual :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct powerLower
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
  change residual ≤
    (CCL.PersistentCCLProfileResidual.clearedProfileResidualCoefficient
      analysis / lower) * epsilon ^ 2
  calc
    residual ≤
        (CCL.PersistentCCLProfileResidual.clearedProfileResidualCoefficient
          analysis * epsilon ^ 2) / lower := by
      apply (RFAP.ConstructiveFraction.le_div_iff_pos lowerPositive).2
      calc
        residual * lower = lower * residual :=
          RFAP.ConstructiveFraction.mul_comm _ _
        _ ≤ RFAP.ConstructiveGaussian.Gaussian.normSq power * residual :=
          lowerProductBound
        _ ≤ CCL.PersistentCCLProfileResidual.clearedProfileResidualCoefficient
          analysis * epsilon ^ 2 := clearedProductBound
    _ =
        (CCL.PersistentCCLProfileResidual.clearedProfileResidualCoefficient
          analysis / lower) * epsilon ^ 2 := by
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      rw [RFAP.ConstructiveFraction.mul_assoc,
        RFAP.ConstructiveFraction.mul_comm (epsilon ^ 2),
        ← RFAP.ConstructiveFraction.mul_assoc]

/-- Every apart condition remains uniformly separated from zero throughout a
retained child at any positive width below its rational sign width. -/
theorem apartConditionLower_lt_eval_sq
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon)
    (condition : CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤
      CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.apartSignWidth
        analysis condition apart)
    (parameter : Coordinate)
    (inside : entry.cell.interval.Contains parameter) :
    CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.apartConditionLower
        analysis condition apart <
      condition.eval parameter ^ 2 :=
  CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.apartConditionLower_lt_eval_sq_on_cell
    entry.cell condition apart epsilon positive epsilonLe entry.refines_chart
      (entry.width_le positive)
      (fun value valueInside =>
        entry.factor_eval_sq_le positive value valueInside)
      parameter inside

/-- Every apart condition has one stable strict sign throughout a retained
child at any positive width below the profile-wide sign width. -/
theorem condition_eval_mul_pos
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon)
    (condition : CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤
      CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.apartSignWidth
        analysis condition apart)
    {left right : Coordinate}
    (leftInside : entry.cell.interval.Contains left)
    (rightInside : entry.cell.interval.Contains right) :
    0 < condition.eval left * condition.eval right :=
  CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.condition_eval_mul_pos_on_cell
    entry.cell condition apart epsilon positive epsilonLe entry.refines_chart
      (entry.width_le positive)
      (fun parameter parameterInside =>
        entry.factor_eval_sq_le positive parameter parameterInside)
      leftInside rightInside

/-- Constructive nonnegativity data appropriate to one exact profile
relation.  Equality-owned conditions are required only at a separately
supplied displayed rational factor zero; apart conditions retain their stable
nonnegative sign throughout the whole rational cell. -/
def ConditionNonnegative
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon)
    (relation :
      CCL.PersistentCCLConditionProfiles.ProfileRelation
        analysis) : Prop :=
  match relation with
  | ⟨condition, .equality _cofactor _factorization⟩ =>
      ∀ parameter : Coordinate,
        entry.cell.interval.Contains parameter →
        analysis.profile.factor.polynomial.eval parameter = 0 →
        0 ≤ condition.eval parameter
  | ⟨condition, .apart _apart⟩ =>
      ∀ parameter : Coordinate,
        entry.cell.interval.Contains parameter →
        0 ≤ condition.eval parameter

/-- Either form of the retained relation certificate supplies nonnegativity
at a separately supplied displayed rational profile zero. -/
theorem ConditionNonnegative.atFactorZero
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    {entry : CompleteRequestLeaf leaf epsilon}
    {relation :
      CCL.PersistentCCLConditionProfiles.ProfileRelation analysis}
    (holds : ConditionNonnegative entry relation)
    (parameter : Coordinate)
    (inside : entry.cell.interval.Contains parameter)
    (factorZero :
      analysis.profile.factor.polynomial.eval parameter = 0) :
    0 ≤ relation.1.eval parameter := by
  rcases relation with ⟨condition, relation⟩
  cases relation with
  | equality cofactor factorization =>
      exact holds parameter inside factorZero
  | apart apart =>
      exact holds parameter inside

/-- One relation is strictly negative at every rational parameter of a
retained child. -/
def ConditionNegative
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon)
    (relation :
      CCL.PersistentCCLConditionProfiles.ProfileRelation
        analysis) : Prop :=
  ∀ parameter : Coordinate,
    entry.cell.interval.Contains parameter →
    relation.1.eval parameter < 0

/-- Exact finite classification of one relation on a retained child. -/
inductive RelationClassification
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon)
    (relation :
      CCL.PersistentCCLConditionProfiles.ProfileRelation
        analysis) where
  | nonnegative (holds : ConditionNonnegative entry relation)
  | negative (holds : ConditionNegative entry relation)

private theorem negative_of_mul_pos_right_neg
    {left right : Coordinate} (product : 0 < left * right)
    (rightNegative : right < 0) : left < 0 := by
  rcases lt_trichotomy left 0 with leftNegative | leftZero | leftPositive
  · exact leftNegative
  · rw [leftZero, RFAP.ConstructiveFraction.zero_mul_direct] at product
    exact (lt_irrefl 0 product).elim
  · have negative :=
      RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
        leftPositive rightNegative
    exact (lt_asymm product negative).elim

private theorem positive_of_mul_pos_right_pos
    {left right : Coordinate} (product : 0 < left * right)
    (rightPositive : 0 < right) : 0 < left := by
  rcases lt_trichotomy left 0 with leftNegative | leftZero | leftPositive
  · have negative :=
      RFAP.ConstructiveFraction.mul_neg_of_neg_of_pos_direct
        leftNegative rightPositive
    exact (lt_asymm product negative).elim
  · rw [leftZero, RFAP.ConstructiveFraction.zero_mul_direct] at product
    exact (lt_irrefl 0 product).elim
  · exact leftPositive

/-- Classify one equality/apart relation from one rational sample in the
retained child. -/
def classifyRelation
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon)
    (relation :
      CCL.PersistentCCLConditionProfiles.ProfileRelation
        analysis)
    (member : relation ∈ analysis.profile.relations)
    (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤
      CCL.PersistentCCLConditionProfiles.profileSignWidth
        analysis)
    (sample : Coordinate)
    (sampleInside : entry.cell.interval.Contains sample) :
    RelationClassification entry relation := by
  rcases relation with ⟨condition, relation⟩
  cases relation with
  | equality cofactor factorization =>
      exact .nonnegative (by
        intro parameter _inside factorZero
        rw [CCL.CoordinateFactorization.eval_factorization
          factorization parameter, factorZero,
          RFAP.ConstructiveFraction.zero_mul_direct])
  | apart apart =>
      have apartWidthLe : epsilon ≤
          CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.apartSignWidth
            analysis condition apart :=
        epsilonLe.trans
          (CCL.PersistentCCLConditionProfiles.profileSignWidth_le_apart
            analysis condition apart member)
      have sampleStable := entry.condition_eval_mul_pos condition apart
        positive apartWidthLe sampleInside sampleInside
      by_cases sampleNegative : condition.eval sample < 0
      · exact .negative (by
          intro parameter parameterInside
          exact negative_of_mul_pos_right_neg
            (entry.condition_eval_mul_pos condition apart positive apartWidthLe
              parameterInside sampleInside)
            sampleNegative)
      · have sampleNonnegative : 0 ≤ condition.eval sample :=
          le_of_not_gt sampleNegative
        have sampleNonzero : condition.eval sample ≠ 0 := by
          intro sampleZero
          rw [sampleZero, RFAP.ConstructiveFraction.zero_mul_direct]
            at sampleStable
          exact (lt_irrefl 0 sampleStable).elim
        have samplePositive : 0 < condition.eval sample :=
          lt_of_le_of_ne sampleNonnegative (Ne.symm sampleNonzero)
        exact .nonnegative (by
          intro parameter parameterInside
          exact (positive_of_mul_pos_right_pos
            (entry.condition_eval_mul_pos condition apart positive apartWidthLe
              parameterInside sampleInside)
            samplePositive).le)

/-- Finite scan result for any displayed sublist of a retained child's
profile relations. -/
inductive RelationsClassification
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon)
    (relations : List
      (CCL.PersistentCCLConditionProfiles.ProfileRelation
        analysis)) where
  | inside (holds : ∀ relation ∈ relations,
      ConditionNonnegative entry relation)
  | outside (relation :
      CCL.PersistentCCLConditionProfiles.ProfileRelation analysis)
      (member : relation ∈ relations)
      (fails : ConditionNegative entry relation)

/-- Execute the exact equality/apart scan for a retained child. -/
def classifyRelations
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon)
    (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤
      CCL.PersistentCCLConditionProfiles.profileSignWidth
        analysis)
    (sample : Coordinate)
    (sampleInside : entry.cell.interval.Contains sample) :
    ∀ relations : List
        (CCL.PersistentCCLConditionProfiles.ProfileRelation
          analysis),
      (∀ relation ∈ relations, relation ∈ analysis.profile.relations) →
      RelationsClassification entry relations
  | [], _ => .inside (by intro relation member; simp at member)
  | head :: tail, subset =>
      match classifyRelation entry head (subset head List.mem_cons_self)
          positive epsilonLe sample sampleInside with
      | .negative fails => .outside head List.mem_cons_self fails
      | .nonnegative headHolds =>
          match classifyRelations entry positive epsilonLe sample sampleInside
              tail (fun relation member =>
                subset relation (List.mem_cons_of_mem head member)) with
          | .outside relation member fails =>
              .outside relation (List.mem_cons_of_mem head member) fails
          | .inside tailHolds =>
              .inside (by
                intro relation member
                rcases List.mem_cons.mp member with rfl | tailMember
                · exact headHolds
                · exact tailHolds relation tailMember)

/-- Semantic box classification of a complete retained child. -/
inductive BoxClassification
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) where
  | inside (holds : ∀ relation ∈ analysis.profile.relations,
      ConditionNonnegative entry relation)
  | outside (relation :
      CCL.PersistentCCLConditionProfiles.ProfileRelation analysis)
      (member : relation ∈ analysis.profile.relations)
      (fails : ConditionNegative entry relation)

/-- Compute the whole retained-child box classification from its rational
lower endpoint. -/
def classifyBox
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon)
    (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤
      CCL.PersistentCCLConditionProfiles.profileSignWidth
        analysis) : BoxClassification entry := by
  let sample := entry.cell.interval.lower
  have sampleInside : entry.cell.interval.Contains sample :=
    ⟨le_rfl, entry.cell.proper.le⟩
  have classified := classifyRelations entry positive epsilonLe sample
    sampleInside analysis.profile.relations
    (by intro relation member; exact member)
  cases classified with
  | inside allNonnegative => exact .inside allNonnegative
  | outside relation member fails => exact .outside relation member fails

/-- Affine meaning of a retained child's exact finite classification.  The
inside branch remains conditional on a supplied displayed rational profile
zero; the outside branch excludes every non-pole rational parameter. -/
inductive AffineClassification
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) where
  | inside (contains : ∀ parameter : Coordinate,
      entry.cell.interval.Contains parameter →
      analysis.profile.factor.polynomial.eval parameter = 0 →
      chart.parameterization.curve.denominatorAt parameter ≠ 0 →
      box.Contains (chart.parameterization.curve.point parameter))
  | outside (excludes : ∀ parameter : Coordinate,
      entry.cell.interval.Contains parameter →
      chart.parameterization.curve.denominatorAt parameter ≠ 0 →
      ¬ box.Contains (chart.parameterization.curve.point parameter))

/-- Exact affine containment recovered from the complete retained
per-relation certificate and a separately supplied displayed rational profile
zero. -/
theorem contains_of_relations_nonnegative
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon)
    (allNonnegative : ∀ relation ∈ analysis.profile.relations,
      ConditionNonnegative entry relation)
    (parameter : Coordinate)
    (parameterInside : entry.cell.interval.Contains parameter)
    (factorZero :
      analysis.profile.factor.polynomial.eval parameter = 0)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0) :
    box.Contains (chart.parameterization.curve.point parameter) := by
  have relationsNonnegative :
      CCL.PersistentCCLConditionProfiles.RelationsNonnegativeAt
        analysis parameter :=
    List.forall_iff_forall_mem.mpr (by
      intro relation member
      exact (allNonnegative relation member).atFactorZero parameter
        parameterInside factorZero)
  have listed :=
    (CCL.PersistentCCLConditionProfiles.relationsNonnegativeAt_iff_listedHolds
      analysis parameter).mp relationsNonnegative
  have holds :=
    (CCL.CurveBoxConditions.listedHolds_iff_holds
      chart.parameterization.curve box parameter).mp listed
  exact (CCL.CurveBoxConditions.holds_iff_contains
    chart.parameterization.curve box parameter denominatorNonzero).mp holds

/-- Exact whole-cell affine exclusion recovered from one retained negative
relation. -/
theorem excludes_of_relation_negative
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon)
    (relation :
      CCL.PersistentCCLConditionProfiles.ProfileRelation analysis)
    (member : relation ∈ analysis.profile.relations)
    (negative : ConditionNegative entry relation)
    (parameter : Coordinate)
    (parameterInside : entry.cell.interval.Contains parameter)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0) :
    ¬box.Contains (chart.parameterization.curve.point parameter) := by
  intro contained
  have holds :=
    (CCL.CurveBoxConditions.holds_iff_contains
      chart.parameterization.curve box parameter denominatorNonzero).mpr
        contained
  have listed :=
    (CCL.CurveBoxConditions.listedHolds_iff_holds
      chart.parameterization.curve box parameter).mpr holds
  have relationsNonnegative :=
    (CCL.PersistentCCLConditionProfiles.relationsNonnegativeAt_iff_listedHolds
      analysis parameter).mpr listed
  have relationNonnegative :=
    (List.forall_iff_forall_mem.mp relationsNonnegative) relation member
  exact (not_lt_of_ge relationNonnegative)
    (negative parameter parameterInside)

/-- Convert one retained finite box classification into its exact affine
semantics without discarding the original per-relation certificate. -/
def BoxClassification.toAffine
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    {entry : CompleteRequestLeaf leaf epsilon}
    (classification : BoxClassification entry) : AffineClassification entry :=
  match classification with
  | .inside allNonnegative =>
      .inside (entry.contains_of_relations_nonnegative allNonnegative)
  | .outside relation member negative =>
      .outside (entry.excludes_of_relation_negative relation member negative)

/-- Convert the retained child's finite sign scan into exact affine box
semantics. -/
def classifyAffine
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon)
    (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤
      CCL.PersistentCCLConditionProfiles.profileSignWidth
        analysis) : AffineClassification entry :=
  (entry.classifyBox positive epsilonLe).toAffine

/-- Homogeneous chordal diameter bound for every retained child,
independently of affine poles. -/
theorem chordalSq_le
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon) (positive : 0 < epsilon)
    {left right : Coordinate}
    (leftInside : entry.cell.interval.Contains left)
    (rightInside : entry.cell.interval.Contains right) :
    CCL.Chordal.chordalSq
        (chart.projective left) (chart.projective right) ≤
      chart.uniformChordalVariationCoefficient * epsilon ^ 2 := by
  have leftChart : chart.cell.interval.Contains left :=
    ⟨entry.refines_chart.1.trans leftInside.1,
      leftInside.2.trans entry.refines_chart.2⟩
  have rightChart : chart.cell.interval.Contains right :=
    ⟨entry.refines_chart.1.trans rightInside.1,
      rightInside.2.trans entry.refines_chart.2⟩
  have parameterBound :=
    CCL.RationalCurveBounds.parameter_sub_sq_le_width_sq
      entry.cell.interval leftInside rightInside
  have widthSquare : entry.cell.interval.width ^ 2 ≤ epsilon ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      entry.cell.interval.width_nonneg (entry.width_le positive) 2
  exact (chart.chordalSq_le_uniform leftChart rightChart).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (parameterBound.trans widthSquare)
      chart.uniformChordalVariationCoefficient_nonneg)

end CompleteRequestLeaf

/-! ## Explicit denominator relation of every final profile -/

/-- The first retained profile relation is the homogeneous curve-denominator
quadrance.  Keeping its membership proof makes the pole/apart split available
without searching an unbounded carrier. -/
structure ProfileDenominatorRelation
    (analysis : ProfileAnalysis factorAnalysis) where
  relation : CCL.CoordinateFactorization.ConditionRelation
    (CCL.CurveBoxConditions.denominatorNormSq
      chart.parameterization.curve)
    analysis.profile.factor
  member :
    (⟨CCL.CurveBoxConditions.denominatorNormSq
        chart.parameterization.curve, relation⟩ :
      CCL.PersistentCCLConditionProfiles.ProfileRelation
        analysis) ∈ analysis.profile.relations

/-- Recover the denominator relation from the exact finite list-alignment
certificate. -/
def profileDenominatorRelation
    (analysis : ProfileAnalysis factorAnalysis) :
    ProfileDenominatorRelation analysis := by
  cases relationsEq : analysis.profile.relations with
  | nil =>
      have aligned := analysis.profile.conditions_eq
      rw [relationsEq] at aligned
      simp only [List.map_nil,
        CCL.CurveBoxConditions.profiledConditionPolynomials]
        at aligned
      cases aligned
  | cons head tail =>
      rcases head with ⟨condition, relation⟩
      have aligned := analysis.profile.conditions_eq
      rw [relationsEq] at aligned
      simp only [List.map_cons,
        CCL.CurveBoxConditions.profiledConditionPolynomials]
        at aligned
      have conditionEq := (List.cons.inj aligned).1
      subst condition
      exact
        { relation := relation
          member := by rw [relationsEq]; exact List.mem_cons_self }

namespace ProfileDenominatorRelation

/-- Positive rational affine-denominator lower bound contributed by an apart
denominator relation.  The minimum with one avoids taking a square root. -/
def apartLower
    {analysis : ProfileAnalysis factorAnalysis}
    (_entry : ProfileDenominatorRelation analysis)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial
        (CCL.CurveBoxConditions.denominatorNormSq
          chart.parameterization.curve)) : Coordinate :=
  min 1
    (CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.apartConditionLower
      analysis
        (CCL.CurveBoxConditions.denominatorNormSq
          chart.parameterization.curve)
        apart)

theorem apartLower_pos
    {analysis : ProfileAnalysis factorAnalysis}
    (entry : ProfileDenominatorRelation analysis)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial
        (CCL.CurveBoxConditions.denominatorNormSq
          chart.parameterization.curve)) :
    0 < entry.apartLower apart :=
  lt_min (by decide)
    (CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.apartConditionLower_pos
      analysis
        (CCL.CurveBoxConditions.denominatorNormSq
          chart.parameterization.curve)
        apart)

end ProfileDenominatorRelation

namespace CompleteRequestLeaf

/-- An apart denominator relation supplies a uniform positive rational lower
bound for the affine denominator quadrance throughout the retained cell. -/
theorem denominatorNormSq_lower_of_apart
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (requestEntry : CompleteRequestLeaf leaf epsilon)
    (denominator : ProfileDenominatorRelation analysis)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial
        (CCL.CurveBoxConditions.denominatorNormSq
          chart.parameterization.curve))
    (relationEq : denominator.relation =
      CCL.CoordinateFactorization.ConditionRelation.apart apart)
    (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤
      CCL.PersistentCCLConditionProfiles.profileSignWidth
        analysis)
    (parameter : Coordinate)
    (inside : requestEntry.cell.interval.Contains parameter) :
    denominator.apartLower apart ≤
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (chart.parameterization.curve.denominatorAt parameter) := by
  have relationMember := denominator.member
  rw [relationEq] at relationMember
  have epsilonLeApart : epsilon ≤
      CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.apartSignWidth
        analysis
          (CCL.CurveBoxConditions.denominatorNormSq
            chart.parameterization.curve)
          apart :=
    epsilonLe.trans
      (CCL.PersistentCCLConditionProfiles.profileSignWidth_le_apart
        analysis
          (CCL.CurveBoxConditions.denominatorNormSq
            chart.parameterization.curve)
          apart relationMember)
  have squareLower := requestEntry.apartConditionLower_lt_eval_sq
    (CCL.CurveBoxConditions.denominatorNormSq
      chart.parameterization.curve)
    apart positive epsilonLeApart parameter inside
  let value := RFAP.ConstructiveGaussian.Gaussian.normSq
    (chart.parameterization.curve.denominatorAt parameter)
  have lowerLtSquare :
      CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.apartConditionLower
          analysis
            (CCL.CurveBoxConditions.denominatorNormSq
              chart.parameterization.curve)
            apart < value ^ 2 := by
    simpa only [value,
      CCL.CurveBoxConditions.eval_denominatorNormSq] using
      squareLower
  have valueNonnegative : 0 ≤ value :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
  by_cases oneLe : 1 ≤ value
  · exact (min_le_left _ _).trans oneLe
  · have valueLeOne : value ≤ 1 := le_of_not_ge oneLe
    have squareLeValue : value ^ 2 ≤ value := by
      rw [pow_two]
      calc
        value * value ≤ 1 * value :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            valueLeOne valueNonnegative
        _ = value := by ring1
    exact (min_le_right _ _).trans (lowerLtSquare.le.trans squareLeValue)

/-- Exact finite pole/apart classification of the denominator relation on a
retained child.  The apart branch carries a uniform rational denominator
lower bound; the pole branch carries only its explicit factorization and
does not assert a factor zero. -/
inductive DenominatorClassification
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (requestEntry : CompleteRequestLeaf leaf epsilon)
    (denominator : ProfileDenominatorRelation analysis) where
  | pole
      (cofactor : CCL.CoordinateFactorization.Polynomial)
      (factorization : CCL.CoordinateFactorization.Factorization
        (CCL.CurveBoxConditions.denominatorNormSq
          chart.parameterization.curve)
        analysis.profile.factor.polynomial cofactor)
      (relationEq : denominator.relation =
        CCL.CoordinateFactorization.ConditionRelation.equality
          cofactor factorization)
  | apart
      (certificate : RFAP.PathClearance.CoprimeCertificate
        analysis.profile.factor.polynomial
          (CCL.CurveBoxConditions.denominatorNormSq
            chart.parameterization.curve))
      (relationEq : denominator.relation =
        CCL.CoordinateFactorization.ConditionRelation.apart
          certificate)
      (lower : ∀ parameter : Coordinate,
        requestEntry.cell.interval.Contains parameter →
        denominator.apartLower certificate ≤
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (chart.parameterization.curve.denominatorAt parameter))

/-- Execute the profile's finite pole/apart denominator split and attach the
uniform lower bound in the apart branch. -/
def classifyDenominator
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (requestEntry : CompleteRequestLeaf leaf epsilon)
    (denominator : ProfileDenominatorRelation analysis)
    (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤
      CCL.PersistentCCLConditionProfiles.profileSignWidth
        analysis) :
    DenominatorClassification requestEntry denominator := by
  match relationEq : denominator.relation with
  | .equality cofactor factorization =>
      exact .pole cofactor factorization relationEq
  | .apart certificate =>
      exact .apart certificate relationEq (by
        intro parameter inside
        exact requestEntry.denominatorNormSq_lower_of_apart denominator
          certificate relationEq positive epsilonLe parameter inside)

end CompleteRequestLeaf

/-! ## Uniform quantitative widths for equality-owned profile conditions -/

/-- Width assigned to one profile relation when controlling approximate box
conditions.  Equality relations use their retained cofactor bound; apart
relations already have a stable strict sign and need no additional shrink. -/
def relationConditionRequestWidth
    (analysis : ProfileAnalysis factorAnalysis)
    (relation :
      CCL.PersistentCCLConditionProfiles.ProfileRelation analysis)
    (target : Coordinate) : Coordinate :=
  match relation.2 with
  | .equality cofactor _factorization =>
      CompleteRequestLeaf.equalityConditionWidth analysis cofactor target
  | .apart _apart => 1

theorem relationConditionRequestWidth_pos
    (analysis : ProfileAnalysis factorAnalysis)
    (relation :
      CCL.PersistentCCLConditionProfiles.ProfileRelation analysis)
    {target : Coordinate} (targetPositive : 0 < target) :
    0 < relationConditionRequestWidth analysis relation target := by
  rcases relation with ⟨condition, relation⟩
  cases relation with
  | equality cofactor factorization =>
      exact CompleteRequestLeaf.equalityConditionWidth_pos analysis cofactor
        targetPositive
  | apart apart =>
      exact (show (0 : Coordinate) < 1 by decide)

/-- Finite list of the quantitative condition widths for one exact profile. -/
def profileConditionRequestWidths
    (analysis : ProfileAnalysis factorAnalysis)
    (target : Coordinate) : List Coordinate :=
  analysis.profile.relations.map fun relation =>
    relationConditionRequestWidth analysis relation target

theorem relationConditionRequestWidth_mem
    (analysis : ProfileAnalysis factorAnalysis)
    (target : Coordinate)
    (relation :
      CCL.PersistentCCLConditionProfiles.ProfileRelation analysis)
    (member : relation ∈ analysis.profile.relations) :
    relationConditionRequestWidth analysis relation target ∈
      profileConditionRequestWidths analysis target :=
  QuotientFreeList.mem_map.mpr ⟨relation, member, rfl⟩

theorem profileConditionRequestWidths_positive
    (analysis : ProfileAnalysis factorAnalysis)
    {target : Coordinate} (targetPositive : 0 < target) :
    ∀ width ∈ profileConditionRequestWidths analysis target, 0 < width := by
  intro width member
  rw [profileConditionRequestWidths, QuotientFreeList.mem_map] at member
  rcases member with ⟨relation, _relationMember, rfl⟩
  exact relationConditionRequestWidth_pos analysis relation targetPositive

/-- One positive rational width below every equality-cofactor condition width
in a profile.  An empty relation list retains the harmless value `1`. -/
def profileConditionRequestWidth
    (analysis : ProfileAnalysis factorAnalysis)
    (target : Coordinate) : Coordinate :=
  CCL.PersistentCCLRegionOwnership.finitePositiveMinimum
    (profileConditionRequestWidths analysis target)

theorem profileConditionRequestWidth_pos
    (analysis : ProfileAnalysis factorAnalysis)
    {target : Coordinate} (targetPositive : 0 < target) :
    0 < profileConditionRequestWidth analysis target :=
  CCL.PersistentCCLRegionOwnership.finitePositiveMinimum_pos _
    (profileConditionRequestWidths_positive analysis targetPositive)

theorem profileConditionRequestWidth_le_relation
    (analysis : ProfileAnalysis factorAnalysis)
    (target : Coordinate)
    (relation :
      CCL.PersistentCCLConditionProfiles.ProfileRelation analysis)
    (member : relation ∈ analysis.profile.relations) :
    profileConditionRequestWidth analysis target ≤
      relationConditionRequestWidth analysis relation target :=
  CCL.PersistentCCLRegionOwnership.finitePositiveMinimum_le_of_mem
    (relationConditionRequestWidth_mem analysis target relation member)

namespace CompleteRequestLeaf

/-- Quantitative negative-cap bound for one equality-owned relation on the
common condition-controlled descendant. -/
theorem request_equality_condition_eval_gt_neg_cap
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon)
    (condition cofactor :
      CCL.CoordinateFactorization.Polynomial)
    (factorization : CCL.CoordinateFactorization.Factorization
      condition analysis.profile.factor.polynomial cofactor)
    (member :
      (⟨condition,
        CCL.CoordinateFactorization.ConditionRelation.equality
          cofactor factorization⟩ :
        CCL.PersistentCCLConditionProfiles.ProfileRelation
          analysis) ∈ analysis.profile.relations)
    {cap : Coordinate} (capPositive : 0 < cap)
    (parameter : Coordinate)
    (inside : (entry.request
      (profileConditionRequestWidth analysis (cap ^ 2))).cell.interval.Contains
        parameter) :
    -cap < condition.eval parameter := by
  let target := profileConditionRequestWidth analysis (cap ^ 2)
  have capSquarePositive : 0 < cap ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct capPositive 2
  have targetPositive : 0 < target := by
    simpa only [target] using
      profileConditionRequestWidth_pos analysis capSquarePositive
  have targetLe : target ≤
      equalityConditionWidth analysis cofactor (cap ^ 2) := by
    have relationLe := profileConditionRequestWidth_le_relation analysis
      (cap ^ 2)
      (⟨condition,
        CCL.CoordinateFactorization.ConditionRelation.equality
          cofactor factorization⟩ :
        CCL.PersistentCCLConditionProfiles.ProfileRelation
          analysis)
      member
    simpa only [target, relationConditionRequestWidth] using relationLe
  have squareSmall := entry.request_equality_condition_eval_sq_lt
    targetPositive condition cofactor factorization targetLe
      capSquarePositive parameter (by simpa only [target] using inside)
  have negSquareSmall : (-condition.eval parameter) ^ 2 < cap ^ 2 := by
    simpa only [neg_sq] using squareSmall
  have negEvalLtCap :=
    RFAP.CauchyResolution.lt_of_sq_lt_sq_of_nonneg
      capPositive.le negSquareSmall
  simpa only [neg_neg] using
    RFAP.ConstructiveFraction.neg_lt_neg_direct negEvalLtCap

/-- Negative-cap bound for one apart relation from its retained stable
nonnegative sign. -/
theorem request_apart_condition_eval_gt_neg_cap
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon)
    (condition : CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (nonnegative : ConditionNonnegative entry
      (⟨condition,
        CCL.CoordinateFactorization.ConditionRelation.apart apart⟩ :
        CCL.PersistentCCLConditionProfiles.ProfileRelation
          analysis))
    {cap : Coordinate} (capPositive : 0 < cap)
    (parameter : Coordinate)
    (inside : (entry.request
      (profileConditionRequestWidth analysis (cap ^ 2))).cell.interval.Contains
        parameter) :
    -cap < condition.eval parameter := by
  have descendantRefines := entry.request_refines
    (profileConditionRequestWidth analysis (cap ^ 2))
  have parentInside : entry.cell.interval.Contains parameter :=
    ⟨descendantRefines.1.trans inside.1,
      inside.2.trans descendantRefines.2⟩
  exact (neg_neg_of_pos capPositive).trans_le
    (nonnegative parameter parentInside)

/-- On the deterministic descendant requested at the profile-wide condition
width, every retained relation is greater than the same negative rational
cap.  Apart relations use their stable nonnegative sign; equality relations
use their explicit cofactor residual bound. -/
theorem request_condition_eval_gt_neg_cap
    {leaf : ProfileEventLeaf analysis} {epsilon : Coordinate}
    (entry : CompleteRequestLeaf leaf epsilon)
    (allNonnegative : ∀ relation ∈ analysis.profile.relations,
      ConditionNonnegative entry relation)
    (relation :
      CCL.PersistentCCLConditionProfiles.ProfileRelation analysis)
    (member : relation ∈ analysis.profile.relations)
    {cap : Coordinate} (capPositive : 0 < cap)
    (parameter : Coordinate)
    (inside : (entry.request
      (profileConditionRequestWidth analysis (cap ^ 2))).cell.interval.Contains
        parameter) :
    -cap < relation.1.eval parameter := by
  rcases relation with ⟨condition, relation⟩
  cases relation with
  | equality cofactor factorization =>
      exact entry.request_equality_condition_eval_gt_neg_cap condition
        cofactor factorization member capPositive parameter inside
  | apart apart =>
      exact entry.request_apart_condition_eval_gt_neg_cap condition apart
        (allNonnegative
          (⟨condition,
            CCL.CoordinateFactorization.ConditionRelation.apart
              apart⟩ :
            CCL.PersistentCCLConditionProfiles.ProfileRelation
              analysis)
          member)
        capPositive parameter inside

end CompleteRequestLeaf

/-- Every supplied displayed rational profile zero is retained as a nonzero
child of the complete requested subdivision. -/
theorem completeRequestCell_countNonzero_of_zero
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate)
    (cell : Cell)
    (member : cell ∈ (completeRequestSubdivision leaf epsilon).leaves)
    (parameter : Coordinate) (inside : cell.interval.Contains parameter)
    (zero : analysis.profile.factor.polynomial.eval parameter = 0) :
    RFAP.SturmRootCount.sturmRootCount2
      analysis.profile.factor.polynomial cell.interval.lower
        cell.interval.upper ≠ 0 := by
  have childLeaf := completeRequestCell_refines_leaf leaf epsilon member
  have childWidth : cell.interval.width ≤ leaf.cell.interval.width :=
    RFAP.ConstructiveFraction.sub_le_sub_direct childLeaf.2 childLeaf.1
  have leafWidthSmall : leaf.cell.interval.width <
      CCL.CurveBoxEventPartition.squarefreeLeafWidth
        analysis.profile.factor.polynomial analysis.profile.factor.squarefree
          chart.parameterization.curve box chart.cell := by
    simpa only [leaf.classification_cell] using
      leaf.classification.widthSmall
  have orientationWidth : cell.interval.width <
      CCL.CoordinateTaylor.rootOrientationWidth
        analysis.profile.factor.polynomial
          analysis.profile.factor.squarefree chart.cell.interval :=
    childWidth.trans_lt
      (leafWidthSmall.trans_le
        (CCL.CurveBoxEventPartition.squarefreeLeafWidth_le_orientation
          analysis.profile.factor.polynomial
            analysis.profile.factor.squarefree
              chart.parameterization.curve box chart.cell))
  exact CCL.CoordinateTaylor.sturmRootCount2_ne_zero_of_root
    analysis.profile.factor.polynomial analysis.profile.factor.squarefree
      (completeRequestCell_refines_chart leaf epsilon member) cell.proper
      orientationWidth (completeRequestResolution leaf epsilon cell member)
      parameter inside zero

/-- A supplied displayed rational profile zero, located in one retained
member of the complete requested family. -/
structure LocatedCompleteRequestZero
    (leaf : ProfileEventLeaf analysis) (epsilon parameter : Coordinate) where
  entry : CompleteRequestLeaf leaf epsilon
  member : entry ∈ completeRequestFamily leaf epsilon
  contains : entry.cell.interval.Contains parameter
  zero : analysis.profile.factor.polynomial.eval parameter = 0

/-- Execute the complete-tree locator and retain the child's directly proved
nonzero count.  This direction starts from a supplied rational zero. -/
def locateCompleteRequestZero
    (leaf : ProfileEventLeaf analysis) (epsilon parameter : Coordinate)
    (inside : leaf.cell.interval.Contains parameter)
    (zero : analysis.profile.factor.polynomial.eval parameter = 0) :
    LocatedCompleteRequestZero leaf epsilon parameter := by
  let found :=
    CCL.CurveBoxEventPartition.Subdivision.locateBuild
      analysis.profile.factor.polynomial analysis.profile.factor.nonzero
        chart.parameterization.curve box (completeRequestDepth leaf epsilon)
          leaf.cell parameter inside
  have countNonzero := completeRequestCell_countNonzero_of_zero leaf epsilon
    found.leaf found.member parameter found.contains zero
  let entry : CompleteRequestLeaf leaf epsilon :=
    { cell := found.leaf
      member := found.member
      countNonzero := countNonzero }
  exact
    { entry := entry
      member := mem_completeRequestFamily entry
      contains := found.contains
      zero := zero }

end Profile

/-! ## Complete requested families through a dispatched boundary -/

section Boundary

variable {p : GaussianPolynomial} {reference : Mat2} {current : Box}
variable {denominatorMargin : Coordinate}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : CCL.CCLFormula.Atom}

/-- One nonzero child in the full requested refinement of one attached
condition-profile boundary event. -/
structure BoundaryCompleteRequestEntry
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (epsilon : Coordinate) where
  parent : BoundaryProfileEventEntry boundary
  parentMember : parent ∈
    CCL.PersistentCCLProfileBoundaryEvents.boundaryProfileEventFamily
      boundary
  child : CompleteRequestLeaf parent.event.2 epsilon
  childMember : child ∈ completeRequestFamily parent.event.2 epsilon

/-- Expand one attached boundary profile into all of its nonzero requested
children. -/
def completeRequestEntriesOfProfile
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (epsilon : Coordinate) (parent : BoundaryProfileEventEntry boundary)
    (parentMember : parent ∈
      CCL.PersistentCCLProfileBoundaryEvents.boundaryProfileEventFamily
        boundary) :
    List (BoundaryCompleteRequestEntry boundary epsilon) :=
  (completeRequestFamily parent.event.2 epsilon).attach.map fun attached =>
    { parent := parent
      parentMember := parentMember
      child := attached.1
      childMember := attached.2 }

/-- Complete finite family of all nonzero requested children across every
profile and every bounded chart of one dispatched boundary. -/
def boundaryCompleteRequestFamily
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (epsilon : Coordinate) :
    List (BoundaryCompleteRequestEntry boundary epsilon) :=
  (CCL.PersistentCCLProfileBoundaryEvents.boundaryProfileEventFamily
    boundary).attach.flatMap fun attached =>
      completeRequestEntriesOfProfile boundary epsilon attached.1 attached.2

/-- Per-profile widths satisfying sign stability, separated-region
ownership, the supplied original-polynomial residual target, a direct
homogeneous cylinder-diameter target, and every equality-owned condition
residual target.  Reusing the same positive rational target keeps the public
API small; callers may pass any finite minimum of their residual and
projective-clearance requirements. -/
def boundaryControlledRequestWidths
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate) : List Coordinate :=
  (CCL.PersistentCCLProfileBoundaryEvents.boundaryProfileEventFamily
    boundary).map fun parent =>
      min
        (CCL.PersistentCCLProfileResidual.controlledProfileRequestWidth
          parent boxes pairwise target)
        (min
          (CCL.PersistentCCLRegionSeparation.shrinkingWidth
            parent.parent.chart.uniformChordalVariationCoefficient target)
          (profileConditionRequestWidth parent.event.1 target))

theorem boundaryControlledRequestWidth_mem
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate) (parent : BoundaryProfileEventEntry boundary)
    (parentMember : parent ∈
      CCL.PersistentCCLProfileBoundaryEvents.boundaryProfileEventFamily
        boundary) :
    min
        (CCL.PersistentCCLProfileResidual.controlledProfileRequestWidth
          parent boxes pairwise target)
        (min
          (CCL.PersistentCCLRegionSeparation.shrinkingWidth
            parent.parent.chart.uniformChordalVariationCoefficient target)
          (profileConditionRequestWidth parent.event.1 target)) ∈
      boundaryControlledRequestWidths boundary boxes pairwise target :=
  QuotientFreeList.mem_map.mpr ⟨parent, parentMember, rfl⟩

theorem boundaryControlledRequestWidths_positive
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    {target : Coordinate} (targetPositive : 0 < target) :
    ∀ width ∈ boundaryControlledRequestWidths boundary boxes pairwise target,
      0 < width := by
  intro width member
  rw [boundaryControlledRequestWidths, QuotientFreeList.mem_map] at member
  rcases member with ⟨parent, _parentMember, rfl⟩
  exact lt_min
    (CCL.PersistentCCLProfileResidual.controlledProfileRequestWidth_pos
      parent boxes pairwise targetPositive)
    (lt_min
      (CCL.PersistentCCLRegionSeparation.shrinkingWidth_pos
        parent.parent.chart.uniformChordalVariationCoefficient_nonneg
        targetPositive)
      (profileConditionRequestWidth_pos parent.event.1 targetPositive))

/-- One positive rational width satisfying every profile parent
simultaneously.  All sibling children are subdivided at this same width. -/
def boundaryControlledRequestWidth
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate) : Coordinate :=
  CCL.PersistentCCLRegionOwnership.finitePositiveMinimum
    (boundaryControlledRequestWidths boundary boxes pairwise target)

theorem boundaryControlledRequestWidth_pos
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    {target : Coordinate} (targetPositive : 0 < target) :
    0 < boundaryControlledRequestWidth boundary boxes pairwise target :=
  CCL.PersistentCCLRegionOwnership.finitePositiveMinimum_pos _
    (boundaryControlledRequestWidths_positive boundary boxes pairwise
      targetPositive)

theorem boundaryControlledRequestWidth_le_parent
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate) (parent : BoundaryProfileEventEntry boundary)
    (parentMember : parent ∈
      CCL.PersistentCCLProfileBoundaryEvents.boundaryProfileEventFamily
        boundary) :
    boundaryControlledRequestWidth boundary boxes pairwise target ≤
      CCL.PersistentCCLProfileResidual.controlledProfileRequestWidth
        parent boxes pairwise target :=
  (CCL.PersistentCCLRegionOwnership.finitePositiveMinimum_le_of_mem
    (boundaryControlledRequestWidth_mem boundary boxes pairwise target parent
      parentMember)).trans (min_le_left _ _)

/-- The global width is also below the direct homogeneous-diameter width of
every displayed profile parent. -/
theorem boundaryControlledRequestWidth_le_diameter
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate) (parent : BoundaryProfileEventEntry boundary)
    (parentMember : parent ∈
      CCL.PersistentCCLProfileBoundaryEvents.boundaryProfileEventFamily
        boundary) :
    boundaryControlledRequestWidth boundary boxes pairwise target ≤
      CCL.PersistentCCLRegionSeparation.shrinkingWidth
        parent.parent.chart.uniformChordalVariationCoefficient target :=
  (CCL.PersistentCCLRegionOwnership.finitePositiveMinimum_le_of_mem
    (boundaryControlledRequestWidth_mem boundary boxes pairwise target parent
      parentMember)).trans ((min_le_right _ _).trans (min_le_left _ _))

/-- The global width is below every equality-cofactor condition width in
every displayed profile parent. -/
theorem boundaryControlledRequestWidth_le_condition
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate) (parent : BoundaryProfileEventEntry boundary)
    (parentMember : parent ∈
      CCL.PersistentCCLProfileBoundaryEvents.boundaryProfileEventFamily
        boundary)
    (relation :
      CCL.PersistentCCLConditionProfiles.ProfileRelation
        parent.event.1)
    (relationMember : relation ∈ parent.event.1.profile.relations) :
    boundaryControlledRequestWidth boundary boxes pairwise target ≤
      relationConditionRequestWidth parent.event.1 relation target :=
  (CCL.PersistentCCLRegionOwnership.finitePositiveMinimum_le_of_mem
    (boundaryControlledRequestWidth_mem boundary boxes pairwise target parent
      parentMember)).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      (profileConditionRequestWidth_le_relation parent.event.1 target relation
        relationMember)))

/-- The complete sibling-preserving boundary family at its one shared
sign-, separation-, and residual-controlled width. -/
def controlledBoundaryCompleteRequestFamily
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate) :
    List (BoundaryCompleteRequestEntry boundary
      (boundaryControlledRequestWidth boundary boxes pairwise target)) :=
  boundaryCompleteRequestFamily boundary
    (boundaryControlledRequestWidth boundary boxes pairwise target)

theorem mem_boundaryCompleteRequestFamily
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (epsilon : Coordinate) (parent : BoundaryProfileEventEntry boundary)
    (parentMember : parent ∈
      CCL.PersistentCCLProfileBoundaryEvents.boundaryProfileEventFamily
        boundary)
    (child : CompleteRequestLeaf parent.event.2 epsilon)
    (childMember : child ∈ completeRequestFamily parent.event.2 epsilon) :
    ({ parent := parent
       parentMember := parentMember
       child := child
       childMember := childMember } :
      BoundaryCompleteRequestEntry boundary epsilon) ∈
        boundaryCompleteRequestFamily boundary epsilon := by
  rw [boundaryCompleteRequestFamily, QuotientFreeList.mem_flatMap]
  refine ⟨⟨parent, parentMember⟩, QuotientFreeList.mem_attach _ _, ?_⟩
  rw [completeRequestEntriesOfProfile, QuotientFreeList.mem_map]
  exact ⟨⟨child, childMember⟩, QuotientFreeList.mem_attach _ _, rfl⟩

namespace BoundaryCompleteRequestEntry

variable {boundary : CurveBoundary p reference current denominatorMargin
  marginPositive atom}

theorem controlledWidth_le_sign
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Coordinate}
    (entry : BoundaryCompleteRequestEntry boundary
      (boundaryControlledRequestWidth boundary boxes pairwise target)) :
    boundaryControlledRequestWidth boundary boxes pairwise target ≤
      CCL.PersistentCCLConditionProfiles.profileSignWidth
        entry.parent.event.1 :=
  (boundaryControlledRequestWidth_le_parent boundary boxes pairwise target
    entry.parent entry.parentMember).trans
      (CCL.PersistentCCLProfileResidual.controlledProfileRequestWidth_le_sign
        entry.parent boxes pairwise target)

theorem controlledWidth_le_family
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Coordinate}
    (entry : BoundaryCompleteRequestEntry boundary
      (boundaryControlledRequestWidth boundary boxes pairwise target)) :
    boundaryControlledRequestWidth boundary boxes pairwise target ≤
      CCL.PersistentCCLProfileBoundaryEvents.profileFamilyRequestWidth
        entry.parent boxes pairwise :=
  (boundaryControlledRequestWidth_le_parent boundary boxes pairwise target
    entry.parent entry.parentMember).trans
      (CCL.PersistentCCLProfileResidual.controlledProfileRequestWidth_le_family
        entry.parent boxes pairwise target)

/-- Every equality-owned condition is uniformly below the shared rational
target throughout a globally controlled retained child.  The theorem is
about explicit rational parameters and does not assert a profile-factor
zero. -/
theorem equality_condition_eval_sq_lt
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Coordinate} (targetPositive : 0 < target)
    (entry : BoundaryCompleteRequestEntry boundary
      (boundaryControlledRequestWidth boundary boxes pairwise target))
    (condition cofactor :
      CCL.CoordinateFactorization.Polynomial)
    (factorization : CCL.CoordinateFactorization.Factorization
      condition entry.parent.event.1.profile.factor.polynomial cofactor)
    (relationMember :
      (⟨condition,
        CCL.CoordinateFactorization.ConditionRelation.equality
          cofactor factorization⟩ :
        CCL.PersistentCCLConditionProfiles.ProfileRelation
          entry.parent.event.1) ∈
        entry.parent.event.1.profile.relations)
    (parameter : Coordinate)
    (inside : entry.child.cell.interval.Contains parameter) :
    condition.eval parameter ^ 2 < target := by
  have globalPositive :
      0 < boundaryControlledRequestWidth boundary boxes pairwise target :=
    boundaryControlledRequestWidth_pos boundary boxes pairwise targetPositive
  have globalLeRelation :=
    boundaryControlledRequestWidth_le_condition boundary boxes pairwise target
      entry.parent entry.parentMember
      (⟨condition,
        CCL.CoordinateFactorization.ConditionRelation.equality
          cofactor factorization⟩ :
        CCL.PersistentCCLConditionProfiles.ProfileRelation
          entry.parent.event.1)
      relationMember
  have globalLeEquality :
      boundaryControlledRequestWidth boundary boxes pairwise target ≤
        CompleteRequestLeaf.equalityConditionWidth entry.parent.event.1
          cofactor target := by
    simpa only [relationConditionRequestWidth] using globalLeRelation
  exact entry.child.equality_condition_eval_sq_lt globalPositive condition
    cofactor factorization globalLeEquality targetPositive parameter inside

/-- The same global request directly bounds the homogeneous diameter of
each retained child by the caller's target, independently of affine poles. -/
theorem controlled_chordal_diameter_lt
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Coordinate} (targetPositive : 0 < target)
    (entry : BoundaryCompleteRequestEntry boundary
      (boundaryControlledRequestWidth boundary boxes pairwise target)) :
    entry.parent.parent.chart.uniformChordalVariationCoefficient *
        boundaryControlledRequestWidth boundary boxes pairwise target ^ 2 <
      target := by
  let globalWidth :=
    boundaryControlledRequestWidth boundary boxes pairwise target
  let diameterWidth :=
    CCL.PersistentCCLRegionSeparation.shrinkingWidth
      entry.parent.parent.chart.uniformChordalVariationCoefficient target
  have globalPositive : 0 < globalWidth := by
    simpa only [globalWidth] using
      boundaryControlledRequestWidth_pos boundary boxes pairwise
        targetPositive
  have globalLe : globalWidth ≤ diameterWidth := by
    simpa only [globalWidth, diameterWidth] using
      boundaryControlledRequestWidth_le_diameter boundary boxes pairwise target
        entry.parent entry.parentMember
  have squareLe : globalWidth ^ 2 ≤ diameterWidth ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct globalPositive.le globalLe 2
  have coefficientNonnegative :=
    entry.parent.parent.chart.uniformChordalVariationCoefficient_nonneg
  exact
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct squareLe
      coefficientNonnegative).trans_lt
        (by
          simpa only [diameterWidth] using
            CCL.PersistentCCLRegionSeparation.coefficient_mul_shrinkingWidth_sq_lt
              coefficientNonnegative targetPositive)

/-- Exact per-relation box classification for every sibling retained at the
one global controlled width.  Keeping this certificate available avoids
throwing away which conditions are equality-owned or uniformly apart. -/
def boxClassification
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Coordinate} (targetPositive : 0 < target)
    (entry : BoundaryCompleteRequestEntry boundary
      (boundaryControlledRequestWidth boundary boxes pairwise target)) :
    CompleteRequestLeaf.BoxClassification entry.child :=
  entry.child.classifyBox
    (boundaryControlledRequestWidth_pos boundary boxes pairwise targetPositive)
    entry.controlledWidth_le_sign

/-- Exact finite pole/apart classification for the retained profile's
homogeneous denominator relation at the global controlled width. -/
def denominatorClassification
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Coordinate} (targetPositive : 0 < target)
    (entry : BoundaryCompleteRequestEntry boundary
      (boundaryControlledRequestWidth boundary boxes pairwise target)) :
    CompleteRequestLeaf.DenominatorClassification entry.child
      (profileDenominatorRelation entry.parent.event.1) :=
  entry.child.classifyDenominator
    (profileDenominatorRelation entry.parent.event.1)
    (boundaryControlledRequestWidth_pos boundary boxes pairwise targetPositive)
    entry.controlledWidth_le_sign

/-- Exact affine classification derived from the retained per-relation box
certificate. -/
def classification
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Coordinate} (targetPositive : 0 < target)
    (entry : BoundaryCompleteRequestEntry boundary
      (boundaryControlledRequestWidth boundary boxes pairwise target)) :
    CompleteRequestLeaf.AffineClassification entry.child :=
  (entry.boxClassification targetPositive).toAffine

/-- Homogeneous chordal diameter bound for one complete requested child. -/
theorem chordalSq_le
    {epsilon : Coordinate}
    (entry : BoundaryCompleteRequestEntry boundary epsilon)
    (positive : 0 < epsilon) {left right : Coordinate}
    (leftInside : entry.child.cell.interval.Contains left)
    (rightInside : entry.child.cell.interval.Contains right) :
    CCL.Chordal.chordalSq
        (entry.parent.parent.chart.projective left)
        (entry.parent.parent.chart.projective right) ≤
      entry.parent.parent.chart.uniformChordalVariationCoefficient *
        epsilon ^ 2 :=
  entry.child.chordalSq_le positive leftInside rightInside

/-- A retained child whose homogeneous diameter is below an affine chordal
gap cannot meet both sides of that gap. -/
theorem not_spanning_with_gap
    {epsilon : Coordinate}
    (entry : BoundaryCompleteRequestEntry boundary epsilon)
    {leftBox rightBox : Box} (gap : Coordinate)
    (gapLower : ∀ {leftPoint rightPoint :
        RFAP.ConstructiveGaussian.Gaussian},
      leftBox.Contains leftPoint → rightBox.Contains rightPoint →
        gap ≤ CCL.Chordal.chordalSq
          (CCL.Proj.affine leftPoint) (CCL.Proj.affine rightPoint))
    (positive : 0 < epsilon)
    (diameterSmall :
      entry.parent.parent.chart.uniformChordalVariationCoefficient *
        epsilon ^ 2 < gap)
    {leftParameter rightParameter : Coordinate}
    (leftParameterInside :
      entry.child.cell.interval.Contains leftParameter)
    (rightParameterInside :
      entry.child.cell.interval.Contains rightParameter)
    (leftDenominatorNonzero :
      entry.parent.parent.chart.parameterization.curve.denominatorAt
        leftParameter ≠ 0)
    (rightDenominatorNonzero :
      entry.parent.parent.chart.parameterization.curve.denominatorAt
        rightParameter ≠ 0)
    (leftPointInside : leftBox.Contains
      (entry.parent.parent.chart.parameterization.curve.point leftParameter))
    (rightPointInside : rightBox.Contains
      (entry.parent.parent.chart.parameterization.curve.point
        rightParameter)) : False := by
  let curve := entry.parent.parent.chart.parameterization.curve
  let leftPoint := curve.point leftParameter
  let rightPoint := curve.point rightParameter
  have eventUpper := entry.chordalSq_le positive leftParameterInside
    rightParameterInside
  have leftTransport :
      CCL.Chordal.chordalSq
          (entry.parent.parent.chart.projective leftParameter)
          (entry.parent.parent.chart.projective rightParameter) =
        CCL.Chordal.chordalSq
          (CCL.Proj.affine leftPoint)
          (entry.parent.parent.chart.projective rightParameter) := by
    simpa only [curve, leftPoint,
      CCL.CCLBoundaryCharts.BoundedChart.projective] using
      CCL.RationalCurveBounds.chordalSq_projective_eq_affine
        curve leftParameter leftDenominatorNonzero
          (entry.parent.parent.chart.projective rightParameter)
  have rightEquivalent :
      (entry.parent.parent.chart.projective rightParameter).Equivalent
        (CCL.Proj.affine rightPoint) := by
    simpa only [curve, rightPoint,
      CCL.CCLBoundaryCharts.BoundedChart.projective] using
      CCL.RationalCurveBounds.projective_equivalent_affine
        curve rightParameter rightDenominatorNonzero
  have rightTransport :
      CCL.Chordal.chordalSq
          (CCL.Proj.affine leftPoint)
          (entry.parent.parent.chart.projective rightParameter) =
        CCL.Chordal.chordalSq
          (CCL.Proj.affine leftPoint) (CCL.Proj.affine rightPoint) :=
    CCL.Chordal.chordalSq_eq_of_equivalent_right
      (entry.parent.parent.chart.projective_valid rightParameter)
      (CCL.Chordal.Proj.affine_hasNonzeroCoordinate rightPoint)
      rightEquivalent (CCL.Proj.affine leftPoint)
  have affineUpper :
      CCL.Chordal.chordalSq
          (CCL.Proj.affine leftPoint) (CCL.Proj.affine rightPoint) ≤
        entry.parent.parent.chart.uniformChordalVariationCoefficient *
          epsilon ^ 2 := by
    rw [← rightTransport, ← leftTransport]
    exact eventUpper
  have affineLower : gap ≤
      CCL.Chordal.chordalSq
        (CCL.Proj.affine leftPoint) (CCL.Proj.affine rightPoint) :=
    gapLower leftPointInside rightPointInside
  exact (not_lt_of_ge affineLower) (affineUpper.trans_lt diameterSmall)

/-- At the global controlled width, one retained child cannot meet two
distinct members of the separated finite box family. -/
theorem controlled_not_spanning
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Coordinate} (targetPositive : 0 < target)
    (entry : BoundaryCompleteRequestEntry boundary
      (boundaryControlledRequestWidth boundary boxes pairwise target))
    (left right : Fin boxes.length) (different : left ≠ right) :
    ∀ {leftParameter rightParameter : Coordinate},
      entry.child.cell.interval.Contains leftParameter →
      entry.child.cell.interval.Contains rightParameter →
      entry.parent.parent.chart.parameterization.curve.denominatorAt
        leftParameter ≠ 0 →
      entry.parent.parent.chart.parameterization.curve.denominatorAt
        rightParameter ≠ 0 →
      (boxes.get left).Contains
        (entry.parent.parent.chart.parameterization.curve.point leftParameter) →
      (boxes.get right).Contains
        (entry.parent.parent.chart.parameterization.curve.point rightParameter) →
      False := by
  intro leftParameter rightParameter leftInside rightInside leftDenominator
    rightDenominator leftPointInside rightPointInside
  let separated :=
    CCL.PersistentCCLRegionOwnership.pairwise_get_separated
      pairwise left right different
  let pairWidth :=
    CCL.PersistentCCLProfileBoundaryEvents.separatedProfileRequestWidth
      entry.parent separated
  let globalWidth :=
    boundaryControlledRequestWidth boundary boxes pairwise target
  have globalPositive : 0 < globalWidth := by
    simpa only [globalWidth] using
      boundaryControlledRequestWidth_pos boundary boxes pairwise
        targetPositive
  have globalLePair : globalWidth ≤ pairWidth := by
    exact entry.controlledWidth_le_family.trans
      (by
        simpa only [pairWidth, separated] using
          CCL.PersistentCCLProfileBoundaryEvents.profileFamilyRequestWidth_le_pair
            entry.parent boxes pairwise left right different)
  have widthSquare : globalWidth ^ 2 ≤ pairWidth ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct globalPositive.le
      globalLePair 2
  have coefficientNonnegative :=
    entry.parent.parent.chart.uniformChordalVariationCoefficient_nonneg
  have diameterLe :
      entry.parent.parent.chart.uniformChordalVariationCoefficient *
          globalWidth ^ 2 ≤
        entry.parent.parent.chart.uniformChordalVariationCoefficient *
          pairWidth ^ 2 :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct widthSquare
      coefficientNonnegative
  have pairSmall :
      entry.parent.parent.chart.uniformChordalVariationCoefficient *
          pairWidth ^ 2 <
        CCL.PersistentCCLRegionSeparation.separatedChordalGap
          separated := by
    simpa only [pairWidth,
      CCL.PersistentCCLProfileBoundaryEvents.separatedProfileRequestWidth] using
      CCL.PersistentCCLRegionSeparation.coefficient_mul_shrinkingWidth_sq_lt
        coefficientNonnegative
        (CCL.PersistentCCLRegionSeparation.separatedChordalGap_pos
          separated)
  exact entry.not_spanning_with_gap
    (CCL.PersistentCCLRegionSeparation.separatedChordalGap
      separated)
    (CCL.PersistentCCLRegionSeparation.separatedChordalGap_le_affine
      separated)
    globalPositive (diameterLe.trans_lt pairSmall) leftInside rightInside
      leftDenominator rightDenominator leftPointInside rightPointInside

/-- The original-polynomial residual budget for every possible owner is
strictly below the caller's target at the global controlled width. -/
theorem controlled_residual_budget_lt
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Coordinate} (targetPositive : 0 < target)
    (entry : BoundaryCompleteRequestEntry boundary
      (boundaryControlledRequestWidth boundary boxes pairwise target))
    (index : Fin boxes.length) :
    CCL.PersistentCCLProfileResidual.BoundaryProfileEventEntry.affineResidualCoefficient
        entry.parent (boxes.get index) *
      boundaryControlledRequestWidth boundary boxes pairwise target ^ 2 <
        target := by
  let globalWidth :=
    boundaryControlledRequestWidth boundary boxes pairwise target
  let parentWidth :=
    CCL.PersistentCCLProfileResidual.controlledProfileRequestWidth
      entry.parent boxes pairwise target
  let coefficient :=
    CCL.PersistentCCLProfileResidual.BoundaryProfileEventEntry.affineResidualCoefficient
      entry.parent (boxes.get index)
  have globalPositive : 0 < globalWidth := by
    simpa only [globalWidth] using
      boundaryControlledRequestWidth_pos boundary boxes pairwise
        targetPositive
  have globalLeParent : globalWidth ≤ parentWidth := by
    simpa only [globalWidth, parentWidth] using
      boundaryControlledRequestWidth_le_parent boundary boxes pairwise target
        entry.parent entry.parentMember
  have squareOrder : globalWidth ^ 2 ≤ parentWidth ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct globalPositive.le
      globalLeParent 2
  have coefficientNonnegative : 0 ≤ coefficient := by
    simpa only [coefficient] using
      CCL.PersistentCCLProfileResidual.BoundaryProfileEventEntry.affineResidualCoefficient_nonneg
        entry.parent (boxes.get index)
  have scaled : coefficient * globalWidth ^ 2 ≤
      coefficient * parentWidth ^ 2 :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct squareOrder
      coefficientNonnegative
  exact scaled.trans_lt (by
    simpa only [coefficient, parentWidth] using
      CCL.PersistentCCLProfileResidual.controlledProfileResidual_lt
        entry.parent boxes pairwise targetPositive index)

/-- Every owned rational point of a complete retained child has original-
polynomial residual strictly below the supplied target. -/
theorem residual_lt_of_inside
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Coordinate} (targetPositive : 0 < target)
    (entry : BoundaryCompleteRequestEntry boundary
      (boundaryControlledRequestWidth boundary boxes pairwise target))
    (index : Fin boxes.length) (parameter : Coordinate)
    (parameterInside : entry.child.cell.interval.Contains parameter)
    (denominatorNonzero :
      entry.parent.parent.chart.parameterization.curve.denominatorAt
        parameter ≠ 0)
    (pointInside : (boxes.get index).Contains
      (entry.parent.parent.chart.parameterization.curve.point parameter)) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval
          (entry.parent.parent.chart.parameterization.curve.point parameter)) <
      target := by
  have upper := entry.child.normSq_eval_point_le_of_inside
    (boundaryControlledRequestWidth_pos boundary boxes pairwise targetPositive)
    parameter parameterInside denominatorNonzero pointInside
  exact upper.trans_lt
    (entry.controlled_residual_budget_lt targetPositive index)

end BoundaryCompleteRequestEntry

/-- A denominator-safe rational parameter computed inside one complete
retained child. -/
structure NonpoleCompleteRequestSample
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Coordinate}
    (entry : BoundaryCompleteRequestEntry boundary epsilon) where
  parameter : Coordinate
  parameterInside : entry.child.cell.interval.Contains parameter
  denominatorNonzero :
    entry.parent.parent.chart.parameterization.curve.denominatorAt
      parameter ≠ 0

/-- Bounded finite search for a non-pole rational parameter in any retained
child. -/
def nonpoleCompleteRequestSample
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Coordinate}
    (entry : BoundaryCompleteRequestEntry boundary epsilon) :
    NonpoleCompleteRequestSample entry := by
  let curve := entry.parent.parent.chart.parameterization.curve
  let interval := entry.child.cell.interval
  let denominatorPolynomial :=
    CCL.CurveBoxConditions.denominatorNormSq curve
  have chartMember :=
    CCL.PersistentCCLCurveClear.chart_mem_of_analysis_mem
      boundary entry.parent.parent.analysisMember
  have nondegenerate :=
    CCL.CCLChartNondegenerate.nondegenerate_of_mem_charts
      boundary.source current denominatorMargin marginPositive
        entry.parent.parent.chart chartMember
  have intervalProper : interval.lower < interval.upper := by
    simpa only [interval] using entry.child.cell.proper
  let parameter := RFAP.SafeCandidates.interiorSearchValue
    denominatorPolynomial denominatorPolynomial.natDegree intervalProper
      nondegenerate.denominatorNormNonzero (Nat.le_refl _)
  have specification :=
    RFAP.SafeCandidates.interiorSearchValue_spec
      denominatorPolynomial denominatorPolynomial.natDegree intervalProper
        nondegenerate.denominatorNormNonzero (Nat.le_refl _)
  exact
    { parameter := parameter
      parameterInside := ⟨specification.2.1.le, specification.2.2.le⟩
      denominatorNonzero := by
        intro denominatorZero
        apply specification.1
        change denominatorPolynomial.eval parameter = 0
        rw [show denominatorPolynomial.eval parameter =
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (curve.denominatorAt parameter) by
              exact CCL.CurveBoxConditions.eval_denominatorNormSq
                curve parameter,
          denominatorZero,
          RFAP.ConstructiveGaussian.Gaussian.normSq_zero] }

/-- A denominator-safe rational sample computed on a later deterministic
descendant of one already retained complete child. -/
structure NonpoleCompleteRequestDescendantSample
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Coordinate}
    (entry : BoundaryCompleteRequestEntry boundary epsilon)
    (target : Coordinate) where
  parameter : Coordinate
  parameterInside :
    (entry.child.request target).cell.interval.Contains parameter
  denominatorNonzero :
    entry.parent.parent.chart.parameterization.curve.denominatorAt
      parameter ≠ 0

/-- Bounded finite non-pole search on the selected descendant branch. -/
def nonpoleCompleteRequestDescendantSample
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Coordinate}
    (entry : BoundaryCompleteRequestEntry boundary epsilon)
    (target : Coordinate) :
    NonpoleCompleteRequestDescendantSample entry target := by
  let curve := entry.parent.parent.chart.parameterization.curve
  let interval := (entry.child.request target).cell.interval
  let denominatorPolynomial :=
    CCL.CurveBoxConditions.denominatorNormSq curve
  have chartMember :=
    CCL.PersistentCCLCurveClear.chart_mem_of_analysis_mem
      boundary entry.parent.parent.analysisMember
  have nondegenerate :=
    CCL.CCLChartNondegenerate.nondegenerate_of_mem_charts
      boundary.source current denominatorMargin marginPositive
        entry.parent.parent.chart chartMember
  have intervalProper : interval.lower < interval.upper := by
    simpa only [interval] using (entry.child.request target).cell.proper
  let parameter := RFAP.SafeCandidates.interiorSearchValue
    denominatorPolynomial denominatorPolynomial.natDegree intervalProper
      nondegenerate.denominatorNormNonzero (Nat.le_refl _)
  have specification :=
    RFAP.SafeCandidates.interiorSearchValue_spec
      denominatorPolynomial denominatorPolynomial.natDegree intervalProper
        nondegenerate.denominatorNormNonzero (Nat.le_refl _)
  exact
    { parameter := parameter
      parameterInside := ⟨specification.2.1.le, specification.2.2.le⟩
      denominatorNonzero := by
        intro denominatorZero
        apply specification.1
        change denominatorPolynomial.eval parameter = 0
        rw [show denominatorPolynomial.eval parameter =
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (curve.denominatorAt parameter) by
              exact CCL.CurveBoxConditions.eval_denominatorNormSq
                curve parameter,
          denominatorZero,
          RFAP.ConstructiveGaussian.Gaussian.normSq_zero] }

/-- Deterministic descendant width making every equality-owned box condition
smaller than the square of the denominator-lower-bound-scaled radius. -/
def nearBoxDescendantRequestWidth
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Coordinate}
    (entry : BoundaryCompleteRequestEntry boundary epsilon)
    (denominator : ProfileDenominatorRelation entry.parent.event.1)
    (apart : RFAP.PathClearance.CoprimeCertificate
      entry.parent.event.1.profile.factor.polynomial
        (CCL.CurveBoxConditions.denominatorNormSq
          entry.parent.parent.chart.parameterization.curve))
    (radius : Coordinate) : Coordinate :=
  profileConditionRequestWidth entry.parent.event.1
    ((denominator.apartLower apart * radius) ^ 2)

theorem nearBoxDescendantRequestWidth_pos
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Coordinate}
    (entry : BoundaryCompleteRequestEntry boundary epsilon)
    (denominator : ProfileDenominatorRelation entry.parent.event.1)
    (apart : RFAP.PathClearance.CoprimeCertificate
      entry.parent.event.1.profile.factor.polynomial
        (CCL.CurveBoxConditions.denominatorNormSq
          entry.parent.parent.chart.parameterization.curve))
    {radius : Coordinate} (radiusPositive : 0 < radius) :
    0 < nearBoxDescendantRequestWidth entry denominator apart radius := by
  apply profileConditionRequestWidth_pos
  exact RFAP.ConstructiveFraction.pow_pos_direct
    (RFAP.ConstructiveFraction.mul_pos_direct
      (denominator.apartLower_pos apart)
      radiusPositive) 2

/-- Bounded non-pole sample on the condition-controlled descendant. -/
def nearBoxDescendantSample
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Coordinate}
    (entry : BoundaryCompleteRequestEntry boundary epsilon)
    (denominator : ProfileDenominatorRelation entry.parent.event.1)
    (apart : RFAP.PathClearance.CoprimeCertificate
      entry.parent.event.1.profile.factor.polynomial
        (CCL.CurveBoxConditions.denominatorNormSq
          entry.parent.parent.chart.parameterization.curve))
    (radius : Coordinate) :
    NonpoleCompleteRequestDescendantSample entry
      (nearBoxDescendantRequestWidth entry denominator apart radius) :=
  nonpoleCompleteRequestDescendantSample entry
    (nearBoxDescendantRequestWidth entry denominator apart radius)

/-- If the retained inside-profile classification has an apart denominator,
its computed descendant sample lies within the supplied rational coordinate
radius of the profiled box.  The sample is produced by bounded search; no
profile zero or completed root is asserted. -/
theorem nearBoxDescendantSample_within_radius
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Coordinate}
    (entry : BoundaryCompleteRequestEntry boundary epsilon)
    (denominator : ProfileDenominatorRelation entry.parent.event.1)
    (apart : RFAP.PathClearance.CoprimeCertificate
      entry.parent.event.1.profile.factor.polynomial
        (CCL.CurveBoxConditions.denominatorNormSq
          entry.parent.parent.chart.parameterization.curve))
    (denominatorLower : ∀ parameter : Coordinate,
      entry.child.cell.interval.Contains parameter →
      denominator.apartLower apart ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (entry.parent.parent.chart.parameterization.curve.denominatorAt
            parameter))
    (allNonnegative : ∀ relation ∈
      entry.parent.event.1.profile.relations,
      CompleteRequestLeaf.ConditionNonnegative entry.child relation)
    {radius : Coordinate} (radiusPositive : 0 < radius) :
    let sample := nearBoxDescendantSample entry denominator apart radius
    current.xLower - radius <
        (entry.parent.parent.chart.parameterization.curve.point
          sample.parameter).re ∧
      (entry.parent.parent.chart.parameterization.curve.point
        sample.parameter).re < current.xUpper + radius ∧
      current.yLower - radius <
        (entry.parent.parent.chart.parameterization.curve.point
          sample.parameter).im ∧
      (entry.parent.parent.chart.parameterization.curve.point
        sample.parameter).im < current.yUpper + radius := by
  let lower := denominator.apartLower apart
  let cap := lower * radius
  let target := profileConditionRequestWidth entry.parent.event.1 (cap ^ 2)
  let sample := nearBoxDescendantSample entry denominator apart radius
  have capPositive : 0 < cap := by
    exact RFAP.ConstructiveFraction.mul_pos_direct
      (denominator.apartLower_pos apart) radiusPositive
  have sampleInside :
      (entry.child.request target).cell.interval.Contains sample.parameter := by
    simpa only [sample, target, cap, nearBoxDescendantSample,
      nearBoxDescendantRequestWidth] using sample.parameterInside
  have descendantRefines := entry.child.request_refines target
  have sampleInsideParent :
      entry.child.cell.interval.Contains sample.parameter :=
    ⟨descendantRefines.1.trans sampleInside.1,
      sampleInside.2.trans descendantRefines.2⟩
  have lowerLeDenominator : lower ≤
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (entry.parent.parent.chart.parameterization.curve.denominatorAt
          sample.parameter) := by
    simpa only [lower] using denominatorLower sample.parameter sampleInsideParent
  let conditionLowerPredicate := fun condition :
      CCL.CoordinateFactorization.Polynomial =>
    -cap < condition.eval sample.parameter
  have relationsLower : entry.parent.event.1.profile.relations.Forall
      (conditionLowerPredicate ∘ Sigma.fst) :=
    List.forall_iff_forall_mem.mpr (by
      intro relation relationMember
      exact entry.child.request_condition_eval_gt_neg_cap allNonnegative
        relation relationMember capPositive sample.parameter (by
          simpa only [target, cap] using sampleInside))
  have mappedLower :
      (entry.parent.event.1.profile.relations.map Sigma.fst).Forall
        conditionLowerPredicate := by
    have alignment :
        entry.parent.event.1.profile.relations.Forall
            (conditionLowerPredicate ∘ Sigma.fst) ↔
          (entry.parent.event.1.profile.relations.map Sigma.fst).Forall
            conditionLowerPredicate :=
      (List.forall_map_iff
        (l := entry.parent.event.1.profile.relations)
        (p := conditionLowerPredicate) Sigma.fst).symm
    exact alignment.mp relationsLower
  rw [entry.parent.event.1.profile.conditions_eq] at mappedLower
  have boxConditionsLower :
      (CCL.CurveBoxConditions.conditionPolynomials
        entry.parent.parent.chart.parameterization.curve current).Forall
          conditionLowerPredicate := by
    simpa only [CCL.CurveBoxConditions.profiledConditionPolynomials,
      List.forall_cons] using mappedLower.2
  simp only [CCL.CurveBoxConditions.conditionPolynomials,
    List.forall_cons] at boxConditionsLower
  apply CCL.CurveBoxConditions.point_within_radius_of_condition_lower
    entry.parent.parent.chart.parameterization.curve current sample.parameter
      radius lower radiusPositive.le sample.denominatorNonzero
        lowerLeDenominator
  · exact boxConditionsLower.1
  · exact boxConditionsLower.2.1
  · exact boxConditionsLower.2.2.1
  · exact boxConditionsLower.2.2.2.1

/-- Original-polynomial residual of a descendant sample once its displayed
affine point is supplied inside a target box. -/
theorem NonpoleCompleteRequestDescendantSample.normSq_eval_point_le_of_inside
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Coordinate}
    {entry : BoundaryCompleteRequestEntry boundary epsilon}
    {target : Coordinate} (targetPositive : 0 < target)
    (sample : NonpoleCompleteRequestDescendantSample entry target)
    (targetBox : Box)
    (pointInside : targetBox.Contains
      (entry.parent.parent.chart.parameterization.curve.point
        sample.parameter)) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval
          (entry.parent.parent.chart.parameterization.curve.point
            sample.parameter)) ≤
      CCL.PersistentCCLProfileResidual.affineProfileResidualCoefficient
          (targetBox := targetBox) entry.parent.event.1 * target ^ 2 :=
  entry.child.request_normSq_eval_point_le_of_inside target targetPositive
    sample.parameter sample.parameterInside sample.denominatorNonzero
      pointInside

/-- Positive deterministic descendant width making the original-polynomial
residual smaller than a supplied target whenever the sample lies in
`targetBox`. -/
def descendantResidualRequestWidth
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Coordinate}
    (entry : BoundaryCompleteRequestEntry boundary epsilon)
    (targetBox : Box) (residualTarget : Coordinate) : Coordinate :=
  CCL.PersistentCCLRegionSeparation.shrinkingWidth
    (CCL.PersistentCCLProfileResidual.affineProfileResidualCoefficient
      (targetBox := targetBox) entry.parent.event.1)
    residualTarget

theorem descendantResidualRequestWidth_pos
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Coordinate}
    (entry : BoundaryCompleteRequestEntry boundary epsilon)
    (targetBox : Box) {residualTarget : Coordinate}
    (targetPositive : 0 < residualTarget) :
    0 < descendantResidualRequestWidth entry targetBox residualTarget :=
  CCL.PersistentCCLRegionSeparation.shrinkingWidth_pos
    (CCL.PersistentCCLProfileResidual.affineProfileResidualCoefficient_nonneg
      (targetBox := targetBox) entry.parent.event.1)
    targetPositive

/-- The bounded non-pole sample at the computed descendant width meets the
requested original-polynomial residual target whenever its affine point is
inside the displayed target box. -/
theorem descendant_sample_residual_lt
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Coordinate}
    (entry : BoundaryCompleteRequestEntry boundary epsilon)
    (targetBox : Box) {residualTarget : Coordinate}
    (targetPositive : 0 < residualTarget)
    (sample : NonpoleCompleteRequestDescendantSample entry
      (descendantResidualRequestWidth entry targetBox residualTarget))
    (pointInside : targetBox.Contains
      (entry.parent.parent.chart.parameterization.curve.point
        sample.parameter)) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval
          (entry.parent.parent.chart.parameterization.curve.point
            sample.parameter)) < residualTarget := by
  have upper := sample.normSq_eval_point_le_of_inside
    (descendantResidualRequestWidth_pos entry targetBox targetPositive)
    targetBox pointInside
  exact upper.trans_lt
    (CCL.PersistentCCLRegionSeparation.coefficient_mul_shrinkingWidth_sq_lt
      (CCL.PersistentCCLProfileResidual.affineProfileResidualCoefficient_nonneg
        (targetBox := targetBox) entry.parent.event.1)
      targetPositive)

/-- An explicit owner meeting for one complete child at the global
controlled width. -/
structure ControlledCompleteRequestMeeting
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate)
    (entry : BoundaryCompleteRequestEntry boundary
      (boundaryControlledRequestWidth boundary boxes pairwise target)) where
  index : Fin boxes.length
  parameter : Coordinate
  parameterInside : entry.child.cell.interval.Contains parameter
  denominatorNonzero :
    entry.parent.parent.chart.parameterization.curve.denominatorAt
      parameter ≠ 0
  pointInside : (boxes.get index).Contains
    (entry.parent.parent.chart.parameterization.curve.point parameter)

namespace ControlledCompleteRequestMeeting

variable {boundary : CurveBoundary p reference current denominatorMargin
  marginPositive atom}
variable {boxes : List Box}
variable {pairwise : boxes.Pairwise fun left right => left.Separated right}
variable {target : Coordinate}
variable {entry : BoundaryCompleteRequestEntry boundary
  (boundaryControlledRequestWidth boundary boxes pairwise target)}

/-- Any two displayed rational owner meetings of the same retained child
have the same finite box index. -/
theorem index_unique (targetPositive : 0 < target)
    (left right : ControlledCompleteRequestMeeting boxes pairwise target
      entry) : left.index = right.index := by
  by_cases same : left.index = right.index
  · exact same
  · exact (entry.controlled_not_spanning targetPositive left.index
      right.index same left.parameterInside right.parameterInside
      left.denominatorNonzero right.denominatorNonzero left.pointInside
      right.pointInside).elim

/-- Every explicit owner meeting has original-polynomial residual below the
global target. -/
theorem residual_lt (targetPositive : 0 < target)
    (meeting : ControlledCompleteRequestMeeting boxes pairwise target
      entry) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval (entry.parent.parent.chart.parameterization.curve.point
          meeting.parameter)) < target :=
  entry.residual_lt_of_inside targetPositive meeting.index meeting.parameter
    meeting.parameterInside meeting.denominatorNonzero meeting.pointInside

/-- Below the squarefree derivative threshold, every owned complete-child
sample has a nonzero derivative. -/
theorem derivative_ne_zero
    {ambient : Box}
    (squarefree : RFAP.LocalExtraction.SquarefreeCertificate p)
    (boxesRefine : ∀ index : Fin boxes.length,
      (boxes.get index).Refines ambient)
    (targetPositive : 0 < target)
    (targetLe : target ≤
      RFAP.LocalExtraction.derivativeThreshold squarefree ambient)
    (meeting : ControlledCompleteRequestMeeting boxes pairwise
      target entry) :
    (RFAP.ConstructiveGCD.derivative p).eval
        (entry.parent.parent.chart.parameterization.curve.point
          meeting.parameter) ≠ 0 := by
  let point := entry.parent.parent.chart.parameterization.curve.point
    meeting.parameter
  have pointInsideAmbient : ambient.Contains point :=
    (boxesRefine meeting.index).contains meeting.pointInside
  have residualSmall : RFAP.ConstructiveGaussian.Gaussian.normSq
      (p.eval point) ≤
      RFAP.LocalExtraction.derivativeThreshold squarefree ambient :=
    (meeting.residual_lt targetPositive).le.trans targetLe
  exact RFAP.LocalExtraction.derivative_ne_zero_of_small_residual
    squarefree ambient pointInsideAmbient residualSmall

end ControlledCompleteRequestMeeting

/-- Total finite owner/outside classification of one non-pole sample from a
complete retained child. -/
inductive CompleteRequestSampleClassification
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate)
    (entry : BoundaryCompleteRequestEntry boundary
      (boundaryControlledRequestWidth boundary boxes pairwise target))
    (sample : NonpoleCompleteRequestSample entry) where
  | meeting
      (owner : ControlledCompleteRequestMeeting boxes pairwise target entry)
  | outside (proof : ∀ index : Fin boxes.length,
      ¬(boxes.get index).Contains
        (entry.parent.parent.chart.parameterization.curve.point
          sample.parameter))

/-- Execute every finite box-membership comparison for one complete-child
sample. -/
def classifyCompleteRequestSample
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate)
    (entry : BoundaryCompleteRequestEntry boundary
      (boundaryControlledRequestWidth boundary boxes pairwise target))
    (sample : NonpoleCompleteRequestSample entry) :
    CompleteRequestSampleClassification boxes pairwise target entry sample := by
  let point := entry.parent.parent.chart.parameterization.curve.point
    sample.parameter
  match found :
      CCL.PersistentCCLRegionOwnership.findContainingBoxIndex
        boxes point with
  | some index =>
      exact .meeting
        { index := index
          parameter := sample.parameter
          parameterInside := sample.parameterInside
          denominatorNonzero := sample.denominatorNonzero
          pointInside :=
            CCL.PersistentCCLRegionOwnership.findContainingBoxIndex_sound
              boxes point index found }
  | none =>
      exact .outside
        (CCL.PersistentCCLRegionOwnership.findContainingBoxIndex_none
          boxes point found)

/-- All executable data attached to one member of the globally controlled
complete boundary family. -/
structure ClassifiedControlledBoundaryChild
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate) (targetPositive : 0 < target) where
  entry : BoundaryCompleteRequestEntry boundary
    (boundaryControlledRequestWidth boundary boxes pairwise target)
  member : entry ∈
    controlledBoundaryCompleteRequestFamily boundary boxes pairwise target
  boxClassification : CompleteRequestLeaf.BoxClassification entry.child
  denominatorClassification :
    CompleteRequestLeaf.DenominatorClassification entry.child
      (profileDenominatorRelation entry.parent.event.1)
  sample : NonpoleCompleteRequestSample entry
  sampleClassification : CompleteRequestSampleClassification boxes pairwise
    target entry sample

namespace ClassifiedControlledBoundaryChild

/-- Affine semantics derived from the retained exact per-relation
classification. -/
def affineClassification
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Coordinate} {targetPositive : 0 < target}
    (child : ClassifiedControlledBoundaryChild boundary boxes pairwise target
      targetPositive) :
    CompleteRequestLeaf.AffineClassification child.entry.child :=
  child.boxClassification.toAffine

end ClassifiedControlledBoundaryChild

/-- Compute exact affine and sample-owner classifications for every retained
child in the complete boundary family. -/
def classifiedControlledBoundaryFamily
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate) (targetPositive : 0 < target) :
    List (ClassifiedControlledBoundaryChild boundary boxes pairwise target
      targetPositive) :=
  (controlledBoundaryCompleteRequestFamily boundary boxes pairwise target).attach.map
    fun attached =>
      let sample := nonpoleCompleteRequestSample attached.1
      { entry := attached.1
        member := attached.2
        boxClassification := attached.1.boxClassification targetPositive
        denominatorClassification :=
          attached.1.denominatorClassification targetPositive
        sample := sample
        sampleClassification :=
          classifyCompleteRequestSample boxes pairwise target attached.1
            sample }

/-- A supplied displayed rational boundary root located in the full requested
multi-chart/profile/child family. -/
structure LocatedBoundaryCompleteRequestZero
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (epsilon : Coordinate)
    (value : RFAP.ConstructiveGaussian.Gaussian) where
  entry : BoundaryCompleteRequestEntry boundary epsilon
  member : entry ∈ boundaryCompleteRequestFamily boundary epsilon
  parameter : Coordinate
  parameterInside : entry.child.cell.interval.Contains parameter
  profileZero :
    entry.parent.event.1.profile.factor.polynomial.eval parameter = 0
  denominatorNonzero :
    entry.parent.parent.chart.parameterization.curve.denominatorAt
      parameter ≠ 0
  point_eq :
    entry.parent.parent.chart.parameterization.curve.point parameter = value

/-- Safe pointwise completeness after full requested subdivision: start from
one supplied Gaussian-rational polynomial root and locate its retained child.
No nonzero child count is used to manufacture a root. -/
def locateBoundaryCompleteRequestZero
    (degreePositive : 0 < p.natDegree)
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (epsilon : Coordinate)
    (value : RFAP.ConstructiveGaussian.Gaussian)
    (inside : current.Contains value)
    (onBoundary : atom.form.eval value = 0)
    (root : p.eval value = 0)
    (denominatorLower : denominatorMargin ≤
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.RawParser.denominator reference value)) :
    LocatedBoundaryCompleteRequestZero boundary epsilon value := by
  let located :=
    CCL.PersistentCCLProfileBoundaryEvents.locateBoundaryProfileRoot
      degreePositive boundary value inside onBoundary root denominatorLower
  let childLocated := locateCompleteRequestZero located.entry.event.2 epsilon
    located.parameter located.parameterInside located.profileZero
  let entry : BoundaryCompleteRequestEntry boundary epsilon :=
    { parent := located.entry
      parentMember := located.member
      child := childLocated.entry
      childMember := childLocated.member }
  exact
    { entry := entry
      member := mem_boundaryCompleteRequestFamily boundary epsilon
        located.entry located.member childLocated.entry childLocated.member
      parameter := located.parameter
      parameterInside := childLocated.contains
      profileZero := located.profileZero
      denominatorNonzero := located.denominatorNonzero
      point_eq := located.point_eq }

end Boundary

end CCL.PersistentCCLProfileRequestFamily
