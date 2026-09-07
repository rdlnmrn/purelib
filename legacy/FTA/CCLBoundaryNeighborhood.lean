import FTA.CCLCoupledController

/-!
# Quantitative neighbourhood exclusion for completed CCL boundaries

The ordinary clear-arc refinement and the terminal-guard refinement each
store a rational sampling tolerance.  This module combines them downstream,
without enlarging either foundational clearance module, and proves that no
rational point of any parser-planned boundary lies within the minimum of the
two tolerances of the final guarded winding box.
-/

namespace FTA
namespace CCLBoundaryNeighborhood

open CCL CCL.GaussianRat
open FTA.CCLBranchController
open FTA.CCLBranchCells
open FTA.CCLBranchEvidence
open FTA.CCLBranchPartition
open FTA.CCLClearanceExclusion
open FTA.CCLCoupledController
open FTA.CCLGeometry
open FTA.CCLGuardCellClearance
open FTA.CCLPathIntersection
open FTA.GaussianPolynomialBounds
open FTA.ProjectivePath
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Membership form of the ordinary all-clear neighbourhood exclusion. -/
private theorem refinementOutput_not_near_arc_of_mem
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {arcs : List (BoundaryArc p)} {evidence : AllClear p arcs}
    (output : RefinementOutput p ambient current evidence)
    {arc : BoundaryArc p} (member : arc ∈ arcs) {t : ℚ}
    (lower : arc.interval.lower ≤ t) (upper : t ≤ arc.interval.upper)
    (near : CCLIntersectionSampler.WithinSqOfBox output.state.box
      (arc.path.value t) output.epsilon) : False := by
  obtain ⟨i, equality⟩ := List.mem_iff_get.mp member
  subst arc
  exact FTA.CCLClearanceExclusion.ClearEvidence.not_near_box
    (evidence.get i) output.state.refinesAmbient output.epsilonAtMostOne
    evidence.uniformClearance_pos
    (evidence.uniformClearance_le_certificate i) lower upper near
    output.centerResidual output.distanceBudget

/-- Nearby-point form of terminal-guard clearance, derived solely from the
budgets already stored by `GuardRefinementOutput`. -/
private theorem guardRefinementOutput_not_near_guard_point
    {p : GaussianPolynomial} {ambient box : RatBox}
    {current : WindingOneState p ambient}
    {sourceCells : List (SourceEventGuardCell p box)}
    {evidence : AllGuardClear p box sourceCells}
    (output : GuardRefinementOutput p ambient current evidence)
    (i : Fin sourceCells.length) {t : ℚ}
    (lower : (sourceCells.get i).item.cell.cell.interval.lower ≤ t)
    (upper : t ≤ (sourceCells.get i).item.cell.cell.interval.upper)
    (denominator :
      (sourceCells.get i).partition.entry.chart.path.denominator.eval
        (FTA.PathPolynomial.ofRat t) ≠ 0)
    (boxContains : box.Contains
      ((sourceCells.get i).partition.entry.chart.path.value t))
    (near : CCLIntersectionSampler.WithinSqOfBox output.state.box
      ((sourceCells.get i).partition.entry.chart.path.value t)
        output.epsilon) : False := by
  let point := (sourceCells.get i).partition.entry.chart.path.value t
  let margin := evidence.uniformClearance
  let L := denseLipschitzBound p (nearbyAmbient ambient)
  have centerInNearby :
      (nearbyAmbient ambient).Contains output.state.box.center :=
    nearbyAmbient_contains
      (output.state.refinesAmbient.contains output.state.box.contains_center)
  have pointInNearby : (nearbyAmbient ambient).Contains point :=
    nearbyAmbient_contains_of_withinSqOfBox output.state.refinesAmbient
      output.epsilonAtMostOne near
  rcases near with ⟨witness, witnessInBox, pointWitnessDistance⟩
  have witnessCenterDistance :
      normSq (witness - output.state.box.center) ≤
        output.state.box.diagonalSq :=
    RatBox.normSq_sub_le_diagonalSq witnessInBox
      output.state.box.contains_center
  have pointDecomposition :
      point - output.state.box.center =
        (point - witness) + (witness - output.state.box.center) := by
    ext <;> simp only [sub_re, sub_im, add_re, add_im] <;> ring
  have pointDistance : normSq (point - output.state.box.center) <
      2 * (output.epsilon + output.state.box.diagonalSq) := by
    rw [pointDecomposition]
    apply (normSq_add_le_two (point - witness)
      (witness - output.state.box.center)).trans_lt
    exact mul_lt_mul_of_pos_left
      (add_lt_add_of_lt_of_le pointWitnessDistance witnessCenterDistance)
      (by norm_num)
  have scaledDistance :
      L * normSq (point - output.state.box.center) <
        L * (2 * (output.epsilon + output.state.box.diagonalSq)) := by
    apply mul_lt_mul_of_pos_left pointDistance
    exact denseLipschitzBound_pos p (nearbyAmbient ambient)
  have evaluationDifference :
      normSq (p.eval point - p.eval output.state.box.center) < margin / 8 := by
    have lipschitz := normSq_dense_eval_sub_eval_le_denseLipschitzBound
      p pointInNearby centerInNearby
    have scaledDistance' :
        L * normSq (point + -output.state.box.center) <
          L * (2 * (output.epsilon + output.state.box.diagonalSq)) := by
      simpa only [GaussianRat.sub_eq_add_neg] using scaledDistance
    have evaluationDistance :
        normSq (p.eval point - p.eval output.state.box.center) <
          L * (2 * (output.epsilon + output.state.box.diagonalSq)) := by
      simpa only [GaussianRat.sub_eq_add_neg] using
        lipschitz.trans_lt scaledDistance'
    exact evaluationDistance.trans (by
      simpa only [L, margin] using output.distanceBudget)
  have pointEvaluation : normSq (p.eval point) < margin / 2 := by
    have decomposition :
        (p.eval point - p.eval output.state.box.center) +
            p.eval output.state.box.center = p.eval point := by
      ext <;> simp only [sub_re, sub_im, add_re, add_im] <;> ring
    have sumBound := normSq_add_le_two
      (p.eval point - p.eval output.state.box.center)
      (p.eval output.state.box.center)
    rw [decomposition] at sumBound
    have centerResidual :
        normSq (p.eval output.state.box.center) < margin / 8 := by
      simpa only [margin] using output.centerResidual
    nlinarith
  have clearanceLower : margin ≤ normSq (p.eval point) := by
    apply (evidence.uniformClearance_le_certificate i).trans
    simpa only [point] using
      (evidence.get i).lower lower upper denominator boxContains
  nlinarith [evidence.uniformClearance_pos]

/-- The ordinary clear arcs and terminal guard cells jointly exclude every
rational point of every planned branch boundary from one explicit positive
neighbourhood of the final guarded box. -/
theorem alignedAllClear_guardClear_not_near_boundary
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {word : Prefix.Word}
    {separation : CCLDenominator.SeparationOutput p ambient current
      (adjugate (RawParser.parse word).matrix)}
    {arcs : List (BoundaryArc p)} {evidence : AllClear p arcs}
    (alignment : ClearFamilyAlignment p separation.state.box
      (separatedRelevantClearCells p (RawParser.parse word)
        separation) arcs)
    (output : RefinementOutput p ambient separation.state evidence)
    (guardEvidence : AllGuardClear p separation.state.box
      (separatedEventGuardCells p (RawParser.parse word) separation))
    (guardOutput : GuardRefinementOutput p ambient output.state guardEvidence)
    (source : CCLBranchPlan.BoundarySource)
    (sourceMember : source ∈
      CCLBranchPlan.inputPlan (RawParser.parse word))
    (point : QI) (contains : separation.state.box.Contains point)
    (boundary : source.form.eval point = 0)
    (near : CCLIntersectionSampler.WithinSqOfBox guardOutput.state.box point
      (min output.epsilon guardOutput.epsilon)) : False := by
  have stateDeterminant :
      determinant (RawParser.parse word).matrix ≠ 0 := by
    simpa only [determinant, Mat2.det] using
      RawParser.parse_det_ne word
  rcases separatedChartPartitions_guardCoverage_boundary_point
      stateDeterminant separation source sourceMember point contains boundary with
    ⟨partition, partitionMember, _sourceEquality, t, pathDenominator,
      pathValue, coverage⟩
  cases coverage with
  | clear cell cellMember lower upper =>
      have holds :
          (boxConditions partition.entry.chart.path
            separation.state.box).HoldsAt t :=
        (contains_value_iff_holdsAt partition.entry.chart.path
          separation.state.box t pathDenominator).mp (by
            rw [pathValue]
            exact contains)
      rcases relevantClearCellsOfSourcePartitions_cover_of_clear
          (separatedChartPartitions p (RawParser.parse word)
            separation) partition partitionMember cell cellMember lower upper
          holds with
        ⟨candidate, candidateMember, partitionEquality, candidateLower,
          candidateUpper⟩
      rcases alignment.source_arc_of_mem candidateMember with
        ⟨arc, arcMember, _formEq, pathEq, intervalEq⟩
      have nearOutput : CCLIntersectionSampler.WithinSqOfBox
          output.state.box point output.epsilon := by
        rcases near.mono (min_le_left _ _) with
          ⟨witness, witnessInside, distance⟩
        exact ⟨witness, guardOutput.refines.contains witnessInside,
          distance⟩
      have candidateNear : CCLIntersectionSampler.WithinSqOfBox
          output.state.box
            (candidate.sourceCell.partition.entry.chart.path.value t)
              output.epsilon := by
        rw [partitionEquality, pathValue]
        exact nearOutput
      have excluded := refinementOutput_not_near_arc_of_mem output arcMember
        (t := t)
      rw [pathEq, intervalEq] at excluded
      exact excluded candidateLower candidateUpper candidateNear
  | event planEquality cell cellMember lower upper =>
      let eventCoverage : GuardEventCoverage partition.plan t :=
        .event planEquality cell cellMember lower upper
      rcases eventCoverage.mem_eventGuardCellsOfSourcePartitions
          partitionMember with
        ⟨sourceCell, sourceCellMember, partitionEquality, eventLower,
          eventUpper⟩
      have nearGuard : CCLIntersectionSampler.WithinSqOfBox
          guardOutput.state.box point guardOutput.epsilon :=
        near.mono (min_le_right _ _)
      have pathNear : CCLIntersectionSampler.WithinSqOfBox
          guardOutput.state.box
            (sourceCell.partition.entry.chart.path.value t)
              guardOutput.epsilon := by
        rw [partitionEquality, pathValue]
        exact nearGuard
      have pathContains : separation.state.box.Contains
          (sourceCell.partition.entry.chart.path.value t) := by
        rw [partitionEquality, pathValue]
        exact contains
      obtain ⟨i, equality⟩ := List.mem_iff_get.mp sourceCellMember
      have excluded := guardRefinementOutput_not_near_guard_point
        guardOutput i (t := t)
      have getEquality :
          (separatedEventGuardCells p (RawParser.parse word)
            separation).get i = sourceCell := by
        simpa only [separatedEventGuardCells] using equality
      rw [getEquality] at excluded
      exact excluded eventLower eventUpper (by
        rw [partitionEquality]
        exact pathDenominator) pathContains pathNear

end CCLBoundaryNeighborhood
end FTA
