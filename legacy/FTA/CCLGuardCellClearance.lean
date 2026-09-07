import FTA.CCLBranchEvent
import FTA.CCLClearanceExclusion
import FTA.CCLCurveDecision

/-!
# Polynomial clearance on terminal CCL guard cells

The total branch partition has two sorts of cells.  All-interior cells already
feed the ordinary zero-count clearance family.  A terminal guard cell still
has clear rational endpoints for every squarefree guard factor, even though
it contains a first-member event.  Consequently the polynomial common factor
on that cell has the same finite zero-or-positive decision as an ordinary
arc.

This module records the missing trichotomy for a source-labelled terminal
guard cell: the cleared polynomial coordinates are identically zero, their
common-factor count is positive, or the whole cell carries an explicit affine
clearance certificate.  No algebraic root is chosen.
-/

namespace FTA
namespace CCLGuardCellClearance

open CCL CCL.GaussianRat
open FTA.CCLBranchCharts
open FTA.CCLBranchEvidence
open FTA.CCLBranchEvent
open FTA.CCLBranchPartition
open FTA.CCLCurveDecision
open FTA.CCLClearanceExclusion
open FTA.CCLGeometry
open FTA.CCLIntersectionPartition
open FTA.CCLPathIntersection
open FTA.GaussianPolynomialBounds
open FTA.PathClearance
open FTA.ProjectivePath
open FTA.ProjectivePathBounds
open FTA.RootTrackSeparation
open FTA.RootCountDivisibility
open FTA.SquarefreeFactorization

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- The underlying terminal guard cell has nonzero combined-guard values at
both rational endpoints, despite containing an event in its interior. -/
theorem eventGuardCell_arcGuard_lowerClear
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    (cell : EventGuardCell decomposition) :
    (arcGuard p path box).eval cell.cell.interval.lower ≠ 0 := by
  rw [decomposition.eval_identity]
  exact mul_ne_zero decomposition.scalar_ne_zero
    (factorProduct_eval_ne_zero_of_eventGuard cell.cell.lowerClear)

theorem eventGuardCell_arcGuard_upperClear
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    (cell : EventGuardCell decomposition) :
    (arcGuard p path box).eval cell.cell.interval.upper ≠ 0 := by
  rw [decomposition.eval_identity]
  exact mul_ne_zero decomposition.scalar_ne_zero
    (factorProduct_eval_ne_zero_of_eventGuard cell.cell.upperClear)

/-- Membership of the polynomial common factor in the combined guard
transfers terminal-cell endpoint clearance to that factor. -/
theorem eventGuardCell_commonFactor_lowerClear
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    (cell : EventGuardCell decomposition)
    (clearedNonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false) :
    (PathClearance.commonFactor (clearedReal p path)
      (clearedImag p path)).eval cell.cell.interval.lower ≠ 0 :=
  eval_ne_zero_of_mem_arcPolynomials
    (commonFactor_mem_arcPolynomials p path box)
    (PathClearance.commonFactor_isZero_false clearedNonzero)
    (eventGuardCell_arcGuard_lowerClear cell)

theorem eventGuardCell_commonFactor_upperClear
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    (cell : EventGuardCell decomposition)
    (clearedNonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false) :
    (PathClearance.commonFactor (clearedReal p path)
      (clearedImag p path)).eval cell.cell.interval.upper ≠ 0 :=
  eval_ne_zero_of_mem_arcPolynomials
    (commonFactor_mem_arcPolynomials p path box)
    (PathClearance.commonFactor_isZero_false clearedNonzero)
    (eventGuardCell_arcGuard_upperClear cell)

/-- Quantitative zero-count evidence retained with its exact source guard
cell.  The affine certificate needs a nonzero path denominator only at the
queried parameter, so it remains meaningful even when a different guarded
event in the same cell is a projective pole. -/
structure ClearGuardCurveCell
    (p : GaussianPolynomial) (box : RatBox)
    (sourceCell : SourceEventGuardCell p box) where
  clearedNonzero :
    (clearedReal p sourceCell.partition.entry.chart.path).isZero = false ∨
      (clearedImag p
        sourceCell.partition.entry.chart.path).isZero = false
  certificate : AffineCertificate p
    sourceCell.partition.entry.chart.path sourceCell.item.cell.cell.interval

/-- Exact polynomial alternative on one source-labelled terminal guard cell.
The positive branch retains the computed integer count on this very cell;
the clear branch retains the resulting affine lower bound. -/
inductive GuardCurveDecision
    (p : GaussianPolynomial) (box : RatBox)
    (sourceCell : SourceEventGuardCell p box) where
  | identicallyZero
      (realZero :
        (clearedReal p
          sourceCell.partition.entry.chart.path).isZero = true)
      (imagZero :
        (clearedImag p
          sourceCell.partition.entry.chart.path).isZero = true)
  | clear (evidence : ClearGuardCurveCell p box sourceCell)
  | positive
      (clearedNonzero :
        (clearedReal p
          sourceCell.partition.entry.chart.path).isZero = false ∨
        (clearedImag p
          sourceCell.partition.entry.chart.path).isZero = false)
      (countPositive : 0 < ProjectivePath.commonFactorRootCount2 p
        sourceCell.partition.entry.chart.path clearedNonzero
        sourceCell.item.cell.cell.interval.lower
        sourceCell.item.cell.cell.interval.upper)

/-- Execute the coordinate dichotomy and exact common-factor count on a
terminal guard cell. -/
def decideSourceEventGuardCellCurve
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box) :
    GuardCurveDecision p box sourceCell := by
  let path := sourceCell.partition.entry.chart.path
  let cell := sourceCell.item.cell
  match coordinateDecision : decideClearedCoordinates p path with
  | .identicallyZero realZero imagZero =>
      exact .identicallyZero realZero imagZero
  | .nonzero clearedNonzero =>
      match CCLCurveDecision.decide p path clearedNonzero cell.cell.interval
          cell.cell.proper
          (eventGuardCell_commonFactor_lowerClear cell clearedNonzero)
          (eventGuardCell_commonFactor_upperClear cell clearedNonzero) with
      | .clear certificate =>
          exact .clear
            { clearedNonzero := clearedNonzero
              certificate := certificate }
      | .positiveCount positive =>
          exact .positive clearedNonzero positive

/-- Pointwise meaning of the clear constructor, phrased directly on the
source chart used by boundary coverage. -/
theorem ClearGuardCurveCell.lower
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCell : SourceEventGuardCell p box}
    (evidence : ClearGuardCurveCell p box sourceCell)
    {t : ℚ}
    (lower : sourceCell.item.cell.cell.interval.lower ≤ t)
    (upper : t ≤ sourceCell.item.cell.cell.interval.upper)
    (denominator : sourceCell.partition.entry.chart.path.denominator.eval
      (FTA.PathPolynomial.ofRat t) ≠ 0) :
    evidence.certificate.bound ≤
      normSq (p.eval
        (sourceCell.partition.entry.chart.path.value t)) :=
  evidence.certificate.lower t lower upper denominator

theorem ClearGuardCurveCell.bound_pos
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCell : SourceEventGuardCell p box}
    (evidence : ClearGuardCurveCell p box sourceCell) :
    0 < evidence.certificate.bound :=
  evidence.certificate.positive

/-! ## Total traversal of the finite guarded family -/

/-- A terminal guard cell either exposes a retained relevant curve event or
its executable relevance filter is empty.  Keeping this decision beside a
non-clear curve result distinguishes a genuine in-box affine event from guard
roots that arise only from poles, box edges, or other irrelevant factors. -/
inductive GuardCellRelevanceDecision
    (p : GaussianPolynomial) (box : RatBox)
    (sourceCell : SourceEventGuardCell p box) where
  | relevant
      (event : RelevantCurveEvent p
        sourceCell.partition.entry.chart.path box)
      (member : event ∈ CCLBranchEvent.EventGuardCell.relevantCurveEvents
        sourceCell.item.cell)
  | none
      (empty : CCLBranchEvent.EventGuardCell.relevantCurveEvents
        sourceCell.item.cell = [])

/-- Execute the relevance split without selecting or completing an algebraic
root. -/
def decideGuardCellRelevance
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box) :
    GuardCellRelevanceDecision p box sourceCell := by
  match eventsEquation : CCLBranchEvent.EventGuardCell.relevantCurveEvents
      sourceCell.item.cell with
  | [] => exact .none eventsEquation
  | event :: events =>
      exact .relevant event (by simp [eventsEquation])

/-! ## Quantitative exclusion neighborhoods for irrelevant pole events -/

/-- Refine a pole-labelled count-one event until its denominator norm is
uniformly below the chart's explicit bounded-box pole threshold. -/
def GuardEventClassification.poleNeighborhood
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCell : SourceEventGuardCell p box}
    (item : GuardEventClassification p
      sourceCell.partition.entry.chart.path box sourceCell.item.cell)
    (determinantNonzero : determinant
      sourceCell.partition.entry.source.matrix ≠ 0) :
    NarrowEventApproximation item.classification.branch.factor.input
      item.classification.parent
      (multipleNeighborhoodWidth
        (denominatorNorm sourceCell.partition.entry.chart.path)
        item.classification.branch.factor.polynomial
        item.classification.parent
        (sourceCell.partition.entry.chart.poleDenominatorThreshold box)) :=
  narrowMultipleNeighborhood item.classification.branch.factor.input
    (denominatorNorm sourceCell.partition.entry.chart.path)
    item.classification.parent
    (sourceCell.partition.entry.chart.poleDenominatorThreshold box)
    (sourceCell.partition.entry.chart.poleDenominatorThreshold_pos box
      determinantNonzero)

/-- Every affine parameter in that computed pole neighborhood maps outside
the closed separation box. -/
theorem GuardEventClassification.poleNeighborhood_excludes_contains
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCell : SourceEventGuardCell p box}
    (item : GuardEventClassification p
      sourceCell.partition.entry.chart.path box sourceCell.item.cell)
    (denominatorEquality : denominatorIsEquality
      item.classification.branch = true)
    (determinantNonzero : determinant
      sourceCell.partition.entry.source.matrix ≠ 0)
    {t : ℚ}
    (lower :
      (FTA.CCLGuardCellClearance.GuardEventClassification.poleNeighborhood
        item determinantNonzero).refined.interval.lower ≤ t)
    (upper : t ≤
      (FTA.CCLGuardCellClearance.GuardEventClassification.poleNeighborhood
        item determinantNonzero).refined.interval.upper)
    (denominatorNonzero :
      sourceCell.partition.entry.chart.path.denominator.eval
        (FTA.PathPolynomial.ofRat t) ≠ 0) :
    ¬box.Contains
      (sourceCell.partition.entry.chart.path.value t) := by
  let chart := sourceCell.partition.entry.chart
  let branch := item.classification.branch
  let margin := chart.poleDenominatorThreshold box
  have marginPositive : 0 < margin :=
    chart.poleDenominatorThreshold_pos box determinantNonzero
  have absSmall := narrowMultipleNeighborhood_abs_lt branch.factor.input
    (denominatorFactor_toPolynomial_dvd branch denominatorEquality)
      item.classification.parent marginPositive
        (by simpa only [GuardEventClassification.poleNeighborhood, chart,
          branch, margin] using lower)
        (by simpa only [GuardEventClassification.poleNeighborhood, chart,
          branch, margin] using upper)
  have denominatorNormNonnegative : 0 ≤
      (denominatorNorm chart.path).eval t := by
    rw [eval_denominatorNorm]
    exact normSq_nonneg _
  have denominatorSmall :
      normSq (chart.path.denominator.eval (FTA.PathPolynomial.ofRat t)) <
        chart.poleDenominatorThreshold box := by
    rw [← eval_denominatorNorm]
    simpa only [abs_of_nonneg denominatorNormNonnegative, margin, branch,
      chart] using absSmall
  exact chart.not_contains_of_denominatorNorm_lt_threshold box t
    denominatorNonzero denominatorSmall

/-! ## Uniform packaging of all three irrelevance reasons -/

/-- A refined event neighborhood is either quantitatively curve-clear or
maps every affine parameter outside the active box. -/
inductive IrrelevantNeighborhoodDisposition
    (p : GaussianPolynomial) (path : Path) (box : RatBox)
    (interval : FTA.SturmTransducer.RationalInterval) where
  | clear (certificate : AffineCertificate p path interval)
  | outside
      (excludes : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
        path.denominator.eval (FTA.PathPolynomial.ofRat t) ≠ 0 →
          ¬box.Contains (path.value t))

/-- Restrict either quantitative disposition to a nested rational interval. -/
def IrrelevantNeighborhoodDisposition.restrict
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {parent child : FTA.SturmTransducer.RationalInterval}
    (disposition : IrrelevantNeighborhoodDisposition p path box parent)
    (refines : child.Refines parent) :
    IrrelevantNeighborhoodDisposition p path box child := by
  cases disposition with
  | clear certificate =>
      exact .clear
        { bound := certificate.bound
          positive := certificate.positive
          lower := by
            intro t lower upper denominator
            exact certificate.lower t (refines.1.trans lower)
              (upper.trans refines.2) denominator }
  | outside excludes =>
      exact .outside (by
        intro t lower upper denominator
        exact excludes (refines.1.trans lower) (upper.trans refines.2)
          denominator)

/-- One count-one neighborhood retaining its parent refinement and the exact
quantitative disposition used by the terminal-cell resolver. -/
structure IrrelevantEventNeighborhood
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    {cell : EventGuardCell decomposition}
    (item : GuardEventClassification p path box cell) where
  root : FTA.SturmTransducer.CountOneInterval
    item.classification.branch.factor.polynomial
  refines : root.interval.Refines item.classification.parent.interval
  disposition : IrrelevantNeighborhoodDisposition p path box root.interval

/-- Convert every exact irrelevance reason into a fully quantitative local
neighborhood.  Non-curve branches get an affine residual certificate;
projective poles and failed box checks get whole-neighborhood box exclusion. -/
def GuardEventIrrelevanceReason.neighborhood
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCell : SourceEventGuardCell p box}
    {item : GuardEventClassification p
      sourceCell.partition.entry.chart.path box sourceCell.item.cell}
    (reason : GuardEventIrrelevanceReason item)
    (clearedNonzero :
      (clearedReal p sourceCell.partition.entry.chart.path).isZero = false ∨
      (clearedImag p sourceCell.partition.entry.chart.path).isZero = false)
    (determinantNonzero : determinant
      sourceCell.partition.entry.source.matrix ≠ 0) :
    IrrelevantEventNeighborhood item := by
  let path := sourceCell.partition.entry.chart.path
  let branch := item.classification.branch
  let parent := item.classification.parent
  cases reason with
  | curveNonEquality curveNonEquality =>
      let signs := branch.computeEventSigns parent
      exact
        { root := signs.refined
          refines := signs.refines
          disposition := .clear
            (curveNonEqualityAffineCertificate branch parent clearedNonzero
              curveNonEquality) }
  | pole _curveEquality denominatorEquality =>
      let poleNeighborhood :=
        FTA.CCLGuardCellClearance.GuardEventClassification.poleNeighborhood
          item determinantNonzero
      exact
        { root := poleNeighborhood.refined
          refines := poleNeighborhood.refines
          disposition := .outside (by
            intro t lower upper denominator
            exact FTA.CCLGuardCellClearance.GuardEventClassification.poleNeighborhood_excludes_contains
              item denominatorEquality
                determinantNonzero (by
                  simpa only [poleNeighborhood] using lower) (by
                  simpa only [poleNeighborhood] using upper) denominator) }
  | outsideBox _curveEquality _denominatorNonEquality boxFalse =>
      let signs := boxEventSigns branch parent
      exact
        { root := signs.refined
          refines := signs.refines
          disposition := .outside (by
            intro t lower upper denominator
            exact boxEventCheck_eq_false_excludes_contains branch parent
              boxFalse lower upper denominator) }

/-- Extract the proof-bearing reason promised by an empty relevance filter. -/
def GuardEventClassification.irrelevanceReasonOfCellEmpty
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    {cell : EventGuardCell decomposition}
    (empty : CCLBranchEvent.EventGuardCell.relevantCurveEvents cell = [])
    (item : GuardEventClassification p path box cell)
    (member : item ∈ CCLBranchEvent.EventGuardCell.classifications cell) :
    GuardEventIrrelevanceReason item :=
  item.irrelevanceReason?.get
    (item.irrelevanceReason?_isSome_of_cell_empty empty member)

/-- Source-labelled quantitative neighborhood for one exhaustive classified
event of a relevance-empty terminal guard cell. -/
structure SourceIrrelevantEventNeighborhood
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box) where
  item : GuardEventClassification p
    sourceCell.partition.entry.chart.path box sourceCell.item.cell
  itemMember : item ∈
    CCLBranchEvent.EventGuardCell.classifications sourceCell.item.cell
  neighborhood : IrrelevantEventNeighborhood item

/-- Pointwise constructor used by the executable neighborhood family.  Naming
it separately keeps later coverage proofs independent of proof-term details
inside `List.attach`. -/
def GuardEventClassification.quantitativeNeighborhoodOfCellEmpty
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box)
    (empty : CCLBranchEvent.EventGuardCell.relevantCurveEvents
      sourceCell.item.cell = [])
    (clearedNonzero :
      (clearedReal p sourceCell.partition.entry.chart.path).isZero = false ∨
      (clearedImag p
        sourceCell.partition.entry.chart.path).isZero = false)
    (determinantNonzero : determinant
      sourceCell.partition.entry.source.matrix ≠ 0)
    (item : GuardEventClassification p
      sourceCell.partition.entry.chart.path box sourceCell.item.cell)
    (member : item ∈
      CCLBranchEvent.EventGuardCell.classifications sourceCell.item.cell) :
    SourceIrrelevantEventNeighborhood sourceCell :=
  let reason :=
    FTA.CCLGuardCellClearance.GuardEventClassification.irrelevanceReasonOfCellEmpty
      empty item member
  { item := item
    itemMember := member
    neighborhood :=
      FTA.CCLGuardCellClearance.GuardEventIrrelevanceReason.neighborhood
        reason clearedNonzero determinantNonzero }

/-- Compute the complete finite family of quantitative neighborhoods for a
relevance-empty positive source cell. -/
def irrelevantEventNeighborhoodsOfCellEmpty
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box)
    (empty : CCLBranchEvent.EventGuardCell.relevantCurveEvents
      sourceCell.item.cell = [])
    (clearedNonzero :
      (clearedReal p sourceCell.partition.entry.chart.path).isZero = false ∨
      (clearedImag p sourceCell.partition.entry.chart.path).isZero = false)
    (determinantNonzero : determinant
      sourceCell.partition.entry.source.matrix ≠ 0) :
    List (SourceIrrelevantEventNeighborhood sourceCell) :=
  (CCLBranchEvent.EventGuardCell.classifications
    sourceCell.item.cell).attach.map fun attached =>
      FTA.CCLGuardCellClearance.GuardEventClassification.quantitativeNeighborhoodOfCellEmpty
        sourceCell empty clearedNonzero determinantNonzero attached.1 attached.2

theorem irrelevantEventNeighborhoodsOfCellEmpty_ne_nil
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box)
    (empty : CCLBranchEvent.EventGuardCell.relevantCurveEvents
      sourceCell.item.cell = [])
    (clearedNonzero :
      (clearedReal p sourceCell.partition.entry.chart.path).isZero = false ∨
      (clearedImag p sourceCell.partition.entry.chart.path).isZero = false)
    (determinantNonzero : determinant
      sourceCell.partition.entry.source.matrix ≠ 0) :
    irrelevantEventNeighborhoodsOfCellEmpty sourceCell empty clearedNonzero
      determinantNonzero ≠ [] := by
  intro resultEmpty
  cases classificationsEquation :
      CCLBranchEvent.EventGuardCell.classifications sourceCell.item.cell with
  | nil =>
      exact CCLBranchEvent.EventGuardCell.classifications_ne_nil
        sourceCell.item.cell classificationsEquation
  | cons head tail =>
      simp [irrelevantEventNeighborhoodsOfCellEmpty,
        classificationsEquation] at resultEmpty

/-- Every computed quantitative neighborhood lies inside the original
terminal guard cell that produced it. -/
theorem SourceIrrelevantEventNeighborhood.root_refines_cell
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCell : SourceEventGuardCell p box}
    (candidate : SourceIrrelevantEventNeighborhood sourceCell) :
    candidate.neighborhood.root.interval.Refines
      sourceCell.item.cell.cell.interval :=
  FTA.SturmTransducer.RationalInterval.refines_trans
    candidate.neighborhood.refines
      (FTA.CCLBranchEvent.GuardEventClassification.parent_refines_cell
        candidate.itemMember)

/-- The finite quantitative neighborhood family covers every exact rational
zero of the combined guard in its relevance-empty terminal cell.  Coverage is
not merely inherited from the original squarefree factor: divisor-root
uniqueness first carries the zero through all finite condition splits, and
count-one refinement then carries it into the chosen quantitative
neighborhood. -/
theorem irrelevantEventNeighborhoodsOfCellEmpty_covers_guard_zero
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box)
    (empty : CCLBranchEvent.EventGuardCell.relevantCurveEvents
      sourceCell.item.cell = [])
    (clearedNonzero :
      (clearedReal p sourceCell.partition.entry.chart.path).isZero = false ∨
      (clearedImag p
        sourceCell.partition.entry.chart.path).isZero = false)
    (determinantNonzero : determinant
      sourceCell.partition.entry.source.matrix ≠ 0)
    {t : ℚ} (lower : sourceCell.item.cell.cell.interval.lower ≤ t)
    (upper : t ≤ sourceCell.item.cell.cell.interval.upper)
    (guardZero : (arcGuard p sourceCell.partition.entry.chart.path box).eval
      t = 0) :
    ∃ candidate ∈ irrelevantEventNeighborhoodsOfCellEmpty sourceCell empty
        clearedNonzero determinantNonzero,
      candidate.neighborhood.root.interval.lower ≤ t ∧
        t ≤ candidate.neighborhood.root.interval.upper ∧
        candidate.item.classification.branch.factor.polynomial.eval t = 0 := by
  rcases sourceCell.item.cell.eventIntervals_covers_guard_zero lower upper
      guardZero with
    ⟨entry, entryMember, entryLower, entryUpper, entryZero⟩
  let item : GuardEventClassification p
      sourceCell.partition.entry.chart.path box sourceCell.item.cell :=
    { entry := entry
      classification := FTA.CCLCountOneClassification.followCountOneConditions
        entry.factor entry.root
          (arcPolynomials p sourceCell.partition.entry.chart.path box) }
  have itemMember : item ∈
      CCLBranchEvent.EventGuardCell.classifications sourceCell.item.cell := by
    rw [CCLBranchEvent.EventGuardCell.classifications, List.mem_map]
    exact ⟨entry, entryMember, rfl⟩
  have retained := item.classification.rationalZero_mem entryLower entryUpper
    entryZero
  let candidate :=
    FTA.CCLGuardCellClearance.GuardEventClassification.quantitativeNeighborhoodOfCellEmpty
      sourceCell empty clearedNonzero determinantNonzero item itemMember
  have neighborhoodInside :=
    FTA.PositiveLowerBound.CountOneInterval.rationalZero_mem_of_refines
      item.classification.branch.factor.input item.classification.parent
        candidate.neighborhood.root candidate.neighborhood.refines retained.1
          retained.2.1 retained.2.2
  refine ⟨candidate, ?_, neighborhoodInside.1, neighborhoodInside.2,
    retained.2.2⟩
  let attached : { classified // classified ∈
      CCLBranchEvent.EventGuardCell.classifications sourceCell.item.cell } :=
    ⟨item, itemMember⟩
  rw [irrelevantEventNeighborhoodsOfCellEmpty, List.mem_map]
  exact ⟨attached, by simp [attached], rfl⟩

/-- An irrelevant neighborhood refined once more so that the original
squarefree guard factor, not only its selected classified divisor, has a
count-one interval with clear endpoints.  Its complement certificate gives a
positive factor bound everywhere else in the terminal cell. -/
structure AlignedSourceIrrelevantEventNeighborhood
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box) where
  source : SourceIrrelevantEventNeighborhood sourceCell
  alignment : FTA.RootCountDivisibility.DivisorCountOneAlignment
    source.item.entry.root source.neighborhood.root
  disposition : IrrelevantNeighborhoodDisposition p
    sourceCell.partition.entry.chart.path box alignment.refined.interval
  complement : FTA.RootCountDivisibility.CountOneComplementCertificate
    source.item.entry.root alignment.multiple

/-- Align one classified divisor neighborhood with its original guard-factor
count and retain both its local disposition and its complement lower bound. -/
def SourceIrrelevantEventNeighborhood.align
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCell : SourceEventGuardCell p box}
    (source : SourceIrrelevantEventNeighborhood sourceCell) :
    AlignedSourceIrrelevantEventNeighborhood sourceCell := by
  have branchRefinesEntry : source.neighborhood.root.interval.Refines
      source.item.entry.root.interval :=
    FTA.SturmTransducer.RationalInterval.refines_trans
      source.neighborhood.refines source.item.classification.refines
  let alignment := FTA.RootCountDivisibility.alignDivisorCountOne
    source.item.classification.branch.factor.input source.item.entry.factor.input
      source.item.entry.root source.neighborhood.root
        source.item.classification.divides branchRefinesEntry
  exact
    { source := source
      alignment := alignment
      disposition := source.neighborhood.disposition.restrict
        alignment.refinesSmall
      complement := FTA.RootCountDivisibility.countOneComplementCertificate
        source.item.entry.factor.input source.item.entry.root alignment.multiple
          alignment.refinesLarge }

/-- Complete aligned family, in the same order as the original quantitative
neighborhood family and hence as the terminal cell's event entries. -/
def alignedIrrelevantEventNeighborhoodsOfCellEmpty
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box)
    (empty : CCLBranchEvent.EventGuardCell.relevantCurveEvents
      sourceCell.item.cell = [])
    (clearedNonzero :
      (clearedReal p sourceCell.partition.entry.chart.path).isZero = false ∨
      (clearedImag p
        sourceCell.partition.entry.chart.path).isZero = false)
    (determinantNonzero : determinant
      sourceCell.partition.entry.source.matrix ≠ 0) :
    List (AlignedSourceIrrelevantEventNeighborhood sourceCell) :=
  (irrelevantEventNeighborhoodsOfCellEmpty sourceCell empty clearedNonzero
    determinantNonzero).map fun source => source.align

/-- Alignment preserves complete guard-zero coverage. -/
theorem alignedIrrelevantEventNeighborhoodsOfCellEmpty_covers_guard_zero
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box)
    (empty : CCLBranchEvent.EventGuardCell.relevantCurveEvents
      sourceCell.item.cell = [])
    (clearedNonzero :
      (clearedReal p sourceCell.partition.entry.chart.path).isZero = false ∨
      (clearedImag p
        sourceCell.partition.entry.chart.path).isZero = false)
    (determinantNonzero : determinant
      sourceCell.partition.entry.source.matrix ≠ 0)
    {t : ℚ} (lower : sourceCell.item.cell.cell.interval.lower ≤ t)
    (upper : t ≤ sourceCell.item.cell.cell.interval.upper)
    (guardZero : (arcGuard p sourceCell.partition.entry.chart.path box).eval
      t = 0) :
    ∃ candidate ∈ alignedIrrelevantEventNeighborhoodsOfCellEmpty sourceCell
        empty clearedNonzero determinantNonzero,
      candidate.alignment.refined.interval.lower ≤ t ∧
        t ≤ candidate.alignment.refined.interval.upper := by
  rcases irrelevantEventNeighborhoodsOfCellEmpty_covers_guard_zero sourceCell
      empty clearedNonzero determinantNonzero lower upper guardZero with
    ⟨source, sourceMember, sourceLower, sourceUpper, branchZero⟩
  let candidate := source.align
  have alignedInside :=
    FTA.PositiveLowerBound.CountOneInterval.rationalZero_mem_of_refines
      source.item.classification.branch.factor.input source.neighborhood.root
        candidate.alignment.refined candidate.alignment.refinesSmall
          sourceLower sourceUpper branchZero
  refine ⟨candidate, ?_, alignedInside⟩
  rw [alignedIrrelevantEventNeighborhoodsOfCellEmpty, List.mem_map]
  exact ⟨source, sourceMember, rfl⟩

/-! ## Positive guard bounds away from all irrelevant neighborhoods -/

/-- A pointwise positive squared-value bound for one polynomial, conditional
on lying in the terminal cell but outside every aligned irrelevant-event
neighborhood. -/
structure GuardAwayCertificate
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box)
    (neighborhoods :
      List (AlignedSourceIrrelevantEventNeighborhood sourceCell))
    (polynomial : FTA.CCLIntersectionPartition.RatPolynomial) where
  bound : ℚ
  positive : 0 < bound
  lower : ∀ {t : ℚ}, sourceCell.item.cell.cell.interval.lower ≤ t →
    t ≤ sourceCell.item.cell.cell.interval.upper →
    (∀ candidate ∈ neighborhoods,
      ¬(candidate.alignment.refined.interval.lower ≤ t ∧
        t ≤ candidate.alignment.refined.interval.upper)) →
      bound ≤ polynomial.eval t ^ 2

/-- The product of two away-certificates is an away-certificate for the
product polynomial. -/
def GuardAwayCertificate.mul
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCell : SourceEventGuardCell p box}
    {neighborhoods :
      List (AlignedSourceIrrelevantEventNeighborhood sourceCell)}
    {left right : FTA.CCLIntersectionPartition.RatPolynomial}
    (leftCertificate : GuardAwayCertificate sourceCell neighborhoods left)
    (rightCertificate : GuardAwayCertificate sourceCell neighborhoods right) :
    GuardAwayCertificate sourceCell neighborhoods (left * right) where
  bound := leftCertificate.bound * rightCertificate.bound
  positive := mul_pos leftCertificate.positive rightCertificate.positive
  lower := by
    intro t lower upper away
    rw [FTA.ComputablePolynomial.DensePolynomial.eval_mul, mul_pow]
    exact mul_le_mul (leftCertificate.lower lower upper away)
      (rightCertificate.lower lower upper away)
        rightCertificate.positive.le (sq_nonneg _)

/-- The event-factor complement certificate, transported into the global
aligned neighborhood family. -/
def guardEventEntryAwayCertificate
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box)
    (empty : CCLBranchEvent.EventGuardCell.relevantCurveEvents
      sourceCell.item.cell = [])
    (clearedNonzero :
      (clearedReal p sourceCell.partition.entry.chart.path).isZero = false ∨
      (clearedImag p
        sourceCell.partition.entry.chart.path).isZero = false)
    (determinantNonzero : determinant
      sourceCell.partition.entry.source.matrix ≠ 0)
    (entry : FactorCountOneInterval sourceCell.item.decomposition.factors)
    (entryMember : entry ∈ sourceCell.item.cell.eventIntervals) :
    GuardAwayCertificate sourceCell
      (alignedIrrelevantEventNeighborhoodsOfCellEmpty sourceCell empty
        clearedNonzero determinantNonzero) entry.factor.polynomial := by
  let item : GuardEventClassification p
      sourceCell.partition.entry.chart.path box sourceCell.item.cell :=
    { entry := entry
      classification :=
        FTA.CCLCountOneClassification.followCountOneConditions entry.factor
          entry.root
            (arcPolynomials p sourceCell.partition.entry.chart.path box) }
  have itemMember : item ∈
      CCLBranchEvent.EventGuardCell.classifications sourceCell.item.cell := by
    rw [CCLBranchEvent.EventGuardCell.classifications, List.mem_map]
    exact ⟨entry, entryMember, rfl⟩
  let source :=
    FTA.CCLGuardCellClearance.GuardEventClassification.quantitativeNeighborhoodOfCellEmpty
      sourceCell empty clearedNonzero determinantNonzero item itemMember
  have sourceMember : source ∈
      irrelevantEventNeighborhoodsOfCellEmpty sourceCell empty
        clearedNonzero determinantNonzero := by
    let attached : { classified // classified ∈
        CCLBranchEvent.EventGuardCell.classifications
          sourceCell.item.cell } := ⟨item, itemMember⟩
    rw [irrelevantEventNeighborhoodsOfCellEmpty, List.mem_map]
    exact ⟨attached, by simp [attached], rfl⟩
  let candidate := source.align
  have candidateMember : candidate ∈
      alignedIrrelevantEventNeighborhoodsOfCellEmpty sourceCell empty
        clearedNonzero determinantNonzero := by
    rw [alignedIrrelevantEventNeighborhoodsOfCellEmpty, List.mem_map]
    exact ⟨source, sourceMember, rfl⟩
  have rootInterval :=
    sourceCell.item.cell.cell.leaves.eventIntervals_root_interval entry
      entryMember
  have candidateEntry : candidate.source.item.entry = entry := rfl
  exact
    { bound := candidate.complement.bound
      positive := candidate.complement.positive
      lower := by
        intro t lower upper away
        have notInside := away candidate candidateMember
        apply candidate.complement.lower
        · rw [candidateEntry, rootInterval]
          exact lower
        · rw [candidateEntry, rootInterval]
          exact upper
        · exact notInside }

/-- Zero-count local factors already have a whole-cell away-certificate. -/
def guardInteriorFactorAwayCertificate
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box)
    (empty : CCLBranchEvent.EventGuardCell.relevantCurveEvents
      sourceCell.item.cell = [])
    (clearedNonzero :
      (clearedReal p sourceCell.partition.entry.chart.path).isZero = false ∨
      (clearedImag p
        sourceCell.partition.entry.chart.path).isZero = false)
    (determinantNonzero : determinant
      sourceCell.partition.entry.source.matrix ≠ 0)
    (factor : Factor)
    (leaf : LocalFactorLeaf factor sourceCell.item.cell.cell.interval)
    (interior : leaf.kind = .interior) :
    GuardAwayCertificate sourceCell
      (alignedIrrelevantEventNeighborhoodsOfCellEmpty sourceCell empty
        clearedNonzero determinantNonzero) factor.polynomial := by
  have countZero : FTA.Sturm.sturmRootCount2 factor.polynomial
      sourceCell.item.cell.cell.interval.lower
      sourceCell.item.cell.cell.interval.upper = 0 := by
    simpa [interior, FTA.SturmTransducer.EventKind.contribution2] using
      leaf.countCertificate
  let certificate := FTA.PositiveLowerBound.compute factor.input
    sourceCell.item.cell.cell.interval leaf.proper leaf.lowerClear
      leaf.upperClear countZero
  exact
    { bound := certificate.bound
      positive := certificate.positive
      lower := by
        intro t lower upper _away
        exact certificate.lower t lower upper }

/-- Structural fold over the proof-bearing local leaves.  The `lift` map
embeds each recursive tail event into the original cell's event list. -/
def guardFactorProductAwayCertificateAux
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box)
    (empty : CCLBranchEvent.EventGuardCell.relevantCurveEvents
      sourceCell.item.cell = [])
    (clearedNonzero :
      (clearedReal p sourceCell.partition.entry.chart.path).isZero = false ∨
      (clearedImag p
        sourceCell.partition.entry.chart.path).isZero = false)
    (determinantNonzero : determinant
      sourceCell.partition.entry.source.matrix ≠ 0) :
    {factors : List Factor} →
    (leaves : LocalFactorLeaves sourceCell.item.cell.cell.interval factors) →
    (lift : FactorCountOneInterval factors →
      FactorCountOneInterval sourceCell.item.decomposition.factors) →
    (liftFactor : ∀ entry, (lift entry).factor = entry.factor) →
    (liftMember : ∀ entry, entry ∈ leaves.eventIntervals →
      lift entry ∈ sourceCell.item.cell.eventIntervals) →
    GuardAwayCertificate sourceCell
      (alignedIrrelevantEventNeighborhoodsOfCellEmpty sourceCell empty
        clearedNonzero determinantNonzero) (factorProduct factors)
  | [], .nil, _lift, _liftFactor, _liftMember =>
      { bound := 1
        positive := zero_lt_one
        lower := by
          intro t _lower _upper _away
          simp [factorProduct,
            FTA.ComputablePolynomial.DensePolynomial.eval_constant] }
  | factor :: factors, .cons head tail, lift, liftFactor, liftMember => by
      let tailLift : FactorCountOneInterval factors →
          FactorCountOneInterval sourceCell.item.decomposition.factors :=
        fun entry => lift (entry.prepend factor)
      have tailLiftFactor : ∀ entry, (tailLift entry).factor = entry.factor := by
        intro entry
        exact liftFactor (entry.prepend factor)
      have tailLiftMember : ∀ entry, entry ∈ tail.eventIntervals →
          tailLift entry ∈ sourceCell.item.cell.eventIntervals := by
        intro entry member
        apply liftMember (entry.prepend factor)
        rw [LocalFactorLeaves.eventIntervals]
        split
        · exact List.mem_map.mpr ⟨entry, member, rfl⟩
        · exact List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨entry, member, rfl⟩)
      let tailCertificate := guardFactorProductAwayCertificateAux sourceCell
        empty clearedNonzero determinantNonzero tail tailLift tailLiftFactor
          tailLiftMember
      cases kindEquation : head.kind with
      | interior =>
          let headCertificate := guardInteriorFactorAwayCertificate sourceCell
            empty clearedNonzero determinantNonzero factor head kindEquation
          exact headCertificate.mul tailCertificate
      | firstMember =>
          let localEntry : FactorCountOneInterval (factor :: factors) :=
            { factor := factor
              member := List.mem_cons_self
              root := head.countOneInterval kindEquation }
          have localMember : localEntry ∈
              (LocalFactorLeaves.cons head tail).eventIntervals := by
            rw [LocalFactorLeaves.eventIntervals]
            split
            · rename_i interiorEquation
              rw [kindEquation] at interiorEquation
              contradiction
            · exact List.mem_cons_self
          let entry := lift localEntry
          have entryMember : entry ∈ sourceCell.item.cell.eventIntervals :=
            liftMember localEntry localMember
          have factorEquality : entry.factor = factor := liftFactor localEntry
          let headCertificate := guardEventEntryAwayCertificate sourceCell
            empty clearedNonzero determinantNonzero entry entryMember
          have polynomialEquality : entry.factor.polynomial =
              factor.polynomial := congrArg Factor.polynomial factorEquality
          let transported : GuardAwayCertificate sourceCell
              (alignedIrrelevantEventNeighborhoodsOfCellEmpty sourceCell empty
                clearedNonzero determinantNonzero) factor.polynomial :=
            polynomialEquality ▸ headCertificate
          exact transported.mul tailCertificate

/-- Multiply all local squarefree-factor bounds into one positive lower bound
for the decomposition product away from every aligned neighborhood. -/
def guardFactorProductAwayCertificate
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box)
    (empty : CCLBranchEvent.EventGuardCell.relevantCurveEvents
      sourceCell.item.cell = [])
    (clearedNonzero :
      (clearedReal p sourceCell.partition.entry.chart.path).isZero = false ∨
      (clearedImag p
        sourceCell.partition.entry.chart.path).isZero = false)
    (determinantNonzero : determinant
      sourceCell.partition.entry.source.matrix ≠ 0) :
    GuardAwayCertificate sourceCell
      (alignedIrrelevantEventNeighborhoodsOfCellEmpty sourceCell empty
        clearedNonzero determinantNonzero)
      (factorProduct sourceCell.item.decomposition.factors) :=
  guardFactorProductAwayCertificateAux sourceCell empty clearedNonzero
    determinantNonzero sourceCell.item.cell.cell.leaves (fun entry => entry)
      (fun _entry => rfl) (fun _entry member => member)

/-- Restore the nonzero decomposition scalar to obtain a bound for the whole
combined arc guard away from all aligned event neighborhoods. -/
def guardArcAwayCertificate
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box)
    (empty : CCLBranchEvent.EventGuardCell.relevantCurveEvents
      sourceCell.item.cell = [])
    (clearedNonzero :
      (clearedReal p sourceCell.partition.entry.chart.path).isZero = false ∨
      (clearedImag p
        sourceCell.partition.entry.chart.path).isZero = false)
    (determinantNonzero : determinant
      sourceCell.partition.entry.source.matrix ≠ 0) :
    GuardAwayCertificate sourceCell
      (alignedIrrelevantEventNeighborhoodsOfCellEmpty sourceCell empty
        clearedNonzero determinantNonzero)
      (arcGuard p sourceCell.partition.entry.chart.path box) := by
  let productCertificate := guardFactorProductAwayCertificate sourceCell empty
    clearedNonzero determinantNonzero
  let scalar := sourceCell.item.decomposition.scalar
  exact
    { bound := scalar ^ 2 * productCertificate.bound
      positive := mul_pos (sq_pos_of_ne_zero
        sourceCell.item.decomposition.scalar_ne_zero)
          productCertificate.positive
      lower := by
        intro t lower upper away
        rw [sourceCell.item.decomposition.eval_identity, mul_pow]
        exact mul_le_mul_of_nonneg_left
          (productCertificate.lower lower upper away) (sq_nonneg scalar) }

/-- Divide the away-bound for the complete nonzero arc product by a uniform
upper bound for all other arc-polynomial factors.  This yields a positive
away-bound for the cleared-coordinate common factor itself. -/
def guardCommonFactorAwayCertificate
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box)
    (empty : CCLBranchEvent.EventGuardCell.relevantCurveEvents
      sourceCell.item.cell = [])
    (clearedNonzero :
      (clearedReal p sourceCell.partition.entry.chart.path).isZero = false ∨
      (clearedImag p
        sourceCell.partition.entry.chart.path).isZero = false)
    (determinantNonzero : determinant
      sourceCell.partition.entry.source.matrix ≠ 0) :
    GuardAwayCertificate sourceCell
      (alignedIrrelevantEventNeighborhoodsOfCellEmpty sourceCell empty
        clearedNonzero determinantNonzero)
      (PathClearance.commonFactor
        (clearedReal p sourceCell.partition.entry.chart.path)
        (clearedImag p sourceCell.partition.entry.chart.path)) := by
  let path := sourceCell.partition.entry.chart.path
  let target := PathClearance.commonFactor (clearedReal p path)
    (clearedImag p path)
  let polynomials := arcPolynomials p path box
  let interval := sourceCell.item.cell.cell.interval
  let guardCertificate := guardArcAwayCertificate sourceCell empty
    clearedNonzero determinantNonzero
  let majorant := erasedProductSqMajorant polynomials target interval
  have targetMember : target ∈ polynomials := by
    exact commonFactor_mem_arcPolynomials p path box
  have targetNonzero : target.isZero = false :=
    PathClearance.commonFactor_isZero_false clearedNonzero
  exact
    { bound := guardCertificate.bound / majorant
      positive := div_pos guardCertificate.positive
        (erasedProductSqMajorant_pos polynomials target interval)
      lower := by
        intro t lower upper away
        let remainder := FTA.CauchyProduct.nonzeroPolynomialProduct
          (polynomials.erase target)
        have guardLower := guardCertificate.lower lower upper away
        have productIdentity := nonzeroPolynomialProduct_eval_eq_mul_erase
          polynomials target targetMember targetNonzero t
        have remainderUpper : remainder.eval t ^ 2 ≤ majorant := by
          exact erasedProduct_eval_sq_le_majorant polynomials target interval
            lower upper
        have targetNonnegative : 0 ≤ target.eval t ^ 2 := sq_nonneg _
        have guardIdentity :
            (arcGuard p path box).eval t =
              target.eval t * remainder.eval t := by
          simpa only [arcGuard, polynomials, remainder] using productIdentity
        have scaled : guardCertificate.bound ≤
            target.eval t ^ 2 * majorant := by
          calc
            guardCertificate.bound ≤
                target.eval t ^ 2 * remainder.eval t ^ 2 := by
              rw [← mul_pow, ← guardIdentity]
              exact guardLower
            _ ≤ target.eval t ^ 2 * majorant :=
              mul_le_mul_of_nonneg_left remainderUpper targetNonnegative
        apply (div_le_iff₀
          (erasedProductSqMajorant_pos polynomials target interval)).2
        simpa only [majorant, mul_comm] using scaled }

/-- Affine curve clearance conditional on avoiding every aligned irrelevant
neighborhood.  This is the complement counterpart of each neighborhood's
local `clear` disposition. -/
structure GuardAffineAwayCertificate
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box)
    (neighborhoods :
      List (AlignedSourceIrrelevantEventNeighborhood sourceCell)) where
  bound : ℚ
  positive : 0 < bound
  lower : ∀ {t : ℚ}, sourceCell.item.cell.cell.interval.lower ≤ t →
    t ≤ sourceCell.item.cell.cell.interval.upper →
    (∀ candidate ∈ neighborhoods,
      ¬(candidate.alignment.refined.interval.lower ≤ t ∧
        t ≤ candidate.alignment.refined.interval.upper)) →
    sourceCell.partition.entry.chart.path.denominator.eval
      (FTA.PathPolynomial.ofRat t) ≠ 0 →
      bound ≤ normSq (p.eval
        (sourceCell.partition.entry.chart.path.value t))

/-- The common-factor away-bound, the reduced-pair Bézout identity, and the
projective denominator majorant give a fully affine away-certificate. -/
def guardAffineAwayCertificate
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box)
    (empty : CCLBranchEvent.EventGuardCell.relevantCurveEvents
      sourceCell.item.cell = [])
    (clearedNonzero :
      (clearedReal p sourceCell.partition.entry.chart.path).isZero = false ∨
      (clearedImag p
        sourceCell.partition.entry.chart.path).isZero = false)
    (determinantNonzero : determinant
      sourceCell.partition.entry.source.matrix ≠ 0) :
    GuardAffineAwayCertificate sourceCell
      (alignedIrrelevantEventNeighborhoodsOfCellEmpty sourceCell empty
        clearedNonzero determinantNonzero) := by
  let path := sourceCell.partition.entry.chart.path
  let interval := sourceCell.item.cell.cell.interval
  let P := clearedReal p path
  let Q := clearedImag p path
  let g := PathClearance.commonFactor P Q
  let P₁ := PathClearance.reducedReal P Q
  let Q₁ := PathClearance.reducedImag P Q
  let coprime := PathClearance.reducedPairCertificate P Q clearedNonzero
  let commonCertificate := guardCommonFactorAwayCertificate sourceCell empty
    clearedNonzero determinantNonzero
  let bezoutMajorant := PathClearance.bezoutNormMajorant coprime interval
  let clearedBound := commonCertificate.bound / bezoutMajorant
  let denominatorMajorant := denominatorNormMajorant p path interval
  exact
    { bound := clearedBound / denominatorMajorant
      positive := div_pos
        (div_pos commonCertificate.positive
          (PathClearance.bezoutNormMajorant_pos coprime interval))
        (denominatorNormMajorant_pos p path interval)
      lower := by
        intro t lower upper away denominatorNonzero
        let S := P₁.eval t ^ 2 + Q₁.eval t ^ 2
        have hS : 0 ≤ S := add_nonneg (sq_nonneg _) (sq_nonneg _)
        have hcoefficients :
            coprime.left.eval t ^ 2 + coprime.right.eval t ^ 2 ≤
              bezoutMajorant := by
          exact PathClearance.bezout_eval_sq_add_le_majorant coprime interval
            lower upper
        have hbezout : coprime.left.eval t * P₁.eval t +
            coprime.right.eval t * Q₁.eval t = 1 := coprime.identity t
        have hunit : 1 ≤ bezoutMajorant * S := by
          have sumOfSquares : 1 ≤
              (coprime.left.eval t ^ 2 + coprime.right.eval t ^ 2) * S := by
            calc
              1 = (coprime.left.eval t * P₁.eval t +
                  coprime.right.eval t * Q₁.eval t) ^ 2 := by
                rw [hbezout]
                norm_num
              _ ≤ (coprime.left.eval t ^ 2 +
                    coprime.right.eval t ^ 2) * S := by
                nlinarith [sq_nonneg
                  (coprime.left.eval t * Q₁.eval t -
                    coprime.right.eval t * P₁.eval t)]
          exact sumOfSquares.trans
            (mul_le_mul_of_nonneg_right hcoefficients hS)
        have commonLower := commonCertificate.lower lower upper away
        have realIdentity : P.eval t = g.eval t * P₁.eval t := by
          simpa only [g, P, Q, P₁] using
            PathClearance.commonFactor_mul_reducedReal_eval P Q t
        have imagIdentity : Q.eval t = g.eval t * Q₁.eval t := by
          simpa only [g, P, Q, Q₁] using
            PathClearance.commonFactor_mul_reducedImag_eval P Q t
        have commonScaled : g.eval t ^ 2 ≤
            bezoutMajorant * (g.eval t ^ 2 * S) := by
          have scaled := mul_le_mul_of_nonneg_left hunit (sq_nonneg (g.eval t))
          nlinarith
        have clearedLower : clearedBound ≤ P.eval t ^ 2 + Q.eval t ^ 2 := by
          apply (div_le_iff₀
            (PathClearance.bezoutNormMajorant_pos coprime interval)).2
          calc
            commonCertificate.bound ≤ g.eval t ^ 2 := commonLower
            _ ≤ bezoutMajorant * (g.eval t ^ 2 * S) := commonScaled
            _ = (P.eval t ^ 2 + Q.eval t ^ 2) * bezoutMajorant := by
              rw [realIdentity, imagIdentity]
              dsimp only [S]
              ring
        have denominatorPower :=
          normSq_clearedDenominatorPower_le_majorant p path interval
            lower upper
        have valueNonnegative : 0 ≤ normSq (p.eval (path.value t)) :=
          normSq_nonneg _
        have scaledAffine : clearedBound ≤
            denominatorMajorant * normSq (p.eval (path.value t)) := by
          rw [ProjectivePath.eval_cleared_normSq p path t denominatorNonzero]
            at clearedLower
          exact clearedLower.trans
            (mul_le_mul_of_nonneg_right denominatorPower valueNonnegative)
        apply (div_le_iff₀
          (denominatorNormMajorant_pos p path interval)).2
        calc
          clearedBound ≤ denominatorMajorant *
              normSq (p.eval (path.value t)) := scaledAffine
          _ = normSq (p.eval (path.value t)) * denominatorMajorant := by
            ring }

/-- The positive contribution used in the finite minimum for one aligned
neighborhood.  Outside dispositions need no curve bound, so they contribute
the harmless positive default `1`. -/
def AlignedSourceIrrelevantEventNeighborhood.dispositionBound
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCell : SourceEventGuardCell p box}
    (candidate : AlignedSourceIrrelevantEventNeighborhood sourceCell) : ℚ :=
  match candidate.disposition with
  | .clear certificate => certificate.bound
  | .outside _excludes => 1

theorem AlignedSourceIrrelevantEventNeighborhood.dispositionBound_pos
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCell : SourceEventGuardCell p box}
    (candidate : AlignedSourceIrrelevantEventNeighborhood sourceCell) :
    0 < candidate.dispositionBound := by
  unfold AlignedSourceIrrelevantEventNeighborhood.dispositionBound
  generalize candidate.disposition = disposition
  cases disposition with
  | clear certificate => exact certificate.positive
  | outside excludes => exact zero_lt_one

/-- Bounds from all local neighborhood dispositions. -/
def alignedDispositionBounds
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCell : SourceEventGuardCell p box}
    (neighborhoods :
      List (AlignedSourceIrrelevantEventNeighborhood sourceCell)) : List ℚ :=
  neighborhoods.map fun candidate => candidate.dispositionBound

/-- The exact clearance needed by boundary exclusion: every affine path point
that lies in the active box has positive curve value.  Pole and outside-box
neighborhoods discharge their points geometrically; clear neighborhoods and
the finite complement contribute to one positive rational minimum. -/
structure BoxRelevantGuardClearance
    (p : GaussianPolynomial) (box : RatBox)
    (sourceCell : SourceEventGuardCell p box) where
  bound : ℚ
  positive : 0 < bound
  lower : ∀ {t : ℚ}, sourceCell.item.cell.cell.interval.lower ≤ t →
    t ≤ sourceCell.item.cell.cell.interval.upper →
    sourceCell.partition.entry.chart.path.denominator.eval
      (FTA.PathPolynomial.ofRat t) ≠ 0 →
    box.Contains (sourceCell.partition.entry.chart.path.value t) →
      bound ≤ normSq (p.eval
        (sourceCell.partition.entry.chart.path.value t))

/-- Assemble local irrelevant-event dispositions and the computed finite
complement bound into one box-relevant terminal-cell clearance. -/
def boxRelevantGuardClearanceOfCellEmpty
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box)
    (empty : CCLBranchEvent.EventGuardCell.relevantCurveEvents
      sourceCell.item.cell = [])
    (clearedNonzero :
      (clearedReal p sourceCell.partition.entry.chart.path).isZero = false ∨
      (clearedImag p
        sourceCell.partition.entry.chart.path).isZero = false)
    (determinantNonzero : determinant
      sourceCell.partition.entry.source.matrix ≠ 0) :
    BoxRelevantGuardClearance p box sourceCell := by
  let neighborhoods := alignedIrrelevantEventNeighborhoodsOfCellEmpty
    sourceCell empty clearedNonzero determinantNonzero
  let awayCertificate := guardAffineAwayCertificate sourceCell empty
    clearedNonzero determinantNonzero
  let localMinimum := FTA.Maximality.positiveMinimum
    (alignedDispositionBounds neighborhoods)
  let bound := min awayCertificate.bound localMinimum
  have localMinimumPositive : 0 < localMinimum := by
    apply FTA.Maximality.positiveMinimum_pos
    intro value member
    rw [alignedDispositionBounds, List.mem_map] at member
    rcases member with ⟨candidate, _candidateMember, rfl⟩
    exact candidate.dispositionBound_pos
  exact
    { bound := bound
      positive := lt_min awayCertificate.positive localMinimumPositive
      lower := by
        intro t lower upper denominator contains
        by_cases covered : ∃ candidate ∈ neighborhoods,
            candidate.alignment.refined.interval.lower ≤ t ∧
              t ≤ candidate.alignment.refined.interval.upper
        · rcases covered with ⟨candidate, candidateMember,
            candidateLower, candidateUpper⟩
          cases dispositionEquation : candidate.disposition with
          | clear certificate =>
              have localMember : candidate.dispositionBound ∈
                  alignedDispositionBounds neighborhoods :=
                List.mem_map_of_mem candidateMember
              have minimumLe : localMinimum ≤ candidate.dispositionBound :=
                FTA.Maximality.positiveMinimum_le_of_mem localMember
              have boundLe : bound ≤ certificate.bound := by
                apply (min_le_right awayCertificate.bound localMinimum).trans
                simpa only [AlignedSourceIrrelevantEventNeighborhood.dispositionBound,
                  dispositionEquation] using minimumLe
              exact boundLe.trans
                (certificate.lower t candidateLower candidateUpper denominator)
          | outside excludes =>
              exact (excludes candidateLower candidateUpper denominator
                contains).elim
        · have away : ∀ candidate ∈ neighborhoods,
              ¬(candidate.alignment.refined.interval.lower ≤ t ∧
                t ≤ candidate.alignment.refined.interval.upper) := by
            intro candidate candidateMember inside
            exact covered ⟨candidate, candidateMember, inside⟩
          exact (min_le_left awayCertificate.bound localMinimum).trans
            (awayCertificate.lower lower upper away denominator) }

/-- A cell-local relevant event and its source-cell membership produce the
exact source-labelled event used by the guarded parser-owner family. -/
theorem sourceGuardCurveEvent_mem_of_cell_event
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCells : List (SourceEventGuardCell p box)}
    (sourceCell : SourceEventGuardCell p box)
    (sourceMember : sourceCell ∈ sourceCells)
    (event : RelevantCurveEvent p
      sourceCell.partition.entry.chart.path box)
    (eventMember : event ∈
      CCLBranchEvent.EventGuardCell.relevantCurveEvents
        sourceCell.item.cell) :
    let sourceEvent : SourceGuardCurveEvent p box :=
      ⟨sourceCell, event, eventMember⟩
    sourceEvent ∈ guardCurveEventsOfSourceEventGuardCells sourceCells := by
  let sourceEvent : SourceGuardCurveEvent p box :=
    ⟨sourceCell, event, eventMember⟩
  change sourceEvent ∈ guardCurveEventsOfSourceEventGuardCells sourceCells
  rw [guardCurveEventsOfSourceEventGuardCells, List.mem_flatMap]
  refine ⟨sourceCell, sourceMember, ?_⟩
  rw [guardCurveEventsOfSourceEventGuardCell, List.mem_map]
  exact ⟨⟨event, eventMember⟩, by simp, rfl⟩

/-- The two clearance forms consumed by boundary exclusion.  Ordinary clear
cells work on the whole parameter interval; resolved relevance-empty positive
cells need only cover affine path points that lie in the active box. -/
inductive GuardCellClearance
    (p : GaussianPolynomial) (box : RatBox)
    (sourceCell : SourceEventGuardCell p box) where
  | full (evidence : ClearGuardCurveCell p box sourceCell)
  | boxRelevant (evidence : BoxRelevantGuardClearance p box sourceCell)

def GuardCellClearance.bound
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCell : SourceEventGuardCell p box}
    (evidence : GuardCellClearance p box sourceCell) : ℚ :=
  match evidence with
  | .full cell => cell.certificate.bound
  | .boxRelevant relevant => relevant.bound

theorem GuardCellClearance.bound_pos
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCell : SourceEventGuardCell p box}
    (evidence : GuardCellClearance p box sourceCell) :
    0 < evidence.bound := by
  cases evidence with
  | full cell =>
      simpa only [GuardCellClearance.bound] using cell.bound_pos
  | boxRelevant relevant =>
      simpa only [GuardCellClearance.bound] using relevant.positive

theorem GuardCellClearance.lower
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCell : SourceEventGuardCell p box}
    (evidence : GuardCellClearance p box sourceCell)
    {t : ℚ} (lower : sourceCell.item.cell.cell.interval.lower ≤ t)
    (upper : t ≤ sourceCell.item.cell.cell.interval.upper)
    (denominator : sourceCell.partition.entry.chart.path.denominator.eval
      (FTA.PathPolynomial.ofRat t) ≠ 0)
    (contains : box.Contains
      (sourceCell.partition.entry.chart.path.value t)) :
    evidence.bound ≤ normSq
      (p.eval (sourceCell.partition.entry.chart.path.value t)) := by
  cases evidence with
  | full cell =>
      simpa only [GuardCellClearance.bound] using
        cell.certificate.lower t lower upper denominator
  | boxRelevant relevant =>
      simpa only [GuardCellClearance.bound] using
        relevant.lower lower upper denominator contains

/-- One quantitative certificate for every source guard cell in the displayed
order, allowing both whole-cell and box-relevant clearances. -/
inductive AllGuardClear (p : GaussianPolynomial) (box : RatBox) :
    List (SourceEventGuardCell p box) → Type where
  | nil : AllGuardClear p box []
  | cons {sourceCell : SourceEventGuardCell p box}
      {sourceCells : List (SourceEventGuardCell p box)}
      (head : GuardCellClearance p box sourceCell)
      (tail : AllGuardClear p box sourceCells) :
      AllGuardClear p box (sourceCell :: sourceCells)

/-- Recover the clearance attached to one finite source-cell position. -/
def AllGuardClear.get
    {p : GaussianPolynomial} {box : RatBox} :
    {sourceCells : List (SourceEventGuardCell p box)} →
      (evidence : AllGuardClear p box sourceCells) →
      (i : Fin sourceCells.length) →
        GuardCellClearance p box (sourceCells.get i)
  | _ :: _, .cons head tail, i =>
      Fin.cases head (fun j => tail.get j) i

/-- The exact family-level alternative.  A non-clear result retains the
first offending source cell and its membership proof; otherwise every cell
has its quantitative affine clearance. -/
inductive GuardCurveFamilyDecision
    (p : GaussianPolynomial) (box : RatBox) :
    (sourceCells : List (SourceEventGuardCell p box)) → Type where
  | allClear {sourceCells : List (SourceEventGuardCell p box)}
      (evidence : AllGuardClear p box sourceCells) :
      GuardCurveFamilyDecision p box sourceCells
  | identicallyZero {sourceCells : List (SourceEventGuardCell p box)}
      (sourceCell : SourceEventGuardCell p box)
      (member : sourceCell ∈ sourceCells)
      (realZero :
        (clearedReal p
          sourceCell.partition.entry.chart.path).isZero = true)
      (imagZero :
        (clearedImag p
          sourceCell.partition.entry.chart.path).isZero = true)
      (relevance : GuardCellRelevanceDecision p box sourceCell) :
      GuardCurveFamilyDecision p box sourceCells
  | positive {sourceCells : List (SourceEventGuardCell p box)}
      (sourceCell : SourceEventGuardCell p box)
      (member : sourceCell ∈ sourceCells)
      (clearedNonzero :
        (clearedReal p
          sourceCell.partition.entry.chart.path).isZero = false ∨
        (clearedImag p
          sourceCell.partition.entry.chart.path).isZero = false)
      (countPositive : 0 < ProjectivePath.commonFactorRootCount2 p
        sourceCell.partition.entry.chart.path clearedNonzero
        sourceCell.item.cell.cell.interval.lower
        sourceCell.item.cell.cell.interval.upper)
      (event : RelevantCurveEvent p
        sourceCell.partition.entry.chart.path box)
      (eventMember : event ∈
        CCLBranchEvent.EventGuardCell.relevantCurveEvents
          sourceCell.item.cell) :
      GuardCurveFamilyDecision p box sourceCells

/-- Structurally terminating traversal of every terminal guard cell. -/
def decideGuardCurveFamily
    {p : GaussianPolynomial} {box : RatBox} :
    (sourceCells : List (SourceEventGuardCell p box)) →
    (determinants : ∀ sourceCell ∈ sourceCells,
      determinant sourceCell.partition.entry.source.matrix ≠ 0) →
      GuardCurveFamilyDecision p box sourceCells
  | [], _determinants => .allClear .nil
  | sourceCell :: sourceCells, determinants =>
      match decideSourceEventGuardCellCurve sourceCell with
      | GuardCurveDecision.identicallyZero realZero imagZero =>
          .identicallyZero sourceCell (by simp) realZero imagZero
            (decideGuardCellRelevance sourceCell)
      | GuardCurveDecision.positive clearedNonzero countPositive =>
          match decideGuardCellRelevance sourceCell with
          | .relevant event member =>
              .positive sourceCell (by simp) clearedNonzero countPositive
                event member
          | .none empty =>
              let head : GuardCellClearance p box sourceCell :=
                .boxRelevant (boxRelevantGuardClearanceOfCellEmpty sourceCell
                  empty clearedNonzero (determinants sourceCell (by simp)))
              match decideGuardCurveFamily sourceCells (fun candidate member =>
                  determinants candidate (by simp [member])) with
              | .allClear tail => .allClear (.cons head tail)
              | .identicallyZero terminal member realZero imagZero relevance =>
                  .identicallyZero terminal (by simp [member]) realZero
                    imagZero relevance
              | .positive positive member nonzero positiveCount event
                  eventMember =>
                  .positive positive (by simp [member]) nonzero positiveCount
                    event eventMember
      | GuardCurveDecision.clear head =>
          match decideGuardCurveFamily sourceCells (fun candidate member =>
              determinants candidate (by simp [member])) with
          | .allClear tail => .allClear (.cons (.full head) tail)
          | .identicallyZero terminal member realZero imagZero relevance =>
              .identicallyZero terminal (by simp [member]) realZero imagZero
                relevance
          | .positive positive member clearedNonzero countPositive event
              eventMember =>
              .positive positive (by simp [member]) clearedNonzero countPositive
                event eventMember

/-- Apply the same total traversal to the exact guarded family generated by
one denominator-separated parser state. -/
def decideSeparatedGuardCurveFamily
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} (state : RawParser.State)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (stateDeterminant : determinant state.matrix ≠ 0) :
    GuardCurveFamilyDecision p output.state.box
      (separatedEventGuardCells p state output) :=
  decideGuardCurveFamily (separatedEventGuardCells p state output) (by
    intro sourceCell sourceMember
    have partitionMember : sourceCell.partition ∈
        separatedChartPartitions p state output := by
      apply SourceEventGuardCell.partition_mem_of_mem
      simpa only [separatedEventGuardCells] using sourceMember
    have entryMember : sourceCell.partition.entry ∈
        separatedCharts state output := by
      apply SourceChartPartition.entry_mem_of_mem_build
      simpa only [separatedChartPartitions] using partitionMember
    exact separatedChart_determinant_ne stateDeterminant entryMember)

/-- Certificate bounds in the same order as the guarded source cells. -/
def AllGuardClear.bounds
    {p : GaussianPolynomial} {box : RatBox} :
    {sourceCells : List (SourceEventGuardCell p box)} →
      AllGuardClear p box sourceCells → List ℚ
  | [], .nil => []
  | _ :: _, .cons head tail =>
      head.bound :: tail.bounds

/-- A single positive rational clearance shared by the finite guarded
zero-count family, with the standard positive default for an empty list. -/
def AllGuardClear.uniformClearance
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCells : List (SourceEventGuardCell p box)}
    (evidence : AllGuardClear p box sourceCells) : ℚ :=
  FTA.Maximality.positiveMinimum evidence.bounds

theorem AllGuardClear.uniformClearance_pos
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCells : List (SourceEventGuardCell p box)}
    (evidence : AllGuardClear p box sourceCells) :
    0 < evidence.uniformClearance := by
  apply FTA.Maximality.positiveMinimum_pos
  intro value member
  induction evidence with
  | nil => simp [AllGuardClear.bounds] at member
  | cons head tail inductionHypothesis =>
      simp only [AllGuardClear.bounds, List.mem_cons] at member
      rcases member with rfl | tailMember
      · exact head.bound_pos
      · exact inductionHypothesis tailMember

theorem AllGuardClear.bound_mem
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCells : List (SourceEventGuardCell p box)}
    (evidence : AllGuardClear p box sourceCells)
    (i : Fin sourceCells.length) :
    (evidence.get i).bound ∈ evidence.bounds := by
  induction evidence with
  | nil => exact Fin.elim0 i
  | cons head tail inductionHypothesis =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [AllGuardClear.get, AllGuardClear.bounds]
      · simp only [AllGuardClear.get, AllGuardClear.bounds,
          List.mem_cons]
        exact Or.inr (inductionHypothesis j)

theorem AllGuardClear.uniformClearance_le_certificate
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCells : List (SourceEventGuardCell p box)}
    (evidence : AllGuardClear p box sourceCells)
    (i : Fin sourceCells.length) :
    evidence.uniformClearance ≤
      (evidence.get i).bound :=
  FTA.Maximality.positiveMinimum_le_of_mem (evidence.bound_mem i)

/-! ## Quantitative track refinement for an all-clear guard family -/

/-- Spatial request leaving the same fixed slack used by the ordinary
all-interior clearance refinement. -/
def guardSpatialRadius
    (p : GaussianPolynomial) (ambient : RatBox)
    {box : RatBox} {sourceCells : List (SourceEventGuardCell p box)}
    (evidence : AllGuardClear p box sourceCells) : ℚ :=
  min (1 / 2) (evidence.uniformClearance /
    (64 * denseLipschitzBound p (nearbyAmbient ambient)))

theorem guardSpatialRadius_pos
    (p : GaussianPolynomial) (ambient : RatBox)
    {box : RatBox} {sourceCells : List (SourceEventGuardCell p box)}
    (evidence : AllGuardClear p box sourceCells) :
    0 < guardSpatialRadius p ambient evidence := by
  apply lt_min
  · norm_num
  · exact div_pos evidence.uniformClearance_pos
      (mul_pos (by norm_num)
        (denseLipschitzBound_pos p (nearbyAmbient ambient)))

/-- The two finite track calls needed to exploit a shared guard-cell
clearance.  This mirrors the ordinary all-interior refinement but is indexed
by the source guard family, so no artificial boundary arc or denominator
certificate is required. -/
structure GuardRefinementOutput
    (p : GaussianPolynomial) (ambient : RatBox)
    (current : WindingOneState p ambient)
    {box : RatBox} {sourceCells : List (SourceEventGuardCell p box)}
    (evidence : AllGuardClear p box sourceCells) where
  state : WindingOneState p ambient
  refines : state.box.Refines current.box
  epsilon : ℚ
  epsilonPositive : 0 < epsilon
  epsilonAtMostOne : epsilon ≤ 1
  centerResidual :
    normSq (p.eval state.box.center) < evidence.uniformClearance / 8
  distanceBudget :
    denseLipschitzBound p (nearbyAmbient ambient) *
        (2 * (epsilon + state.box.diagonalSq)) <
      evidence.uniformClearance / 8

/-- Precompute and execute the guard-family clearance refinement. -/
def refineForGuardClearance
    {p : GaussianPolynomial} {ambient box : RatBox}
    {sourceCells : List (SourceEventGuardCell p box)}
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient)
    (evidence : AllGuardClear p box sourceCells) :
    GuardRefinementOutput p ambient current evidence := by
  let delta := evidence.uniformClearance
  let L := denseLipschitzBound p (nearbyAmbient ambient)
  let spatial := guardSpatialRadius p ambient evidence
  let spatialPositive := guardSpatialRadius_pos p ambient evidence
  let small := track.refine current spatial spatialPositive
  let threshold := delta / 16
  have deltaPositive : 0 < delta := evidence.uniformClearance_pos
  have thresholdPositive : 0 < threshold :=
    div_pos deltaPositive (by norm_num)
  let residual := residualRefinementRadius p ambient threshold
  let residualPositive := residualRefinementRadius_pos p ambient
    thresholdPositive
  let final := track.refine small residual residualPositive
  let epsilon := spatial ^ 2
  have spatialHalf : spatial ≤ 1 / 2 := min_le_left _ _
  have spatialOne : spatial ≤ 1 := by linarith
  have spatialSqLe : spatial ^ 2 ≤ spatial := by
    nlinarith [mul_nonneg spatialPositive.le (sub_nonneg.mpr spatialOne)]
  have epsilonPositive : 0 < epsilon := sq_pos_of_pos spatialPositive
  have epsilonAtMostOne : epsilon ≤ 1 := spatialSqLe.trans spatialOne
  have finalRefinesSmall : final.box.Refines small.box :=
    track.nested small residual residualPositive
  have smallRefinesCurrent : small.box.Refines current.box :=
    track.nested current spatial spatialPositive
  have finalDiagonal : final.box.diagonalSq ≤ epsilon := by
    apply (RatBox.diagonalSq_le_of_refines finalRefinesSmall).trans
    simpa only [small, epsilon] using
      track.accurate current spatial spatialPositive
  have centerResidualLe :
      normSq (p.eval final.box.center) ≤ threshold := by
    simpa only [residual, residualPositive, final] using
      refined_center_residual_le track small thresholdPositive
  have centerResidual :
      normSq (p.eval final.box.center) < delta / 8 := by
    dsimp only [threshold] at centerResidualLe
    linarith
  have LPositive : 0 < L :=
    denseLipschitzBound_pos p (nearbyAmbient ambient)
  have spatialRatio : spatial ≤ delta / (64 * L) := min_le_right _ _
  have scaledSpatial : 64 * L * spatial ≤ delta := by
    have scaled := (le_div_iff₀
      (mul_pos (by norm_num) LPositive)).mp spatialRatio
    nlinarith
  have distanceBudget :
      L * (2 * (epsilon + final.box.diagonalSq)) < delta / 8 := by
    calc
      L * (2 * (epsilon + final.box.diagonalSq)) ≤
          L * (2 * (epsilon + epsilon)) := by
        apply mul_le_mul_of_nonneg_left _ LPositive.le
        exact mul_le_mul_of_nonneg_left
          (add_le_add le_rfl finalDiagonal) (by norm_num)
      _ = 4 * L * spatial ^ 2 := by
        dsimp only [epsilon]
        ring
      _ ≤ 4 * L * spatial :=
        mul_le_mul_of_nonneg_left spatialSqLe
          (mul_nonneg (by norm_num) LPositive.le)
      _ ≤ delta / 16 := by nlinarith
      _ < delta / 8 := by linarith
  exact
    { state := final
      refines := finalRefinesSmall.trans smallRefinesCurrent
      epsilon := epsilon
      epsilonPositive := epsilonPositive
      epsilonAtMostOne := epsilonAtMostOne
      centerResidual := by
        simpa only [delta, final] using centerResidual
      distanceBudget := by
        simpa only [delta, L, final] using distanceBudget }

/-- A boundary point covered by a quantitatively clear terminal guard cell
cannot remain in the guard-refined winding box.  Unlike the ordinary arc
sampler theorem, the point is already supplied by reverse boundary coverage,
so no projective variation estimate is needed. -/
theorem GuardRefinementOutput.excludes_guard_point
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
    (contains : output.state.box.Contains
      ((sourceCells.get i).partition.entry.chart.path.value t)) : False := by
  let point := (sourceCells.get i).partition.entry.chart.path.value t
  let margin := evidence.uniformClearance
  let L := denseLipschitzBound p (nearbyAmbient ambient)
  have centerInNearby :
      (nearbyAmbient ambient).Contains output.state.box.center :=
    nearbyAmbient_contains
      (output.state.refinesAmbient.contains output.state.box.contains_center)
  have pointInNearby : (nearbyAmbient ambient).Contains point :=
    nearbyAmbient_contains (output.state.refinesAmbient.contains contains)
  have pointDistance :
      normSq (point - output.state.box.center) ≤
        output.state.box.diagonalSq :=
    RatBox.normSq_sub_le_diagonalSq contains output.state.box.contains_center
  have distanceStrict : output.state.box.diagonalSq <
      2 * (output.epsilon + output.state.box.diagonalSq) := by
    have diagonalNonnegative := output.state.box.diagonalSq_nonneg
    nlinarith [output.epsilonPositive]
  have scaledDistance :
      L * normSq (point - output.state.box.center) <
        L * (2 * (output.epsilon + output.state.box.diagonalSq)) := by
    apply mul_lt_mul_of_pos_left
      (pointDistance.trans_lt distanceStrict)
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

end CCLGuardCellClearance
end FTA
