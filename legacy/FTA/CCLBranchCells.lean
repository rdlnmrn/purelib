import FTA.CCLBranchPartition
import FTA.CCLFormulaPath

/-!
# Stable box cells inside guarded CCL branch charts

An all-interior guarded cell carries a positive squared lower bound for every
nonzero box-condition polynomial.  This module converts those bounds into an
explicit common width at which the ordinary midpoint sign classifier must
succeed, performs the required finite subdivision, and filters the resulting
cells by exact closed-box membership.  No square roots or unbounded retries
are used.
-/

namespace FTA
namespace CCLBranchCells

open CCL
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.CCLPathIntersection
open FTA.CCLIntersectionGuard
open FTA.CCLBranchPartition
open FTA.CCLFormulaPath
open FTA.PositiveLowerBound
open FTA.RationalPolynomialBounds
open FTA.SturmTransducer

abbrev GaussianPolynomial := DensePolynomial CCL.GaussianRat
abbrev RatPolynomial := DensePolynomial ℚ
abbrev RationalInterval := FTA.SturmTransducer.RationalInterval

/-- Width resolving one displayed box condition.  Identically zero
conditions are already stable; every nonzero condition uses the quantitative
member certificate extracted from the complete arc guard. -/
def conditionResolution
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    (cell : ClearGuardCell p path box) (polynomial : RatPolynomial)
    (member : polynomial ∈ conditionPolynomials (boxConditions path box)) : ℚ := by
  if zero : polynomial.isZero = true then
    exact 1
  else
    have nonzero : polynomial.isZero = false :=
      Bool.eq_false_of_not_eq_true zero
    exact (cell.memberCertificate polynomial
      (condition_mem_arcPolynomials member) nonzero).signResolution

theorem conditionResolution_pos
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    (cell : ClearGuardCell p path box) (polynomial : RatPolynomial)
    (member : polynomial ∈ conditionPolynomials (boxConditions path box)) :
    0 < conditionResolution cell polynomial member := by
  rw [conditionResolution]
  split
  · exact zero_lt_one
  · exact Certificate.signResolution_pos _

/-- Proof-bearing list of all four condition resolutions. -/
def conditionResolutions
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    (cell : ClearGuardCell p path box) : List ℚ :=
  (conditionPolynomials (boxConditions path box)).attach.map fun item =>
    conditionResolution cell item.1 item.2

/-- One positive common width at which all four box conditions are either
identically zero or midpoint-sign stable. -/
def boxResolution
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    (cell : ClearGuardCell p path box) : ℚ :=
  FTA.Maximality.positiveMinimum (conditionResolutions cell)

theorem boxResolution_pos
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    (cell : ClearGuardCell p path box) : 0 < boxResolution cell := by
  apply FTA.Maximality.positiveMinimum_pos
  intro resolution member
  rw [conditionResolutions, List.mem_map] at member
  rcases member with ⟨item, _itemMember, rfl⟩
  exact conditionResolution_pos cell item.1 item.2

theorem boxResolution_le_condition
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    (cell : ClearGuardCell p path box) (polynomial : RatPolynomial)
    (member : polynomial ∈ conditionPolynomials (boxConditions path box)) :
    boxResolution cell ≤ conditionResolution cell polynomial member := by
  apply FTA.Maximality.positiveMinimum_le_of_mem
  rw [conditionResolutions, List.mem_map]
  exact ⟨⟨polynomial, member⟩, by simp, rfl⟩

/-- On any sufficiently narrow nested interval, one box condition has a
proof-relevant zero-or-strict status. -/
def conditionStatus
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    (cell : ClearGuardCell p path box) (interval : RationalInterval)
    (refines : interval.Refines cell.interval) (proper : interval.Proper)
    (width : interval.width < boxResolution cell)
    (polynomial : RatPolynomial)
    (member : polynomial ∈ conditionPolynomials (boxConditions path box)) :
    PolynomialStatus polynomial interval := by
  if zero : polynomial.isZero = true then
    exact .zero zero
  else
    have nonzero : polynomial.isZero = false :=
      Bool.eq_false_of_not_eq_true zero
    let certificate := cell.memberCertificate polynomial
      (condition_mem_arcPolynomials member) nonzero
    have resolutionLe : boxResolution cell ≤ certificate.signResolution := by
      have := boxResolution_le_condition cell polynomial member
      simpa [conditionResolution, zero, certificate, nonzero] using this
    exact .strict (certificate.midpointSignCertificateOfWidth refines proper
      (width.trans_le resolutionLe))

/-- A nested all-interior cell on which all four closed-box tests have stable
truth values. -/
structure StableBoxCell
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    (parent : ClearGuardCell p path box) where
  interval : RationalInterval
  proper : interval.Proper
  refines : interval.Refines parent.interval
  status : ∀ polynomial ∈ conditionPolynomials (boxConditions path box),
    PolynomialStatus polynomial interval

/-- Construct a stable cell directly from the common quantitative width. -/
def StableBoxCell.ofNarrowInterval
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    (parent : ClearGuardCell p path box) (interval : RationalInterval)
    (refines : interval.Refines parent.interval) (proper : interval.Proper)
    (width : interval.width < boxResolution parent) :
    StableBoxCell parent where
  interval := interval
  proper := proper
  refines := refines
  status := conditionStatus parent interval refines proper width

/-- Retain the complete guard certificate after finite sign subdivision. -/
def StableBoxCell.toClearGuardCell
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {parent : ClearGuardCell p path box} (cell : StableBoxCell parent) :
    ClearGuardCell p path box where
  interval := cell.interval
  proper := cell.proper
  certificate := parent.certificate.restrict cell.interval cell.refines

/-- Every closed-box condition has the same truth value at every two
parameters of a stable cell. -/
theorem StableBoxCell.holdsAt_iff
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {parent : ClearGuardCell p path box} (cell : StableBoxCell parent)
    {s t : ℚ}
    (sLower : cell.interval.lower ≤ s) (sUpper : s ≤ cell.interval.upper)
    (tLower : cell.interval.lower ≤ t) (tUpper : t ≤ cell.interval.upper) :
    (boxConditions path box).HoldsAt s ↔
      (boxConditions path box).HoldsAt t := by
  let conditions := boxConditions path box
  have xLower := (cell.status conditions.xLower (by
    simp [conditionPolynomials, conditions])).holds_iff
      CCLParserGeometry.SignTest.nonnegative
      sLower sUpper tLower tUpper
  have xUpper := (cell.status conditions.xUpper (by
    simp [conditionPolynomials, conditions])).holds_iff
      CCLParserGeometry.SignTest.nonnegative
      sLower sUpper tLower tUpper
  have yLower := (cell.status conditions.yLower (by
    simp [conditionPolynomials, conditions])).holds_iff
      CCLParserGeometry.SignTest.nonnegative
      sLower sUpper tLower tUpper
  have yUpper := (cell.status conditions.yUpper (by
    simp [conditionPolynomials, conditions])).holds_iff
      CCLParserGeometry.SignTest.nonnegative
      sLower sUpper tLower tUpper
  simpa only [conditions, BoxConditions.HoldsAt,
    CCLParserGeometry.SignTest.Holds] using
      and_congr xLower (and_congr xUpper (and_congr yLower yUpper))

/-- Exact sample bit used to retain only stable cells meeting the root box. -/
def StableBoxCell.meetsBox
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {parent : ClearGuardCell p path box} (cell : StableBoxCell parent) : Bool :=
  (boxConditions path box).check
    (midpoint cell.interval.lower cell.interval.upper)

/-- A stable all-interior cell whose complete affine path lies in the closed
box whenever its projective denominator is nonzero. -/
structure RelevantClearCell
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    (parent : ClearGuardCell p path box) where
  cell : StableBoxCell parent
  meets : cell.meetsBox = true

theorem RelevantClearCell.contains
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {parent : ClearGuardCell p path box} (relevant : RelevantClearCell parent)
    (denominatorNonzero : (denominatorNorm path).isZero = false)
    {t : ℚ} (lower : relevant.cell.interval.lower ≤ t)
    (upper : t ≤ relevant.cell.interval.upper) :
    box.Contains (path.value t) := by
  let sample := midpoint relevant.cell.interval.lower relevant.cell.interval.upper
  have sampleLower : relevant.cell.interval.lower ≤ sample :=
    (lower_lt_midpoint relevant.cell.proper).le
  have sampleUpper : sample ≤ relevant.cell.interval.upper :=
    (midpoint_lt_upper relevant.cell.proper).le
  have sampleHolds : (boxConditions path box).HoldsAt sample :=
    (BoxConditions.check_eq_true_iff _ _).mp relevant.meets
  have targetHolds : (boxConditions path box).HoldsAt t :=
    (relevant.cell.holdsAt_iff sampleLower sampleUpper lower upper).mp
      sampleHolds
  let denominator :=
    relevant.cell.toClearGuardCell.denominatorCertificate denominatorNonzero
  exact (contains_value_iff_holdsAt path box t
    (denominator.denominator_ne lower upper)).2 targetHolds

/-! ## Fixed-depth common sign subdivision -/

/-- Explicit natural depth forcing every descendant below the common box
resolution. -/
def boxResolutionDepth
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    (cell : ClearGuardCell p path box) : ℕ :=
  geometricDepth cell.interval.width (boxResolution cell / 2)

theorem boxResolutionDepth_sufficient
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    (cell : ClearGuardCell p path box) :
    (2 / 3 : ℚ) ^ boxResolutionDepth cell * cell.interval.width <
      boxResolution cell := by
  have halfPositive : 0 < boxResolution cell / 2 := by
    linarith [boxResolution_pos cell]
  have bound := geometricDepth_sufficient
    (RationalInterval.width_pos cell.proper).le halfPositive
  calc
    (2 / 3 : ℚ) ^ boxResolutionDepth cell * cell.interval.width ≤
        boxResolution cell / 2 := by
      simpa [boxResolutionDepth] using bound
    _ < boxResolution cell := by linarith [boxResolution_pos cell]

/-- Execute a fixed binary midpoint subdivision and return only terminal
proof-bearing stable cells. -/
def buildStableBoxCells
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    (parent : ClearGuardCell p path box) :
    (fuel : ℕ) → (interval : RationalInterval) →
      interval.Refines parent.interval → interval.Proper →
      (2 / 3 : ℚ) ^ fuel * interval.width < boxResolution parent →
      List (StableBoxCell parent)
  | 0, interval, refines, proper, sufficient =>
      [StableBoxCell.ofNarrowInterval parent interval refines proper (by
        simpa using sufficient)]
  | fuel + 1, interval, refines, proper, sufficient => by
      let cut := midpoint interval.lower interval.upper
      let left := interval.left cut
      let right := interval.right cut
      have lowerLt : interval.lower < cut := lower_lt_midpoint proper
      have ltUpper : cut < interval.upper := midpoint_lt_upper proper
      have leftProper : left.Proper := by
        change interval.lower < cut
        exact lowerLt
      have rightProper : right.Proper := by
        change cut < interval.upper
        exact ltUpper
      have leftRefines : left.Refines parent.interval :=
        RationalInterval.refines_trans
          (by exact ⟨le_rfl, ltUpper.le⟩) refines
      have rightRefines : right.Refines parent.interval :=
        RationalInterval.refines_trans
          (by exact ⟨lowerLt.le, le_rfl⟩) refines
      have leftWidth : left.width < (2 / 3 : ℚ) * interval.width := by
        have widthPositive := RationalInterval.width_pos proper
        dsimp [left, cut, RationalInterval.left, RationalInterval.width,
          RationalPolynomialBounds.midpoint]
        dsimp [RationalInterval.width] at widthPositive
        linarith
      have rightWidth : right.width < (2 / 3 : ℚ) * interval.width := by
        have widthPositive := RationalInterval.width_pos proper
        dsimp [right, cut, RationalInterval.right, RationalInterval.width,
          RationalPolynomialBounds.midpoint]
        dsimp [RationalInterval.width] at widthPositive
        linarith
      have factorPositive : 0 < (2 / 3 : ℚ) ^ fuel := by positivity
      have leftSufficient :
          (2 / 3 : ℚ) ^ fuel * left.width < boxResolution parent := by
        calc
          (2 / 3 : ℚ) ^ fuel * left.width <
              (2 / 3 : ℚ) ^ fuel * ((2 / 3 : ℚ) * interval.width) :=
            mul_lt_mul_of_pos_left leftWidth factorPositive
          _ = (2 / 3 : ℚ) ^ (fuel + 1) * interval.width := by
            rw [pow_succ]
            ring
          _ < boxResolution parent := sufficient
      have rightSufficient :
          (2 / 3 : ℚ) ^ fuel * right.width < boxResolution parent := by
        calc
          (2 / 3 : ℚ) ^ fuel * right.width <
              (2 / 3 : ℚ) ^ fuel * ((2 / 3 : ℚ) * interval.width) :=
            mul_lt_mul_of_pos_left rightWidth factorPositive
          _ = (2 / 3 : ℚ) ^ (fuel + 1) * interval.width := by
            rw [pow_succ]
            ring
          _ < boxResolution parent := sufficient
      exact buildStableBoxCells parent fuel left leftRefines leftProper
          leftSufficient ++
        buildStableBoxCells parent fuel right rightRefines rightProper
          rightSufficient

/-- The fixed-depth subdivision covers every rational parameter of its
parent interval; shared split points may be represented by either child. -/
theorem buildStableBoxCells_cover
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    (parent : ClearGuardCell p path box) (fuel : ℕ)
    (interval : RationalInterval) (refines : interval.Refines parent.interval)
    (proper : interval.Proper)
    (sufficient :
      (2 / 3 : ℚ) ^ fuel * interval.width < boxResolution parent)
    {t : ℚ} (lower : interval.lower ≤ t) (upper : t ≤ interval.upper) :
    ∃ cell ∈ buildStableBoxCells parent fuel interval refines proper sufficient,
      cell.interval.lower ≤ t ∧ t ≤ cell.interval.upper := by
  induction fuel generalizing interval with
  | zero =>
      refine ⟨StableBoxCell.ofNarrowInterval parent interval refines proper
        (by simpa using sufficient), ?_, lower, upper⟩
      simp [buildStableBoxCells]
  | succ fuel inductionHypothesis =>
      let cut := midpoint interval.lower interval.upper
      let left := interval.left cut
      let right := interval.right cut
      have lowerLt : interval.lower < cut := lower_lt_midpoint proper
      have ltUpper : cut < interval.upper := midpoint_lt_upper proper
      have leftProper : left.Proper := by
        change interval.lower < cut
        exact lowerLt
      have rightProper : right.Proper := by
        change cut < interval.upper
        exact ltUpper
      have leftRefines : left.Refines parent.interval :=
        RationalInterval.refines_trans
          (by exact ⟨le_rfl, ltUpper.le⟩) refines
      have rightRefines : right.Refines parent.interval :=
        RationalInterval.refines_trans
          (by exact ⟨lowerLt.le, le_rfl⟩) refines
      have leftWidth : left.width < (2 / 3 : ℚ) * interval.width := by
        have widthPositive := RationalInterval.width_pos proper
        dsimp [left, cut, RationalInterval.left, RationalInterval.width,
          RationalPolynomialBounds.midpoint]
        dsimp [RationalInterval.width] at widthPositive
        linarith
      have rightWidth : right.width < (2 / 3 : ℚ) * interval.width := by
        have widthPositive := RationalInterval.width_pos proper
        dsimp [right, cut, RationalInterval.right, RationalInterval.width,
          RationalPolynomialBounds.midpoint]
        dsimp [RationalInterval.width] at widthPositive
        linarith
      have factorPositive : 0 < (2 / 3 : ℚ) ^ fuel := by positivity
      have leftSufficient :
          (2 / 3 : ℚ) ^ fuel * left.width < boxResolution parent := by
        calc
          (2 / 3 : ℚ) ^ fuel * left.width <
              (2 / 3 : ℚ) ^ fuel * ((2 / 3 : ℚ) * interval.width) :=
            mul_lt_mul_of_pos_left leftWidth factorPositive
          _ = (2 / 3 : ℚ) ^ (fuel + 1) * interval.width := by
            rw [pow_succ]
            ring
          _ < boxResolution parent := sufficient
      have rightSufficient :
          (2 / 3 : ℚ) ^ fuel * right.width < boxResolution parent := by
        calc
          (2 / 3 : ℚ) ^ fuel * right.width <
              (2 / 3 : ℚ) ^ fuel * ((2 / 3 : ℚ) * interval.width) :=
            mul_lt_mul_of_pos_left rightWidth factorPositive
          _ = (2 / 3 : ℚ) ^ (fuel + 1) * interval.width := by
            rw [pow_succ]
            ring
          _ < boxResolution parent := sufficient
      by_cases leftSide : t ≤ cut
      · rcases inductionHypothesis left leftRefines leftProper leftSufficient
          lower leftSide with ⟨cell, member, cellLower, cellUpper⟩
        refine ⟨cell, ?_, cellLower, cellUpper⟩
        simp only [buildStableBoxCells, List.mem_append]
        exact Or.inl member
      · have rightLower : cut ≤ t := (lt_of_not_ge leftSide).le
        rcases inductionHypothesis right rightRefines rightProper rightSufficient
          rightLower upper with ⟨cell, member, cellLower, cellUpper⟩
        refine ⟨cell, ?_, cellLower, cellUpper⟩
        simp only [buildStableBoxCells, List.mem_append]
        exact Or.inr member

/-- Total stable subdivision of one all-interior guard cell. -/
def stableBoxCells
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    (cell : ClearGuardCell p path box) : List (StableBoxCell cell) :=
  buildStableBoxCells cell (boxResolutionDepth cell) cell.interval
    (RationalInterval.refines_refl cell.interval) cell.proper
    (boxResolutionDepth_sufficient cell)

theorem stableBoxCells_cover
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    (cell : ClearGuardCell p path box) {t : ℚ}
    (lower : cell.interval.lower ≤ t) (upper : t ≤ cell.interval.upper) :
    ∃ stable ∈ stableBoxCells cell,
      stable.interval.lower ≤ t ∧ t ≤ stable.interval.upper := by
  exact buildStableBoxCells_cover cell (boxResolutionDepth cell) cell.interval
    (RationalInterval.refines_refl cell.interval) cell.proper
    (boxResolutionDepth_sufficient cell) lower upper

/-- Exact finite filter retaining the stable descendants whose midpoint is
inside the closed box. -/
def relevantClearCells
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    (cell : ClearGuardCell p path box) : List (RelevantClearCell cell) :=
  (stableBoxCells cell).filterMap fun stable =>
    if meets : stable.meetsBox = true then some ⟨stable, meets⟩ else none

/-- Every rational point of an all-interior cell satisfying the four closed
box conditions is covered by a retained relevant stable descendant. -/
theorem relevantClearCells_cover_of_holdsAt
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    (cell : ClearGuardCell p path box) {t : ℚ}
    (lower : cell.interval.lower ≤ t) (upper : t ≤ cell.interval.upper)
    (holds : (boxConditions path box).HoldsAt t) :
    ∃ relevant ∈ relevantClearCells cell,
      relevant.cell.interval.lower ≤ t ∧ t ≤ relevant.cell.interval.upper := by
  rcases stableBoxCells_cover cell lower upper with
    ⟨stable, stableMember, stableLower, stableUpper⟩
  let sample := midpoint stable.interval.lower stable.interval.upper
  have sampleLower : stable.interval.lower ≤ sample :=
    (lower_lt_midpoint stable.proper).le
  have sampleUpper : sample ≤ stable.interval.upper :=
    (midpoint_lt_upper stable.proper).le
  have sampleHolds : (boxConditions path box).HoldsAt sample :=
    (stable.holdsAt_iff stableLower stableUpper sampleLower sampleUpper).mp holds
  have meets : stable.meetsBox = true :=
    (BoxConditions.check_eq_true_iff _ _).mpr sampleHolds
  let relevant : RelevantClearCell cell := ⟨stable, meets⟩
  refine ⟨relevant, ?_, stableLower, stableUpper⟩
  simp [relevantClearCells, relevant, meets, stableMember]

/-! ## Source-labelled finite families -/

/-- Retain the source, bounded-chart, and guarded-partition provenance of one
relevant stable clear cell. -/
structure SourceRelevantClearCell
    (p : GaussianPolynomial) (box : RatBox) where
  sourceCell : SourceClearGuardCell p box
  relevant : RelevantClearCell sourceCell.cell

def relevantClearCellsOfSourceCell
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceClearGuardCell p box) :
    List (SourceRelevantClearCell p box) :=
  (relevantClearCells sourceCell.cell).map fun relevant =>
    ⟨sourceCell, relevant⟩

/-- Flatten the exact relevance filter over every all-interior cell of every
bounded source chart. -/
def relevantClearCellsOfSourcePartitions
    {p : GaussianPolynomial} {box : RatBox}
    (partitions : List (SourceChartPartition p box)) :
    List (SourceRelevantClearCell p box) :=
  (clearGuardCellsOfSourcePartitions partitions).flatMap
    relevantClearCellsOfSourceCell

/-- A rational parameter covered by a labelled clear guard cell and satisfying
the closed box conditions survives both the stable subdivision and relevance
filters, with its exact source partition retained. -/
theorem relevantClearCellsOfSourcePartitions_cover_of_clear
    {p : GaussianPolynomial} {box : RatBox}
    (partitions : List (SourceChartPartition p box))
    (partition : SourceChartPartition p box)
    (partitionMember : partition ∈ partitions)
    (cell : ClearGuardCell p partition.entry.chart.path box)
    (cellMember : cell ∈
      clearGuardCellsOfPlan partition.entry.chart.proper partition.plan)
    {t : ℚ} (lower : cell.interval.lower ≤ t)
    (upper : t ≤ cell.interval.upper)
    (holds : (boxConditions partition.entry.chart.path box).HoldsAt t) :
    ∃ candidate ∈ relevantClearCellsOfSourcePartitions partitions,
      candidate.sourceCell.partition = partition ∧
      candidate.relevant.cell.interval.lower ≤ t ∧
      t ≤ candidate.relevant.cell.interval.upper := by
  rcases relevantClearCells_cover_of_holdsAt cell lower upper holds with
    ⟨relevant, relevantMember, relevantLower, relevantUpper⟩
  let sourceCell : SourceClearGuardCell p box := ⟨partition, cell⟩
  have sourceCellMember : sourceCell ∈
      clearGuardCellsOfSourcePartitions partitions := by
    rw [clearGuardCellsOfSourcePartitions, List.mem_flatMap]
    refine ⟨partition, partitionMember, ?_⟩
    rw [clearGuardCellsOfSourcePartition, List.mem_map]
    exact ⟨cell, cellMember, rfl⟩
  let candidate : SourceRelevantClearCell p box := ⟨sourceCell, relevant⟩
  refine ⟨candidate, ?_, rfl, relevantLower, relevantUpper⟩
  rw [relevantClearCellsOfSourcePartitions, List.mem_flatMap]
  refine ⟨sourceCell, sourceCellMember, ?_⟩
  rw [relevantClearCellsOfSourceCell, List.mem_map]
  exact ⟨relevant, relevantMember, rfl⟩

/-- Relevance subdivision and filtering preserve the originating labelled
clear cell in the flattened source family. -/
theorem SourceRelevantClearCell.sourceCell_mem_of_mem
    {p : GaussianPolynomial} {box : RatBox}
    {partitions : List (SourceChartPartition p box)}
    {candidate : SourceRelevantClearCell p box}
    (member : candidate ∈ relevantClearCellsOfSourcePartitions partitions) :
    candidate.sourceCell ∈ clearGuardCellsOfSourcePartitions partitions := by
  rw [relevantClearCellsOfSourcePartitions, List.mem_flatMap] at member
  rcases member with ⟨sourceCell, sourceCellMember, relevantMember⟩
  rw [relevantClearCellsOfSourceCell, List.mem_map] at relevantMember
  rcases relevantMember with ⟨relevant, _relevantMember, equality⟩
  cases equality
  exact sourceCellMember

end CCLBranchCells
end FTA
