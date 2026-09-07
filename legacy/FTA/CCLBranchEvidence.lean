import FTA.CCLCurveDecision
import FTA.CCLDenominator
import FTA.CCLHermitianBox
import FTA.CCLIntersectionSampler
import FTA.CCLBranchPlan
import FTA.CCLBranchCharts
import FTA.CCLBranchPartition
import FTA.CCLBranchCells
import FTA.CCLBranchEvent
import FTA.CCLBranchOwner

/-!
# Finite evidence for the two CCL branch cases

Theorem 10.2 has two outcomes after decoder-denominator separation.  A
positive root count on a relevant generalized-circle arc assigns the track to
that arc's owner side.  If every relevant count is zero, their clearance
certificates justify refinement until exact Hermitian interval evaluation is
strict on the whole root box.

This module packages both alternatives as finite dependent data.  It also
evaluates the two pulled-back child formulas on a strict cell, returning the
complete truth table.  The later track controller rules out the `ambiguous`
case with parser uniqueness and interprets `terminal` via exact CCL
reconstruction.
-/

namespace FTA
namespace CCLBranchEvidence

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.PathClearance
open FTA.ProjectivePath
open FTA.ProjectivePathBounds
open FTA.CCLGeometry
open FTA.CCLParserGeometry
open FTA.CCLFormulaPullback
open FTA.CCLIntersectionSampler
open FTA.CCLBranchPlan
open FTA.CCLBranchCharts
open FTA.CCLBranchPartition
open FTA.CCLBranchCells
open FTA.CCLBranchEvent
open FTA.CCLBranchOwner
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial := DensePolynomial QI
abbrev RationalInterval := FTA.SturmTransducer.RationalInterval

/-- One relevant parameter cell for a branch-boundary form.  Besides the
finite Sturm input, it records the deterministic equality owner and proves
that the path really lies on the displayed Hermitian boundary. -/
structure BoundaryArc (p : GaussianPolynomial) where
  form : HermitianForm
  owner : Bool
  path : Path
  interval : RationalInterval
  proper : interval.Proper
  clearedNonzero : (clearedReal p path).isZero = false ∨
    (clearedImag p path).isZero = false
  lowerClear :
    (PathClearance.commonFactor (clearedReal p path)
      (clearedImag p path)).eval interval.lower ≠ 0
  upperClear :
    (PathClearance.commonFactor (clearedReal p path)
      (clearedImag p path)).eval interval.upper ≠ 0
  denominator : DenominatorCertificate path interval
  onBoundary : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
    form.eval (path.value t) = 0

/-- Construct a curve-count arc from concrete circle/line provenance.  The
path/form agreement is now generated internally; only the parameter-cell
Sturm and denominator certificates remain as inputs. -/
def BoundaryArc.ofSource
    (p : GaussianPolynomial) (source : BoundarySource) (owner : Bool)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (interval : RationalInterval) (proper : interval.Proper)
    (clearedNonzero :
      (clearedReal p source.path).isZero = false ∨
        (clearedImag p source.path).isZero = false)
    (lowerClear :
      (PathClearance.commonFactor (clearedReal p source.path)
        (clearedImag p source.path)).eval interval.lower ≠ 0)
    (upperClear :
      (PathClearance.commonFactor (clearedReal p source.path)
        (clearedImag p source.path)).eval interval.upper ≠ 0)
    (denominator : DenominatorCertificate source.path interval) :
    BoundaryArc p where
  form := source.form
  owner := owner
  path := source.path
  interval := interval
  proper := proper
  clearedNonzero := clearedNonzero
  lowerClear := lowerClear
  upperClear := upperClear
  denominator := denominator
  onBoundary := by
    intro t lower upper
    exact source.onBoundary t determinantNonzero
      (denominator.denominator_ne lower upper)

/-- Construct a curve-count arc from any member of the finite bounded chart
family, including the reciprocal circle chart. -/
def BoundaryArc.ofChart
    (p : GaussianPolynomial) (source : BoundarySource)
    (chart : BoundedChart source) (owner : Bool)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (clearedNonzero :
      (clearedReal p chart.path).isZero = false ∨
        (clearedImag p chart.path).isZero = false)
    (lowerClear :
      (PathClearance.commonFactor (clearedReal p chart.path)
        (clearedImag p chart.path)).eval chart.interval.lower ≠ 0)
    (upperClear :
      (PathClearance.commonFactor (clearedReal p chart.path)
        (clearedImag p chart.path)).eval chart.interval.upper ≠ 0)
    (denominator : DenominatorCertificate chart.path chart.interval) :
    BoundaryArc p where
  form := source.form
  owner := owner
  path := chart.path
  interval := chart.interval
  proper := chart.proper
  clearedNonzero := clearedNonzero
  lowerClear := lowerClear
  upperClear := upperClear
  denominator := denominator
  onBoundary := by
    intro t _lower _upper
    exact chart.onBoundary determinantNonzero
      (denominator.denominator_ne _lower _upper)

/-- Construct an arc on an arbitrary certified subcell of a bounded chart. -/
def BoundaryArc.ofChartCell
    (p : GaussianPolynomial) (source : BoundarySource)
    (chart : BoundedChart source) (owner : Bool)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (interval : RationalInterval) (proper : interval.Proper)
    (clearedNonzero :
      (clearedReal p chart.path).isZero = false ∨
        (clearedImag p chart.path).isZero = false)
    (lowerClear :
      (PathClearance.commonFactor (clearedReal p chart.path)
        (clearedImag p chart.path)).eval interval.lower ≠ 0)
    (upperClear :
      (PathClearance.commonFactor (clearedReal p chart.path)
        (clearedImag p chart.path)).eval interval.upper ≠ 0)
    (denominator : DenominatorCertificate chart.path interval) :
    BoundaryArc p where
  form := source.form
  owner := owner
  path := chart.path
  interval := interval
  proper := proper
  clearedNonzero := clearedNonzero
  lowerClear := lowerClear
  upperClear := upperClear
  denominator := denominator
  onBoundary := by
    intro t lower upper
    exact chart.onBoundary determinantNonzero
      (denominator.denominator_ne lower upper)

/-- Turn a source-labelled relevant all-interior cell into the existing
boundary-arc record.  Equality ownership is supplied separately because it
depends on the parser formula's other active boundaries. -/
def BoundaryArc.ofRelevantClearCell
    {p : GaussianPolynomial} {box : RatBox}
    (candidate : SourceRelevantClearCell p box) (owner : Bool)
    (determinantNonzero : determinant
      candidate.sourceCell.partition.entry.source.matrix ≠ 0)
    (nondegenerate :
      candidate.sourceCell.partition.entry.source.ParametrizationNondegenerate)
    (clearedNonzero :
      (clearedReal p
        candidate.sourceCell.partition.entry.chart.path).isZero = false ∨
      (clearedImag p
        candidate.sourceCell.partition.entry.chart.path).isZero = false) :
    BoundaryArc p := by
  let entry := candidate.sourceCell.partition.entry
  let clear := candidate.relevant.cell.toClearGuardCell
  have denominatorNonzero := entry.chart.denominatorNorm_isZero_false
    determinantNonzero nondegenerate
  let common := PathClearance.commonFactor
    (clearedReal p entry.chart.path) (clearedImag p entry.chart.path)
  have commonNonzero : common.isZero = false :=
    PathClearance.commonFactor_isZero_false clearedNonzero
  let commonCertificate := clear.memberCertificate common
    (commonFactor_mem_arcPolynomials p entry.chart.path box) commonNonzero
  exact BoundaryArc.ofChartCell p entry.source entry.chart owner
    determinantNonzero clear.interval clear.proper clearedNonzero
    (commonCertificate.eval_ne_zero le_rfl clear.proper.le)
    (commonCertificate.eval_ne_zero clear.proper.le le_rfl)
    (clear.denominatorCertificate denominatorNonzero)

/-- A constructed boundary arc together with the affine clearance and exact
source-cell provenance available from its all-interior guard cell. -/
structure ClearBoundaryArc
    (p : GaussianPolynomial) {box : RatBox}
    (candidate : SourceRelevantClearCell p box) where
  arc : BoundaryArc p
  form_eq : arc.form = candidate.sourceCell.partition.entry.source.form
  path_eq : arc.path = candidate.sourceCell.partition.entry.chart.path
  interval_eq : arc.interval = candidate.relevant.cell.interval
  certificate : AffineCertificate p arc.path arc.interval

/-- Total cleared-coordinate outcome for one relevant all-interior cell.
Identically zero cleared coordinates expose an exact rational root at the
midpoint; otherwise the result is a proof-bearing clear boundary arc. -/
inductive RelevantClearCellOutcome
    (p : GaussianPolynomial) (box : RatBox)
    (candidate : SourceRelevantClearCell p box) where
  | terminal (point : QI) (contains : box.Contains point)
      (root : p.eval point = 0)
  | clear (result : ClearBoundaryArc p candidate)

def decideRelevantClearCell
    {p : GaussianPolynomial} {box : RatBox}
    (candidate : SourceRelevantClearCell p box) (owner : Bool)
    (determinantNonzero : determinant
      candidate.sourceCell.partition.entry.source.matrix ≠ 0)
    (nondegenerate :
      candidate.sourceCell.partition.entry.source.ParametrizationNondegenerate) :
    RelevantClearCellOutcome p box candidate := by
  let entry := candidate.sourceCell.partition.entry
  let clear := candidate.relevant.cell.toClearGuardCell
  have denominatorNonzero := entry.chart.denominatorNorm_isZero_false
    determinantNonzero nondegenerate
  let denominator := clear.denominatorCertificate denominatorNonzero
  match coordinateDecision :
      ProjectivePath.decideClearedCoordinates p entry.chart.path with
  | .identicallyZero realZero imagZero =>
      let parameter := FTA.RationalPolynomialBounds.midpoint
        clear.interval.lower clear.interval.upper
      have lower : clear.interval.lower ≤ parameter :=
        (FTA.RationalPolynomialBounds.lower_lt_midpoint clear.proper).le
      have upper : parameter ≤ clear.interval.upper :=
        (FTA.RationalPolynomialBounds.midpoint_lt_upper clear.proper).le
      let point := entry.chart.path.value parameter
      exact .terminal point
        (candidate.relevant.contains denominatorNonzero lower upper)
        (ProjectivePath.eval_eq_zero_of_cleared_isZero p entry.chart.path
          parameter (denominator.denominator_ne lower upper)
          realZero imagZero)
  | .nonzero clearedNonzero =>
      let arc := BoundaryArc.ofRelevantClearCell candidate owner
        determinantNonzero nondegenerate clearedNonzero
      exact .clear
        { arc := arc
          form_eq := by rfl
          path_eq := by rfl
          interval_eq := by rfl
          certificate := by
            change AffineCertificate p entry.chart.path clear.interval
            exact clear.affineCertificate clearedNonzero }

/-! ## Parser-certified owner cells -/

/-- One point of a planned parameter cell witnessing the current parser state
in inverse-decoder coordinates. -/
structure ArcStateWitness
    (state : RawParser.State) (source : BoundarySource)
    (interval : RationalInterval) where
  parameter : ℚ
  lower : interval.lower ≤ parameter
  upper : parameter ≤ interval.upper
  inverseDenominator :
    (adjugate state.matrix).c * source.path.value parameter +
      (adjugate state.matrix).d ≠ 0
  holds : state.Holds
    (RatBox.homographic (adjugate state.matrix)
      (source.path.value parameter))

/-- Stable cell outcomes after parser uniqueness removes the impossible
two-owner case. -/
inductive ResolvedInputCellDecision
    (state : RawParser.State) (source : BoundarySource)
    (interval : RationalInterval) where
  | irrelevant
      (none : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
        ∀ bit, ¬(inputAdvanceFormula state bit).Holds (source.path.value t))
  | owner (bit : Bool)
      (holds : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
        (inputAdvanceFormula state bit).Holds (source.path.value t))
      (otherFails : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
        ¬(inputAdvanceFormula state (!bit)).Holds (source.path.value t))

/-- A relevant planned arc has at most one equality owner. -/
def resolveInputCellDecision
    (state : RawParser.State) (source : BoundarySource)
    (interval : RationalInterval)
    (determinantNonzero : determinant state.matrix ≠ 0)
    (witness : ArcStateWitness state source interval)
    (decision : InputCellDecision state source interval) :
    ResolvedInputCellDecision state source interval :=
  match decision with
  | .irrelevant noChild => .irrelevant noChild
  | .owner bit holds otherFails => .owner bit holds otherFails
  | .ambiguous falseHolds trueHolds => by
      have impossible : false = true :=
        inputAdvanceFormula_unique state
          (source.path.value witness.parameter) determinantNonzero
          witness.inverseDenominator witness.holds
          (falseHolds witness.lower witness.upper)
          (trueHolds witness.lower witness.upper)
      exact (Bool.false_ne_true impossible).elim

/-- Run the exact zero-or-positive curve count for one relevant arc. -/
def BoundaryArc.decide {p : GaussianPolynomial} (arc : BoundaryArc p) :
    CCLCurveDecision.Decision p arc.path arc.clearedNonzero arc.interval :=
  CCLCurveDecision.decide p arc.path arc.clearedNonzero arc.interval
    arc.proper arc.lowerClear arc.upperClear

/-- A positive-count arc, retaining its equality-owner bit and boundary
identification rather than only the bare integer inequality. -/
structure PositiveEvidence
    (p : GaussianPolynomial) (arc : BoundaryArc p) where
  positive : 0 < ProjectivePath.commonFactorRootCount2 p arc.path
    arc.clearedNonzero arc.interval.lower arc.interval.upper

/-- A zero-count arc with the affine clearance certificate obtained after
dividing the cleared projective expression by its denominator bound. -/
structure ClearEvidence
    (p : GaussianPolynomial) (arc : BoundaryArc p) where
  certificate : AffineCertificate p arc.path arc.interval

/-- Existing clearance record obtained by forgetting the boundary owner and
Hermitian-form metadata. -/
def ClearEvidence.toClearArc
    {p : GaussianPolynomial} {arc : BoundaryArc p}
    (evidence : ClearEvidence p arc) : CCLCurveDecision.ClearArc p where
  path := arc.path
  interval := arc.interval
  certificate := evidence.certificate

/-- Exact alternative for one relevant boundary arc. -/
inductive ArcDecision (p : GaussianPolynomial) (arc : BoundaryArc p) where
  | clear (evidence : ClearEvidence p arc)
  | positive (evidence : PositiveEvidence p arc)

/-- Preserve the boundary metadata while exposing the existing finite curve
decision. -/
def decideArc {p : GaussianPolynomial} (arc : BoundaryArc p) :
    ArcDecision p arc :=
  match arc.decide with
  | .clear certificate => .clear ⟨certificate⟩
  | .positiveCount positive => .positive ⟨positive⟩

/-- Proof-bearing zero counts for every arc in an ordered finite family. -/
inductive AllClear (p : GaussianPolynomial) :
    List (BoundaryArc p) → Type where
  | nil : AllClear p []
  | cons {arc : BoundaryArc p} {arcs : List (BoundaryArc p)}
      (head : ClearEvidence p arc) (tail : AllClear p arcs) :
      AllClear p (arc :: arcs)

/-- Forget boundary labels and expose the clearance list consumed by the
uniform positive-minimum construction. -/
def AllClear.clearArcs {p : GaussianPolynomial} :
    {arcs : List (BoundaryArc p)} → AllClear p arcs →
      List (CCLCurveDecision.ClearArc p)
  | [], .nil => []
  | _ :: _, .cons head tail =>
      head.toClearArc :: tail.clearArcs

/-- Recover the clearance evidence at a finite position in the aligned source
arc list. -/
def AllClear.get {p : GaussianPolynomial} :
    {arcs : List (BoundaryArc p)} → (evidence : AllClear p arcs) →
      (i : Fin arcs.length) → ClearEvidence p (arcs.get i)
  | _ :: _, .cons head tail, i =>
      Fin.cases head (fun j => tail.get j) i

@[simp] theorem AllClear.clearArcs_length
    {p : GaussianPolynomial} {arcs : List (BoundaryArc p)}
    (evidence : AllClear p arcs) : evidence.clearArcs.length = arcs.length := by
  induction evidence with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [clearArcs, inductionHypothesis]

/-- A finite family either has a first positive-count arc or carries a
clearance certificate for every member. -/
inductive FamilyDecision
    (p : GaussianPolynomial) (arcs : List (BoundaryArc p)) where
  | allClear (evidence : AllClear p arcs)
  | positive (arc : BoundaryArc p) (member : arc ∈ arcs)
      (evidence : PositiveEvidence p arc)

/-- Terminating list traversal of all exact curve decisions. -/
def decideFamily (p : GaussianPolynomial) :
    (arcs : List (BoundaryArc p)) → FamilyDecision p arcs
  | [] => .allClear .nil
  | arc :: arcs =>
      match decideArc arc with
      | .positive evidence => .positive arc (by simp) evidence
      | .clear head =>
          match decideFamily p arcs with
          | .allClear tail => .allClear (.cons head tail)
          | .positive positiveArc member evidence =>
              .positive positiveArc (by simp [member]) evidence

/-- The common positive clearance attached to an all-clear family. -/
def AllClear.uniformClearance
    {p : GaussianPolynomial} {arcs : List (BoundaryArc p)}
    (evidence : AllClear p arcs) : ℚ :=
  CCLCurveDecision.uniformClearance evidence.clearArcs

theorem AllClear.uniformClearance_pos
    {p : GaussianPolynomial} {arcs : List (BoundaryArc p)}
    (evidence : AllClear p arcs) : 0 < evidence.uniformClearance :=
  CCLCurveDecision.uniformClearance_pos evidence.clearArcs

theorem AllClear.uniformClearance_le_certificate
    {p : GaussianPolynomial} {arcs : List (BoundaryArc p)}
    (evidence : AllClear p arcs) (i : Fin arcs.length) :
    evidence.uniformClearance ≤ (evidence.get i).certificate.bound := by
  induction evidence with
  | nil => exact Fin.elim0 i
  | cons head tail inductionHypothesis =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (inductionHypothesis j)

/-! ## Whole-cell decision for the two pulled-back child formulas -/

/-- Exact result of strict interval evaluation of both proposed child
formulas.  `unresolved` means that at least one atom enclosure still meets
zero.  Every other constructor gives the truth value throughout the box. -/
inductive CellOutcome (state : RawParser.State) (box : RatBox) where
  | unresolved
  | terminal
      (falseStrict : CCLHermitianBox.Formula.strictOnBox
        (inputAdvanceFormula state false) box = true)
      (trueStrict : CCLHermitianBox.Formula.strictOnBox
        (inputAdvanceFormula state true) box = true)
      (none : ∀ {input : QI}, box.Contains input →
        ∀ bit, ¬(inputAdvanceFormula state bit).Holds input)
  | next (bit : Bool)
      (selectedStrict : CCLHermitianBox.Formula.strictOnBox
        (inputAdvanceFormula state bit) box = true)
      (otherStrict : CCLHermitianBox.Formula.strictOnBox
        (inputAdvanceFormula state (!bit)) box = true)
      (holds : ∀ {input : QI}, box.Contains input →
        (inputAdvanceFormula state bit).Holds input)
      (otherFails : ∀ {input : QI}, box.Contains input →
        ¬(inputAdvanceFormula state (!bit)).Holds input)
  | ambiguous
      (falseStrict : CCLHermitianBox.Formula.strictOnBox
        (inputAdvanceFormula state false) box = true)
      (trueStrict : CCLHermitianBox.Formula.strictOnBox
        (inputAdvanceFormula state true) box = true)
      (falseHolds : ∀ {input : QI}, box.Contains input →
        (inputAdvanceFormula state false).Holds input)
      (trueHolds : ∀ {input : QI}, box.Contains input →
        (inputAdvanceFormula state true).Holds input)

private theorem false_of_characterized_false
    {formula : Formula} {box : RatBox}
    (characterization : ∀ {z : QI}, box.Contains z →
      (formula.Holds z ↔ false = true))
    {z : QI} (hz : box.Contains z) : ¬formula.Holds z := by
  intro holds
  have impossible := (characterization hz).mp holds
  contradiction

private theorem true_of_characterized_true
    {formula : Formula} {box : RatBox}
    (characterization : ∀ {z : QI}, box.Contains z →
      (formula.Holds z ↔ true = true))
    {z : QI} (hz : box.Contains z) : formula.Holds z :=
  (characterization hz).mpr rfl

/-- Evaluate both formulas by exact rational box arithmetic. -/
def decideCell (state : RawParser.State) (box : RatBox) :
    CellOutcome state box :=
  match CCLHermitianBox.Formula.decideCell
      (inputAdvanceFormula state false) box,
    CCLHermitianBox.Formula.decideCell
      (inputAdvanceFormula state true) box with
  | .unresolved, _ | _, .unresolved => .unresolved
  | .stable false falseStrict falseCharacterization,
      .stable false trueStrict trueCharacterization =>
      .terminal falseStrict trueStrict (by
        intro input inputInBox bit
        cases bit
        · exact false_of_characterized_false falseCharacterization inputInBox
        · exact false_of_characterized_false trueCharacterization inputInBox)
  | .stable true falseStrict falseCharacterization,
      .stable false trueStrict trueCharacterization =>
      .next false falseStrict (by simpa using trueStrict)
        (true_of_characterized_true falseCharacterization)
        (fun {input : QI} (inputInBox : box.Contains input) => by
          simpa using false_of_characterized_false
            trueCharacterization inputInBox)
  | .stable false falseStrict falseCharacterization,
      .stable true trueStrict trueCharacterization =>
      .next true trueStrict (by simpa using falseStrict)
        (true_of_characterized_true trueCharacterization)
        (fun {input : QI} (inputInBox : box.Contains input) => by
          simpa using false_of_characterized_false
            falseCharacterization inputInBox)
  | .stable true falseStrict falseCharacterization,
      .stable true trueStrict trueCharacterization =>
      .ambiguous falseStrict trueStrict
        (true_of_characterized_true falseCharacterization)
        (true_of_characterized_true trueCharacterization)

/-! ## Parser uniqueness and denominator composition -/

/-- A rational point in the cell witnessing the current parser predicate in
inverse-decoder coordinates.  The denominator field is kept explicit so the
same record also applies outside the track controller. -/
structure CellWitness (state : RawParser.State) (box : RatBox) where
  input : QI
  contains : box.Contains input
  inverseDenominator :
    (adjugate state.matrix).c * input + (adjugate state.matrix).d ≠ 0
  holds : state.Holds
    (RatBox.homographic (adjugate state.matrix) input)

/-- The exact cell outcomes after pointwise parser uniqueness removes the
formally possible `ambiguous` truth table. -/
inductive ResolvedCellOutcome (state : RawParser.State) (box : RatBox) where
  | unresolved
  | terminal
      (falseStrict : CCLHermitianBox.Formula.strictOnBox
        (inputAdvanceFormula state false) box = true)
      (trueStrict : CCLHermitianBox.Formula.strictOnBox
        (inputAdvanceFormula state true) box = true)
      (none : ∀ {input : QI}, box.Contains input →
        ∀ bit, ¬(inputAdvanceFormula state bit).Holds input)
  | next (bit : Bool)
      (selectedStrict : CCLHermitianBox.Formula.strictOnBox
        (inputAdvanceFormula state bit) box = true)
      (otherStrict : CCLHermitianBox.Formula.strictOnBox
        (inputAdvanceFormula state (!bit)) box = true)
      (holds : ∀ {input : QI}, box.Contains input →
        (inputAdvanceFormula state bit).Holds input)
      (otherFails : ∀ {input : QI}, box.Contains input →
        ¬(inputAdvanceFormula state (!bit)).Holds input)

/-- The two child formulas cannot both hold throughout a cell containing a
current-state witness. -/
def resolveCell
    (state : RawParser.State) (box : RatBox)
    (determinantNonzero : determinant state.matrix ≠ 0)
    (witness : CellWitness state box) : ResolvedCellOutcome state box :=
  match decideCell state box with
  | .unresolved => ResolvedCellOutcome.unresolved
  | .terminal falseStrict trueStrict noChild =>
      ResolvedCellOutcome.terminal falseStrict trueStrict noChild
  | .next bit selectedStrict otherStrict holds otherFails =>
      ResolvedCellOutcome.next bit selectedStrict otherStrict holds otherFails
  | .ambiguous _falseStrict _trueStrict falseHolds trueHolds => by
      have impossible : false = true :=
        inputAdvanceFormula_unique state witness.input determinantNonzero
          witness.inverseDenominator witness.holds
          (falseHolds witness.contains) (trueHolds witness.contains)
      exact (Bool.false_ne_true impossible).elim

/-- Nonzero determinant forces the lower row of the inverse-decoder
adjugate to be nonzero, which is the premise of the pole decision. -/
theorem adjugate_lowerRow_ne (M : Mat2 QI)
    (determinantNonzero : determinant M ≠ 0) :
    (adjugate M).c ≠ 0 ∨ (adjugate M).d ≠ 0 := by
  by_cases hc : M.c = 0
  · right
    simp only [adjugate]
    intro ha
    apply determinantNonzero
    simp [determinant, hc, ha]
  · left
    simpa only [adjugate] using neg_ne_zero.mpr hc

theorem separation_denominator_ne
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {M : Mat2 QI}
    (output : CCLDenominator.SeparationOutput p ambient current M)
    {z : QI} (hz : output.state.box.Contains z) :
    M.c * z + M.d ≠ 0 := by
  intro zero
  have lower := output.lower hz
  rw [zero, normSq_zero] at lower
  linarith [output.margin_pos]

/-- The single inverse-decoder separation certificate applies to every
parser-generated branch source because all planned matrices share its lower
row. -/
theorem separation_source_denominator_ne
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {source : BoundarySource}
    (member : source ∈ inputPlan state)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    {z : QI} (contains : output.state.box.Contains z) :
    source.matrix.c * z + source.matrix.d ≠ 0 := by
  have lowerRow := inputPlan_lowerRow state member
  rw [lowerRow.1, lowerRow.2]
  exact separation_denominator_ne output contains

theorem separation_source_denominator_lower
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {source : BoundarySource}
    (member : source ∈ inputPlan state)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    {z : QI} (contains : output.state.box.Contains z) :
    output.margin ≤ normSq (source.matrix.c * z + source.matrix.d) := by
  have lowerRow := inputPlan_lowerRow state member
  simpa only [lowerRow.1, lowerRow.2] using output.lower contains

/-! ## Concrete bounded chart family after denominator separation -/

/-- The at-most-four bounded branch charts generated directly from a
denominator-separated parser state. -/
def separatedCharts
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} (state : RawParser.State)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) : List SourceChart :=
  plannedCharts state output.state.box output.margin output.margin_pos

theorem separatedCharts_ne_nil
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} (state : RawParser.State)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    separatedCharts state output ≠ [] :=
  plannedCharts_ne_nil state output.state.box output.margin output.margin_pos

theorem separatedCharts_length_le_four
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} (state : RawParser.State)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    (separatedCharts state output).length ≤ 4 :=
  plannedCharts_length_le_four state output.state.box output.margin
    output.margin_pos

/-- Run the total endpoint-safe common partition constructor on every
bounded chart generated by the separated parser state. -/
def separatedChartPartitions
    {ambient : RatBox} (p : GaussianPolynomial)
    {current : WindingOneState p ambient} (state : RawParser.State)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    List (SourceChartPartition p output.state.box) :=
  buildSourceChartPartitions p output.state.box (separatedCharts state output)

theorem separatedChartPartitions_ne_nil
    {ambient : RatBox} (p : GaussianPolynomial)
    {current : WindingOneState p ambient} (state : RawParser.State)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    separatedChartPartitions p state output ≠ [] :=
  buildSourceChartPartitions_ne_nil p output.state.box
    (separatedCharts_ne_nil state output)

theorem separatedChartPartitions_length_le_four
    {ambient : RatBox} (p : GaussianPolynomial)
    {current : WindingOneState p ambient} (state : RawParser.State)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    (separatedChartPartitions p state output).length ≤ 4 := by
  rw [separatedChartPartitions, buildSourceChartPartitions_length]
  exact separatedCharts_length_le_four state output

/-- Every rational point on a parser-planned branch boundary in the
denominator-separated box is represented by a parameter of a partitioned
bounded chart. -/
theorem separatedChartPartitions_cover_boundary_point
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (stateDeterminant : determinant state.matrix ≠ 0)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (source : BoundarySource) (sourceMember : source ∈ inputPlan state)
    (point : QI) (contains : output.state.box.Contains point)
    (boundary : source.form.eval point = 0) :
    ∃ partition ∈ separatedChartPartitions p state output,
      partition.entry.source = source ∧
      ∃ t : ℚ,
        partition.entry.chart.interval.lower ≤ t ∧
        t ≤ partition.entry.chart.interval.upper ∧
        partition.entry.chart.path.denominator.eval
          (PathPolynomial.ofRat t) ≠ 0 ∧
        partition.entry.chart.path.value t = point := by
  rcases plannedCharts_cover_boundary_point state output.state.box
      output.margin output.margin_pos source sourceMember
      (inputPlan_determinant_ne state sourceMember stateDeterminant)
      (inputPlan_parametrizationNondegenerate state sourceMember) point
      contains (separation_source_denominator_lower sourceMember output
        contains) boundary with
    ⟨entry, entryMember, sourceEquality, t, lower, upper, pathDenominator,
      pathValue⟩
  have separatedMember : entry ∈ separatedCharts state output := by
    simpa only [separatedCharts] using entryMember
  rcases SourceChartPartition.exists_mem_build_of_entry_mem
      (p := p) (box := output.state.box) separatedMember with
    ⟨partition, partitionMember, entryEquality⟩
  subst entry
  refine ⟨partition, ?_, sourceEquality, t, lower, upper, pathDenominator,
    pathValue⟩
  simpa only [separatedChartPartitions] using partitionMember

/-- Reverse chart coverage composed with the total guard partition: a
planned rational boundary point in the separated box reaches either a
quantitatively clear terminal cell or an explicit guarded event cell. -/
theorem separatedChartPartitions_guardCoverage_boundary_point
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (stateDeterminant : determinant state.matrix ≠ 0)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (source : BoundarySource) (sourceMember : source ∈ inputPlan state)
    (point : QI) (contains : output.state.box.Contains point)
    (boundary : source.form.eval point = 0) :
    ∃ partition ∈ separatedChartPartitions p state output,
      partition.entry.source = source ∧
      ∃ t : ℚ,
        partition.entry.chart.path.denominator.eval
          (PathPolynomial.ofRat t) ≠ 0 ∧
        partition.entry.chart.path.value t = point ∧
        GuardCellCoverage partition.entry.chart.proper partition.plan t := by
  rcases separatedChartPartitions_cover_boundary_point stateDeterminant output
      source sourceMember point contains boundary with
    ⟨partition, partitionMember, sourceEquality, t, lower, upper,
      pathDenominator, pathValue⟩
  exact ⟨partition, partitionMember, sourceEquality, t, pathDenominator,
    pathValue, partition.plan.guardCellCoverage
      partition.entry.chart.proper lower upper⟩

/-- Fully executable list of non-pole curve-root events whose exact closed
box test is true, flattened over every guarded chart partition. -/
def separatedRelevantCurveEvents
    {ambient : RatBox} (p : GaussianPolynomial)
    {current : WindingOneState p ambient} (state : RawParser.State)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    List (SourceRelevantCurveEvent p output.state.box) :=
  relevantCurveEventsOfSourcePartitions
    (separatedChartPartitions p state output)

/-- Fully executable relevant all-interior cells, after the quantitative
common-width subdivision of every guarded chart cell. -/
def separatedRelevantClearCells
    {ambient : RatBox} (p : GaussianPolynomial)
    {current : WindingOneState p ambient} (state : RawParser.State)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    List (SourceRelevantClearCell p output.state.box) :=
  relevantClearCellsOfSourcePartitions
    (separatedChartPartitions p state output)

/-- Fully executable guarded-event cells, retaining the same source/chart
partition provenance as the clear family. -/
def separatedEventGuardCells
    {ambient : RatBox} (p : GaussianPolynomial)
    {current : WindingOneState p ambient} (state : RawParser.State)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    List (SourceEventGuardCell p output.state.box) :=
  eventGuardCellsOfSourcePartitions
    (separatedChartPartitions p state output)

/-- Relevant curve-root classifications obtained directly from the terminal
guard cells, retaining their source partition. -/
def separatedGuardCurveEvents
    {ambient : RatBox} (p : GaussianPolynomial)
    {current : WindingOneState p ambient} (state : RawParser.State)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    List (SourceRelevantCurveEvent p output.state.box) :=
  relevantCurveEventsOfSourceEventGuardCells
    (separatedEventGuardCells p state output)

/-- The same cell-local events with their exact guard-cell membership retained
for constructive positive-count recovery. -/
def separatedSourceGuardCurveEvents
    {ambient : RatBox} (p : GaussianPolynomial)
    {current : WindingOneState p ambient} (state : RawParser.State)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    List (SourceGuardCurveEvent p output.state.box) :=
  guardCurveEventsOfSourceEventGuardCells
    (separatedEventGuardCells p state output)

/-- Every non-identically-zero rational chart root in the separated box is
retained by the final source-labelled relevant-event family. -/
theorem separatedRelevantCurveEvents_covers_root_nonzero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (partition : SourceChartPartition p output.state.box)
    (partitionMember : partition ∈ separatedChartPartitions p state output)
    {t : ℚ} (lower : partition.entry.chart.interval.lower ≤ t)
    (upper : t ≤ partition.entry.chart.interval.upper)
    (clearedNonzero :
      (clearedReal p partition.entry.chart.path).isZero = false ∨
      (clearedImag p partition.entry.chart.path).isZero = false)
    (pathDenominator : partition.entry.chart.path.denominator.eval
      (PathPolynomial.ofRat t) ≠ 0)
    (polynomialZero : p.eval (partition.entry.chart.path.value t) = 0)
    (contains : output.state.box.Contains
      (partition.entry.chart.path.value t)) :
    ∃ sourceEvent ∈ separatedRelevantCurveEvents p state output,
      sourceEvent.partition = partition ∧
      (boxEventSigns sourceEvent.event.branch
        sourceEvent.event.parent).refined.interval.lower ≤ t ∧
      t ≤ (boxEventSigns sourceEvent.event.branch
        sourceEvent.event.parent).refined.interval.upper ∧
      sourceEvent.event.branch.factor.polynomial.eval t = 0 := by
  simpa only [separatedRelevantCurveEvents] using
    relevantCurveEventsOfSourcePartitions_covers_root_nonzero
      (separatedChartPartitions p state output) partition partitionMember lower
      upper clearedNonzero pathDenominator polynomialZero contains

theorem separatedChart_source_mem_inputPlan
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)} {entry : SourceChart}
    (member : entry ∈ separatedCharts state output) :
    entry.source ∈ inputPlan state :=
  source_mem_inputPlan_of_mem_plannedCharts state output.state.box
    output.margin output.margin_pos member

theorem separatedChart_determinant_ne
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (stateDeterminant : determinant state.matrix ≠ 0)
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)} {entry : SourceChart}
    (member : entry ∈ separatedCharts state output) :
    determinant entry.source.matrix ≠ 0 :=
  inputPlan_determinant_ne state
    (separatedChart_source_mem_inputPlan member) stateDeterminant

/-- Every retained algebraic event still points to a chart in the separated
parser-generated chart family. -/
theorem separatedRelevantCurveEvent_entry_mem
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {candidate : SourceRelevantCurveEvent p output.state.box}
    (member : candidate ∈ separatedRelevantCurveEvents p state output) :
    candidate.partition.entry ∈ separatedCharts state output := by
  have partitionMember : candidate.partition ∈
      separatedChartPartitions p state output :=
    candidate.partition_mem_of_mem (by
      simpa only [separatedRelevantCurveEvents] using member)
  exact SourceChartPartition.entry_mem_of_mem_build (by
    simpa only [separatedChartPartitions] using partitionMember)

theorem separatedRelevantCurveEvent_source_mem_inputPlan
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {candidate : SourceRelevantCurveEvent p output.state.box}
    (member : candidate ∈ separatedRelevantCurveEvents p state output) :
    candidate.partition.entry.source ∈ inputPlan state :=
  separatedChart_source_mem_inputPlan
    (separatedRelevantCurveEvent_entry_mem member)

theorem separatedRelevantCurveEvent_parametrizationNondegenerate
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {candidate : SourceRelevantCurveEvent p output.state.box}
    (member : candidate ∈ separatedRelevantCurveEvents p state output) :
    candidate.partition.entry.source.ParametrizationNondegenerate :=
  inputPlan_parametrizationNondegenerate state
    (separatedRelevantCurveEvent_source_mem_inputPlan member)

/-- Execute the complete event-count dichotomy directly on a member of the
denominator-separated, parser-generated chart family. -/
def SourceRelevantCurveEvent.decideSeparatedCount
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (candidate : SourceRelevantCurveEvent p output.state.box)
    (member : candidate ∈ separatedRelevantCurveEvents p state output) :
    CurveEventCountDecision p candidate.partition.entry.chart.path
      output.state.box candidate.event :=
  candidate.decideCountOfMem (by
    simpa only [separatedRelevantCurveEvents] using member)

theorem separatedRelevantCurveEvent_determinant_ne
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (stateDeterminant : determinant state.matrix ≠ 0)
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {candidate : SourceRelevantCurveEvent p output.state.box}
    (member : candidate ∈ separatedRelevantCurveEvents p state output) :
    determinant candidate.partition.entry.source.matrix ≠ 0 :=
  separatedChart_determinant_ne stateDeterminant
    (separatedRelevantCurveEvent_entry_mem member)

/-- Every retained relevant clear cell still points to a chart in the
separated parser-generated chart family. -/
theorem separatedRelevantClearCell_entry_mem
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {candidate : SourceRelevantClearCell p output.state.box}
    (member : candidate ∈ separatedRelevantClearCells p state output) :
    candidate.sourceCell.partition.entry ∈ separatedCharts state output := by
  have sourceCellMember :
      candidate.sourceCell ∈ clearGuardCellsOfSourcePartitions
        (separatedChartPartitions p state output) :=
    candidate.sourceCell_mem_of_mem (by
      simpa only [separatedRelevantClearCells] using member)
  have partitionMember :
      candidate.sourceCell.partition ∈
        separatedChartPartitions p state output :=
    candidate.sourceCell.partition_mem_of_mem sourceCellMember
  exact SourceChartPartition.entry_mem_of_mem_build (by
    simpa only [separatedChartPartitions] using partitionMember)

theorem separatedRelevantClearCell_source_mem_inputPlan
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {candidate : SourceRelevantClearCell p output.state.box}
    (member : candidate ∈ separatedRelevantClearCells p state output) :
    candidate.sourceCell.partition.entry.source ∈ inputPlan state :=
  separatedChart_source_mem_inputPlan
    (separatedRelevantClearCell_entry_mem member)

theorem separatedRelevantClearCell_parametrizationNondegenerate
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {candidate : SourceRelevantClearCell p output.state.box}
    (member : candidate ∈ separatedRelevantClearCells p state output) :
    candidate.sourceCell.partition.entry.source.ParametrizationNondegenerate :=
  inputPlan_parametrizationNondegenerate state
    (separatedRelevantClearCell_source_mem_inputPlan member)

theorem separatedRelevantClearCell_determinant_ne
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (stateDeterminant : determinant state.matrix ≠ 0)
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {candidate : SourceRelevantClearCell p output.state.box}
    (member : candidate ∈ separatedRelevantClearCells p state output) :
    determinant candidate.sourceCell.partition.entry.source.matrix ≠ 0 :=
  separatedChart_determinant_ne stateDeterminant
    (separatedRelevantClearCell_entry_mem member)

/-- Decide one cell returned by the separated finite pipeline without asking
the caller for any path-denominator side condition. -/
def decideSeparatedRelevantClearCell
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} (state : RawParser.State)
    (stateDeterminant : determinant state.matrix ≠ 0)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (candidate : SourceRelevantClearCell p output.state.box)
    (member : candidate ∈ separatedRelevantClearCells p state output)
    (owner : Bool) : RelevantClearCellOutcome p output.state.box candidate :=
  decideRelevantClearCell candidate owner
    (separatedRelevantClearCell_determinant_ne stateDeterminant member)
    (separatedRelevantClearCell_parametrizationNondegenerate member)

/-- The computed line radius contains every real-boundary parameter whose
inverse path can meet the separated root box. -/
theorem separated_real_parameter_abs_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {matrix : Mat2 QI} {threshold t : ℚ}
    (sourceMember : BoundarySource.real matrix threshold ∈ inputPlan state)
    (stateDeterminant : determinant state.matrix ≠ 0)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (pathDenominator :
      (BoundarySource.real matrix threshold).path.denominator.eval
        (PathPolynomial.ofRat t) ≠ 0)
    (contains : output.state.box.Contains
      ((BoundarySource.real matrix threshold).path.value t)) :
    |t| ≤ lineParameterRadius (.real matrix threshold) output.state.box
      output.margin := by
  apply real_parameter_abs_le matrix threshold output.state.box
    output.margin_pos
    (inputPlan_determinant_ne state sourceMember stateDeterminant)
    pathDenominator contains
  exact separation_source_denominator_lower sourceMember output contains

/-- The computed line radius contains every imaginary-boundary parameter
whose inverse path can meet the separated root box. -/
theorem separated_imag_parameter_abs_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {matrix : Mat2 QI} {threshold t : ℚ}
    (sourceMember : BoundarySource.imag matrix threshold ∈ inputPlan state)
    (stateDeterminant : determinant state.matrix ≠ 0)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (pathDenominator :
      (BoundarySource.imag matrix threshold).path.denominator.eval
        (PathPolynomial.ofRat t) ≠ 0)
    (contains : output.state.box.Contains
      ((BoundarySource.imag matrix threshold).path.value t)) :
    |t| ≤ lineParameterRadius (.imag matrix threshold) output.state.box
      output.margin := by
  apply imag_parameter_abs_le matrix threshold output.state.box
    output.margin_pos
    (inputPlan_determinant_ne state sourceMember stateDeterminant)
    pathDenominator contains
  exact separation_source_denominator_lower sourceMember output contains

/-- A current-state witness before adding the denominator proof supplied by
the separation branch. -/
structure StateWitness (state : RawParser.State) (box : RatBox) where
  input : QI
  contains : box.Contains input
  holds : state.Holds
    (RatBox.homographic (adjugate state.matrix) input)

/-- Add the uniform inverse-decoder denominator certificate to a witness in
the separated track box. -/
def CellWitness.ofSeparation
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (witness : StateWitness state output.state.box) :
    CellWitness state output.state.box where
  input := witness.input
  contains := witness.contains
  inverseDenominator := separation_denominator_ne output witness.contains
  holds := witness.holds

/-- Opening finite controller outcome: an exact polynomial root at the
decoder pole, or a denominator-separated cell with its fully resolved strict
formula truth table (possibly requesting more refinement). -/
inductive ClearStepDecision
    (p : GaussianPolynomial) (ambient : RatBox)
    (current : WindingOneState p ambient) (state : RawParser.State) where
  | terminalPole (point : QI) (root : p.eval point = 0)
      (contains : current.box.Contains point)
      (strict : current.box.StrictContains point)
      (denominatorZero :
        (adjugate state.matrix).c * point +
          (adjugate state.matrix).d = 0)
  | separated
      (output : CCLDenominator.SeparationOutput p ambient current
        (adjugate state.matrix))
      (cell : ResolvedCellOutcome state output.state.box)

/-- Compose the exact pole decision, its uniform box denominator bound, and
the strict-cell child-formula evaluator. -/
def decideClearStep
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient) (state : RawParser.State)
    (determinantNonzero : determinant state.matrix ≠ 0)
    (witness :
      (output : CCLDenominator.SeparationOutput p ambient current
        (adjugate state.matrix)) → StateWitness state output.state.box) :
    ClearStepDecision p ambient current state :=
  match CCLDenominator.decide track current (adjugate state.matrix)
      (adjugate_lowerRow_ne state.matrix determinantNonzero) with
  | .terminal point root contains strict denominatorZero =>
      .terminalPole point root contains strict denominatorZero
  | .separated output =>
      .separated output
        (resolveCell state output.state.box determinantNonzero
          (CellWitness.ofSeparation output (witness output)))

end CCLBranchEvidence
end FTA
