import FTA.CCLActiveBoundarySectorClosure

/-!
# Total active-controller steps at unfinished sector boundaries

The zero-prefix and one-prefix boundaries each consume one sector bit.  The
one-prefix successor records an explicit completed-sector boundary policy:
exact canonical active truth is deliberately false at its all-neither event,
so the remaining third-bit wall is entered geometrically on the next call.
-/

namespace FTA
namespace CCLActiveMetricTrack

open CCL CCL.GaussianRat
open CCL.EncoderParserBridge
open FTA.AxisSafeCuts
open FTA.CCLActiveBoxCoupling
open FTA.CCLActiveCanonicalEvent
open FTA.CCLActiveEventGrid
open FTA.CCLBoundaryPreservingOwner
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLBranchEvidence
open FTA.CCLCanonicalEvent
open FTA.CCLCompletedBlockContraction
open FTA.CCLCompletedBlockObservation
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLNextBitFormula
open FTA.CCLParserGeometry
open FTA.CCLPositiveEventConvergence
open FTA.CCLPersistentBlockObservations
open FTA.CCLSectorBoundaryConvergence
open FTA.CCLSectorInteriorCone
open FTA.CCLSectorInteriorSelection
open FTA.CCLStrictChildSemantics
open FTA.ConstructiveTrack
open FTA.CentralBandGrid
open FTA.GlobalNonnegativity
open FTA.LocalExtraction
open FTA.RootTrackSeparation

/-- A row admitted by a one-bit sector prefix has that prefix as its first
code projection. -/
theorem sectorFirstBit_eq_of_mem_one
    (first : Bool) (sector : Sector)
    (member : sector ∈ RawParser.sectorCandidates (.one first)) :
    sectorFirstBit sector = first := by
  cases first <;> cases sector <;> simp_all [sectorFirstBit]

/-- Retaining the row's second projection gives the corresponding completed
two-bit prefix. -/
theorem sector_mem_two_of_mem_one
    (first : Bool) (sector : Sector)
    (member : sector ∈ RawParser.sectorCandidates (.one first)) :
    sector ∈ RawParser.sectorCandidates
      (.two first (sectorSecondBit sector)) := by
  cases first <;> cases sector <;> simp_all [sectorSecondBit]

/-- Every row of the zero-prefix table belongs to the one-bit prefix selected
by its first code projection. -/
theorem sector_mem_one_projection_of_mem_zero
    (sector : Sector)
    (_member : sector ∈ RawParser.sectorCandidates .zero) :
    sector ∈ RawParser.sectorCandidates
      (.one (sectorFirstBit sector)) := by
  cases sector <;> native_decide

/-- At a completed two-bit prefix, a strict point in either remaining full
sector row selects exactly that row's third code bit. -/
theorem localBit_sector_two_eq_sectorThirdBit
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (sector : Sector) (value : QI)
    (member : sector ∈ RawParser.sectorCandidates (.two first second))
    (holds : sector.Holds
      (RawParser.normalizedValue kind exponent value)) :
    localBit (.sector kind exponent (.two first second)) value =
      sectorThirdBit sector := by
  cases first <;> cases second <;> cases sector <;>
    simp_all [localBit, Sector.Holds, sectorThirdBit]

/-- Every comparison source of an admitted completed-prefix row is an atom of
that row's third-bit child formula. -/
theorem blockEventFace_source_mem_inputAdvanceFormula_atoms_of_completedSector
    (state : RawParser.State) (kind : RawParser.BlockKind) (exponent : ℕ)
    (first second : Bool) (sector : Sector)
    (phase : state.phase = .sector kind exponent (.two first second))
    (candidate : sector ∈
      RawParser.sectorCandidates (.two first second))
    (face : EventOrientedFace)
    (member : face ∈ blockEventFaces kind exponent sector
      (adjugate state.matrix)) :
    ∃ atom ∈ formulaAtoms
        (inputAdvanceFormula state (sectorThirdBit sector)),
      atom.form = face.source := by
  rcases state with ⟨statePhase, matrix, history⟩
  simp only at phase
  subst statePhase
  cases kind <;> cases first <;> cases second <;> cases sector <;>
    simp_all [blockEventFaces, radialEventFaces, sectorEventFaces,
      eventNormFace, eventRealFace, eventImagFace, inputAdvanceFormula,
      advanceFormula, sectorThirdBit, RawParser.sectorOfBits,
      radialFormula, sectorFormula, Formula.pullback, formulaAtoms,
      pullbackForm_normComparison, pullbackForm_realComparison,
      pullbackForm_imagComparison, normalizedMatrix, normalizationMatrix,
      RawParser.identityMatrix, Mat2.mul, adjugate] <;> aesop

/-- Every comparison face of a row admitted by a completed sector prefix is
classified by the pair of third-bit child formulas. -/
theorem clearedForm_mem_inputEventPolynomials_of_completedSectorBlockFace
    (state : RawParser.State) (kind : RawParser.BlockKind) (exponent : ℕ)
    (first second : Bool) (sector : Sector) (path : ProjectivePath.Path)
    (phase : state.phase = .sector kind exponent (.two first second))
    (candidate : sector ∈
      RawParser.sectorCandidates (.two first second))
    (face : EventOrientedFace)
    (member : face ∈ blockEventFaces kind exponent sector
      (adjugate state.matrix)) :
    clearedForm face.source path ∈ inputEventPolynomials state path := by
  rcases blockEventFace_source_mem_inputAdvanceFormula_atoms_of_completedSector
      state kind exponent first second sector phase candidate face member with
    ⟨atom, atomMember, atomForm⟩
  rw [← atomForm]
  exact clearedForm_mem_inputEventPolynomials_of_advance_atom state path
    (sectorThirdBit sector) atom atomMember

/-- Uniform finite source list for the two full rows admitted by a completed
sector prefix. -/
def completedSectorEventSourceForms
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (matrix : Mat2 QI) : List HermitianForm :=
  (RawParser.sectorCandidates (.two first second)).flatMap fun sector =>
    blockEventSourceForms kind exponent sector matrix

theorem blockEventFace_source_mem_completedSectorEventSourceForms
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (sector : Sector) (matrix : Mat2 QI)
    (candidate : sector ∈ RawParser.sectorCandidates (.two first second))
    (face : EventOrientedFace)
    (member : face ∈ blockEventFaces kind exponent sector matrix) :
    face.source ∈ completedSectorEventSourceForms kind exponent first second
      matrix := by
  apply List.mem_flatMap.mpr
  exact ⟨sector, candidate, List.mem_map.mpr ⟨face, member, rfl⟩⟩

/-- A sufficiently close persistent active sample supplies one admitted full
row whose exact event orientations are all weakly inward. -/
theorem exists_canonicalBlockTarget_of_completedSector
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent (.two first second)) :
    ∃ sector ∈ RawParser.sectorCandidates (.two first second),
      CanonicalBlockTarget data.boundaryOrientedInputCell kind exponent sector
        (adjugate (RawParser.parse current.core.word).matrix) := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let cell := data.boundaryOrientedInputCell
  let forms := completedSectorEventSourceForms kind exponent first second matrix
  let strictRadius := convergentStrictRadius cell forms
  let radius := strictRadius / 2
  have strictRadiusPositive : 0 < strictRadius :=
    convergentStrictRadius_pos cell forms
  have radiusPositive : 0 < radius := by
    dsimp only [radius]
    linarith
  have radiusSmall : radius < convergentStrictRadius cell forms := by
    dsimp only [radius, strictRadius]
    linarith
  let inner := refineState squarefree elimination data.output.state radius
    radiusPositive
  have innerRefinesCurrent : inner.box.Refines current.core.numerical.box := by
    apply (refineState_refines squarefree elimination data.output.state radius
      radiusPositive).trans
    exact data.output_refines_separation.trans data.separation.refines
  let sample := current.samples.sample inner innerRefinesCurrent
  have active := sample.tail_active
  rw [phase] at active
  rcases active with ⟨radial, sector, sectorCandidate, sectorHolds⟩
  refine ⟨sector, sectorCandidate, ?_⟩
  let tail := RatBox.homographic matrix sample.point
  have radialClosure : RadialClosureHolds kind exponent tail :=
    radialClosureHolds_of_radialBracket kind exponent tail radial
  have sectorClosure : SectorClosureHolds sector
      (RawParser.normalizedValue kind exponent tail) :=
    sectorClosureHolds_of_holds sector _ sectorHolds
  have denominator : matrix.c * sample.point + matrix.d ≠ 0 := by
    simpa only [matrix, state] using sample.inverseDenominator
  have inward : ∀ form ∈
      blockSectorInteriorForms kind exponent sector matrix,
      0 ≤ form.eval sample.point := by
    intro form member
    rcases List.mem_append.mp member with radialMember | sectorMember
    · exact radialInteriorForms_nonneg_of_closure kind exponent matrix
        sample.point denominator radialClosure form radialMember
    · let normalized := normalizedMatrix kind exponent matrix
      have normalizedDenominator :
          normalized.c * sample.point + normalized.d ≠ 0 := by
        have lowerRow := normalizedMatrix_lowerRow kind exponent matrix
        simpa only [normalized, lowerRow.1, lowerRow.2] using denominator
      have closureAt : SectorClosureHolds sector
          (RatBox.homographic normalized sample.point) := by
        simpa only [normalized, tail, homographic_normalizedMatrix] using
          sectorClosure
      exact sectorInteriorForms_nonneg_of_closure sector normalized
        sample.point normalizedDenominator closureAt form sectorMember
  change CanonicalBlockTarget cell kind exponent sector matrix
  apply canonicalBlockTargetOfInnerSample cell kind exponent sector matrix forms
    squarefree degreeNonzero elimination data.output.state
    data.output_refines_separation radius radiusPositive radiusSmall
    sample.point
  · simpa only [inner] using sample.inside
  · intro face faceMember
    exact blockEventFace_source_mem_completedSectorEventSourceForms kind
      exponent first second sector matrix sectorCandidate face faceMember
  · intro face faceMember
    exact clearedForm_mem_inputEventPolynomials_of_completedSectorBlockFace
      state kind exponent first second sector _ phase sectorCandidate face
        faceMember
  · exact inward

def canonicalCompletedSectorCandidates
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (matrix : Mat2 QI) : List Sector :=
  (RawParser.sectorCandidates (.two first second)).filter fun sector =>
    canonicalBlockTargetCheck cell kind exponent sector matrix

structure CompletedSectorCanonicalSelection
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool) where
  sector : Sector
  candidate : sector ∈ RawParser.sectorCandidates (.two first second)
  target : CanonicalBlockTarget data.boundaryOrientedInputCell kind exponent
    sector (adjugate (RawParser.parse current.core.word).matrix)

/-- Executably choose the first full row admitted by the completed prefix and
weakly inward in the exact event's finite canonical table. -/
def completedSectorCanonicalSelection
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent (.two first second)) :
    CompletedSectorCanonicalSelection data kind exponent first second := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let cell := data.boundaryOrientedInputCell
  let candidates := canonicalCompletedSectorCandidates cell kind exponent
    first second matrix
  have candidatesNonempty : candidates ≠ [] := by
    rcases exists_canonicalBlockTarget_of_completedSector data squarefree
        degreeNonzero elimination kind exponent first second phase with
      ⟨sector, sectorCandidate, target⟩
    intro empty
    have member : sector ∈ candidates := by
      apply List.mem_filter.mpr
      exact ⟨sectorCandidate,
        (canonicalBlockTargetCheck_eq_true_iff cell kind exponent sector
          matrix).2 target.canonicalNonnegative⟩
    rw [empty] at member
    simp at member
  let sector := candidates.head candidatesNonempty
  have selected := List.head_mem candidatesNonempty
  have selectedParts := List.mem_filter.mp selected
  refine
    { sector := sector
      candidate := selectedParts.1
      target := ?_ }
  refine
    { classified := ?_
      canonicalNonnegative :=
        (canonicalBlockTargetCheck_eq_true_iff cell kind exponent sector
          matrix).1 selectedParts.2 }
  intro face faceMember
  exact clearedForm_mem_inputEventPolynomials_of_completedSectorBlockFace
    state kind exponent first second sector _ phase selectedParts.1 face
      faceMember

/-! ## Zero-prefix sector transition -/

/-- State-indexed wrapper for the strict full-row realization theorem. -/
theorem blockSectorBoxSample_inputIncremental_holds_zero_of_phase
    {kind : RawParser.BlockKind} {exponent : ℕ} {sector : Sector}
    {state : RawParser.State} {box : RatBox}
    (sample : BlockSectorBoxSample kind exponent sector
      (adjugate state.matrix) box)
    (phase : state.phase = .sector kind exponent .zero)
    (bit : Bool)
    (sectorMember : sector ∈ RawParser.sectorCandidates (.one bit))
    (denominator : (adjugate state.matrix).c * sample.point +
      (adjugate state.matrix).d ≠ 0) :
    (inputIncrementalAdvanceFormula state bit).Holds sample.point := by
  rcases state with ⟨statePhase, matrix, history⟩
  simp only at phase
  subst statePhase
  exact sample.inputIncrementalAdvanceFormula_holds_zero bit sectorMember
    denominator

/-- One bit after a zero-prefix sector is a one-prefix sector, never the
completed two-bit phase. -/
theorem rawParser_step_not_completed_of_sector_zero
    (state : RawParser.State) (bit : Bool)
    {kind : RawParser.BlockKind} {exponent : ℕ}
    (phase : state.phase = .sector kind exponent .zero) :
    ¬∃ kind exponent first second,
      (RawParser.step state bit).phase =
        .sector kind exponent (.two first second) := by
  rcases state with ⟨statePhase, matrix, history⟩
  simp only at phase
  subst statePhase
  simp [RawParser.step]

/-- Strict radial and common angular faces realize the one-prefix incremental
child without choosing the future third sector wall. -/
theorem orientedBoxSample_inputIncremental_holds_one_of_phase
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    {state : RawParser.State} {box : RatBox}
    (sample : OrientedBoxSample
      (orientedFaceForms (blockSectorTwoEventFaces kind exponent first second
        (adjugate state.matrix))) box)
    (phase : state.phase = .sector kind exponent (.one first)) :
    (inputIncrementalAdvanceFormula state second).Holds sample.point := by
  rcases state with ⟨statePhase, matrix, history⟩
  simp only at phase
  subst statePhase
  have strict := sample.formsStrict
  cases kind <;> cases first <;> cases second <;>
    simp_all [orientedFaceForms, blockSectorTwoEventFaces, radialEventFaces,
      sectorTwoEventFaces, EventOrientedFace.form, eventNormFace,
      eventRealFace, eventImagFace, inputIncrementalAdvanceFormula,
      CCLNextBitFormula.incrementalAdvanceFormula, activeFormula, radialFormula,
      sectorBitsFormula, Formula.pullback, CCLParserGeometry.Formula.Holds,
      CCLParserGeometry.Atom.Holds, SignTest.Holds, RawParser.step,
      pullbackForm_normComparison, pullbackForm_realComparison,
      pullbackForm_imagComparison, normalizedMatrix, normalizationMatrix,
      RawParser.identityMatrix, Mat2.mul, adjugate] <;>
    constructor <;> linarith

/-- A strict admitted full-row sample realizes the completed prefix's active
predicate and, away from its isolated terminal representative, advances by
that row's third code bit. -/
theorem blockSectorBoxSample_inputIncremental_holds_completed_of_phase
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    {sector : Sector} {state : RawParser.State} {box : RatBox}
    (sample : BlockSectorBoxSample kind exponent sector
      (adjugate state.matrix) box)
    (phase : state.phase = .sector kind exponent (.two first second))
    (candidate : sector ∈
      RawParser.sectorCandidates (.two first second))
    (denominator : (adjugate state.matrix).c * sample.point +
      (adjugate state.matrix).d ≠ 0)
    (notTerminal : ¬TerminalSectorAt state
      (RatBox.homographic (adjugate state.matrix) sample.point)) :
    (inputIncrementalAdvanceFormula state
      (sectorThirdBit sector)).Holds sample.point := by
  let matrix := adjugate state.matrix
  let tail := RatBox.homographic matrix sample.point
  have radial : RawParser.radialBracket kind exponent tail :=
    (radialFormula_iff kind exponent matrix sample.point denominator).1
      sample.radialFormula_holds
  have sectorHolds : sector.Holds
      (RawParser.normalizedValue kind exponent tail) :=
    (normalizedSectorFormula_iff kind exponent sector matrix sample.point
      denominator).1 sample.sectorFormula_holds
  have active : (inputActiveFormula state).Holds sample.point := by
    apply (inputActiveFormula_iff state sample.point denominator).2
    rw [phase]
    exact ⟨radial, sector, candidate, sectorHolds⟩
  have incremental := inputIncremental_holds_localBit_of_active_notTerminal
    state sample.point denominator active notTerminal
  have localBitEq : inputLocalBit state sample.point =
      sectorThirdBit sector := by
    unfold inputLocalBit
    rw [phase]
    exact localBit_sector_two_eq_sectorThirdBit kind exponent first second
      sector tail candidate sectorHolds
  rwa [localBitEq] at incremental

/-- Completing a two-bit sector installs the next loop header; it cannot
leave another completed sector phase immediately. -/
theorem rawParser_step_not_completed_of_completedSector
    (state : RawParser.State) (bit : Bool)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : state.phase = .sector kind exponent (.two first second)) :
    ¬∃ kind exponent first second,
      (RawParser.step state bit).phase =
        .sector kind exponent (.two first second) := by
  rcases state with ⟨statePhase, matrix, history⟩
  simp only at phase
  subst statePhase
  simp [RawParser.step, RawParser.completeSector]

/-- Persistent active representatives after a zero-prefix sector boundary.
The finite canonical row is fixed once; its rational representative is
reconstructed inside every later winding box. -/
def persistentActiveSamplesOfSectorZeroBoundary
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent .zero)
    (selection : SectorZeroCanonicalSelection data kind exponent)
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR) data.output.state
      (adjugate (RawParser.step (RawParser.parse current.core.word)
        (sectorFirstBit selection.sector)).matrix)) :
    PersistentActiveSamples
      (current.core.word ++ [sectorFirstBit selection.sector])
      successorSeparation.state where
  sample next nextRefines := by
    let bit := sectorFirstBit selection.sector
    have nextRefinesOutput : next.box.Refines data.output.state.box :=
      nextRefines.trans successorSeparation.refines
    have nextRefinesSeparation : next.box.Refines data.separation.state.box :=
      nextRefinesOutput.trans data.output_refines_separation
    let block := activeBlockConvergentSample data kind exponent
      selection.sector selection.target squarefree degreeNonzero elimination
        next nextRefinesSeparation
    have inside : next.box.Contains block.point :=
      ⟨block.boxStrict.1.le, block.boxStrict.2.1.le,
        block.boxStrict.2.2.1.le, block.boxStrict.2.2.2.le⟩
    have oldDenominator := separation_denominator_ne data.separation
      (nextRefinesSeparation.contains inside)
    have newDenominator := separation_denominator_ne successorSeparation
      (nextRefines.contains inside)
    have sectorMember : selection.sector ∈
        RawParser.sectorCandidates (.one bit) :=
      sector_mem_one_projection_of_mem_zero selection.sector
        selection.candidate
    exact ActiveBoxSample.ofIncrementalStep bit block.point inside
      oldDenominator newDenominator
        (blockSectorBoxSample_inputIncremental_holds_zero_of_phase block phase
          bit sectorMember oldDenominator)

/-- Install the selected zero-prefix sector bit as an ordinary repeatable
active state. -/
def nextOfSectorZeroBoundary
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR))
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent .zero)
    (selection : SectorZeroCanonicalSelection data kind exponent)
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR) data.output.state
      (adjugate (RawParser.step (RawParser.parse current.core.word)
        (sectorFirstBit selection.sector)).matrix)) :
    State p (RatBox.symmetric R hR) where
  core :=
    { numerical := successorSeparation.state
      word := current.core.word ++ [sectorFirstBit selection.sector] }
  samples := persistentActiveSamplesOfSectorZeroBoundary data squarefree
    degreeNonzero elimination kind exponent phase selection
      successorSeparation
  observations := persistentObservationsOfNoncompletedStep current
    successorSeparation.state
      (successorSeparation.refines.trans
        (data.output_refines_separation.trans data.separation.refines))
      (sectorFirstBit selection.sector) (by
        rintro ⟨_, _, _, _, completed⟩
        rw [phase] at completed
        cases completed)
  completedSector := .canonical (by
    intro completed
    rw [rawParser_parse_append_singleton] at completed
    exact (rawParser_step_not_completed_of_sector_zero
      (RawParser.parse current.core.word) (sectorFirstBit selection.sector)
        phase completed).elim)

theorem nextOfSectorZeroBoundary_refines
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR))
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent .zero)
    (selection : SectorZeroCanonicalSelection data kind exponent)
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR) data.output.state
      (adjugate (RawParser.step (RawParser.parse current.core.word)
        (sectorFirstBit selection.sector)).matrix)) :
    (nextOfSectorZeroBoundary current data squarefree degreeNonzero
      elimination kind exponent phase selection
        successorSeparation).core.numerical.box.Refines
          current.core.numerical.box :=
  successorSeparation.refines.trans
    (data.output_refines_separation.trans data.separation.refines)

/-- Execute denominator separation after the selected zero-prefix sector bit. -/
def resolveSectorZeroBoundary
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (current : State p (RatBox.symmetric R hR))
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent .zero) : StepResult current := by
  let selection := sectorZeroCanonicalSelection data squarefree degreeNonzero
    elimination kind exponent phase
  let bit := sectorFirstBit selection.sector
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
      let next := nextOfSectorZeroBoundary current data squarefree
        degreeNonzero elimination kind exponent phase selection
          successorSeparation
      .next bit next
        (nextOfSectorZeroBoundary_refines current data squarefree
          degreeNonzero elimination kind exponent phase selection
            successorSeparation) rfl

/-! ## One-prefix sector transition -/

/-- Persistent active representatives after a one-prefix sector boundary.
The canonical common two-face cone fixes the second bit while deliberately
leaving the third sector wall for the completed-sector boundary step. -/
def persistentActiveSamplesOfSectorOneBoundary
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first : Bool)
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent (.one first))
    (selection : SectorOneCanonicalSelection data kind exponent first)
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR) data.output.state
      (adjugate (RawParser.step (RawParser.parse current.core.word)
        selection.second).matrix)) :
    PersistentActiveSamples
      (current.core.word ++ [selection.second])
      successorSeparation.state where
  sample next nextRefines := by
    let second := selection.second
    have nextRefinesOutput : next.box.Refines data.output.state.box :=
      nextRefines.trans successorSeparation.refines
    have nextRefinesSeparation : next.box.Refines data.separation.state.box :=
      nextRefinesOutput.trans data.output_refines_separation
    let oriented := activeBlockSectorTwoConvergentSample data kind exponent
      first second selection.target squarefree degreeNonzero elimination next
        nextRefinesSeparation
    have inside : next.box.Contains oriented.point :=
      ⟨oriented.boxStrict.1.le, oriented.boxStrict.2.1.le,
        oriented.boxStrict.2.2.1.le, oriented.boxStrict.2.2.2.le⟩
    have oldDenominator := separation_denominator_ne data.separation
      (nextRefinesSeparation.contains inside)
    have newDenominator := separation_denominator_ne successorSeparation
      (nextRefines.contains inside)
    exact ActiveBoxSample.ofIncrementalStep second oriented.point inside
      oldDenominator newDenominator
        (orientedBoxSample_inputIncremental_holds_one_of_phase oriented phase)

/-- Install the selected second sector bit.  The resulting completed prefix
must use the geometric boundary handler rather than the exact canonical-event
shortcut. -/
def nextOfSectorOneBoundary
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR))
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first : Bool)
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent (.one first))
    (selection : SectorOneCanonicalSelection data kind exponent first)
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR) data.output.state
      (adjugate (RawParser.step (RawParser.parse current.core.word)
        selection.second).matrix)) :
    State p (RatBox.symmetric R hR) where
  core :=
    { numerical := successorSeparation.state
      word := current.core.word ++ [selection.second] }
  samples := persistentActiveSamplesOfSectorOneBoundary data squarefree
    degreeNonzero elimination kind exponent first phase selection
      successorSeparation
  observations := persistentObservationsOfNoncompletedStep current
    successorSeparation.state
      (successorSeparation.refines.trans
        (data.output_refines_separation.trans data.separation.refines))
      selection.second (by
        rintro ⟨_, _, _, _, completed⟩
        rw [phase] at completed
        cases completed)
  completedSector := .boundary

theorem nextOfSectorOneBoundary_refines
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR))
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first : Bool)
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent (.one first))
    (selection : SectorOneCanonicalSelection data kind exponent first)
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR) data.output.state
      (adjugate (RawParser.step (RawParser.parse current.core.word)
        selection.second).matrix)) :
    (nextOfSectorOneBoundary current data squarefree degreeNonzero elimination
      kind exponent first phase selection successorSeparation).core.numerical.box.Refines
        current.core.numerical.box :=
  successorSeparation.refines.trans
    (data.output_refines_separation.trans data.separation.refines)

/-- Execute denominator separation after the selected second sector bit. -/
def resolveSectorOneBoundary
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (current : State p (RatBox.symmetric R hR))
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first : Bool)
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent (.one first)) : StepResult current := by
  let selection := sectorOneCanonicalSelection data squarefree degreeNonzero
    elimination kind exponent first phase
  let bit := selection.second
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
      let next := nextOfSectorOneBoundary current data squarefree
        degreeNonzero elimination kind exponent first phase selection
          successorSeparation
      .next bit next
        (nextOfSectorOneBoundary_refines current data squarefree degreeNonzero
          elimination kind exponent first phase selection successorSeparation)
        rfl

/-! ## Completed-sector transition -/

/-- Persistent active representatives after the selected full sector row.
Terminal separation removes the row's sole zero-residual obstruction before
the third bit is installed. -/
def persistentActiveSamplesOfCompletedSectorBoundary
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent (.two first second))
    (selection : CompletedSectorCanonicalSelection data kind exponent first
      second)
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR) data.output.state
      (adjugate (RawParser.step (RawParser.parse current.core.word)
        (sectorThirdBit selection.sector)).matrix)) :
    PersistentActiveSamples
      (current.core.word ++ [sectorThirdBit selection.sector])
      successorSeparation.state where
  sample next nextRefines := by
    let bit := sectorThirdBit selection.sector
    have nextRefinesOutput : next.box.Refines data.output.state.box :=
      nextRefines.trans successorSeparation.refines
    have nextRefinesSeparation : next.box.Refines data.separation.state.box :=
      nextRefinesOutput.trans data.output_refines_separation
    have nextRefinesTerminal : next.box.Refines data.terminal.numerical.box :=
      nextRefinesOutput.trans data.output.refines
    let block := activeBlockConvergentSample data kind exponent
      selection.sector selection.target squarefree degreeNonzero elimination
        next nextRefinesSeparation
    have inside : next.box.Contains block.point :=
      ⟨block.boxStrict.1.le, block.boxStrict.2.1.le,
        block.boxStrict.2.2.1.le, block.boxStrict.2.2.2.le⟩
    have oldDenominator := separation_denominator_ne data.separation
      (nextRefinesSeparation.contains inside)
    have notTerminal : ¬TerminalSectorAt
        (RawParser.parse current.core.word)
        (RatBox.homographic
          (adjugate (RawParser.parse current.core.word).matrix)
            block.point) :=
      data.terminal.excludes_terminalSectorAt block.point
        (by simpa only [determinant, Mat2.det] using
          RawParser.parse_det_ne current.core.word)
        oldDenominator (nextRefinesTerminal.contains inside)
    have newDenominator := separation_denominator_ne successorSeparation
      (nextRefines.contains inside)
    exact ActiveBoxSample.ofIncrementalStep bit block.point inside
      oldDenominator newDenominator
        (blockSectorBoxSample_inputIncremental_holds_completed_of_phase block
          phase selection.candidate oldDenominator notTerminal)

/-- Persist the newly completed decoder block using a fresh rational witness
in every later winding-box refinement.  Earlier blocks retain their own
witness providers; no single rational point is required to realize the whole
parser history. -/
def persistentObservationsOfCompletedSectorBoundary
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent (.two first second))
    (selection : CompletedSectorCanonicalSelection data kind exponent first
      second)
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR) data.output.state
      (adjugate (RawParser.step (RawParser.parse current.core.word)
        (sectorThirdBit selection.sector)).matrix)) :
    PersistentObservationChain RawParser.identityMatrix
      (parserBlocks
        (current.core.word ++ [sectorThirdBit selection.sector]))
      successorSeparation.state := by
  let bit := sectorThirdBit selection.sector
  have refinesCurrent : successorSeparation.state.box.Refines
      current.core.numerical.box :=
    successorSeparation.refines.trans
      (data.output_refines_separation.trans data.separation.refines)
  let provider :
      (next : WindingOneState p (RatBox.symmetric R hR)) →
      next.box.Refines successorSeparation.state.box →
        BlockObservationSample
          (DecoderBlock.matrixProduct RawParser.identityMatrix
            (parserBlocks current.core.word))
          ⟨kind, exponent, RawParser.sectorOfBits first second bit⟩
          next.box := by
    intro next nextRefines
    have nextRefinesOutput : next.box.Refines data.output.state.box :=
      nextRefines.trans successorSeparation.refines
    have nextRefinesSeparation : next.box.Refines data.separation.state.box :=
      nextRefinesOutput.trans data.output_refines_separation
    have nextRefinesTerminal : next.box.Refines data.terminal.numerical.box :=
      nextRefinesOutput.trans data.output.refines
    let blockSample := activeBlockConvergentSample data kind exponent
      selection.sector selection.target squarefree degreeNonzero elimination
        next nextRefinesSeparation
    have inside : next.box.Contains blockSample.point :=
      ⟨blockSample.boxStrict.1.le, blockSample.boxStrict.2.1.le,
        blockSample.boxStrict.2.2.1.le,
        blockSample.boxStrict.2.2.2.le⟩
    have oldDenominator := separation_denominator_ne data.separation
      (nextRefinesSeparation.contains inside)
    have notTerminal : ¬TerminalSectorAt
        (RawParser.parse current.core.word)
        (RatBox.homographic
          (adjugate (RawParser.parse current.core.word).matrix)
            blockSample.point) :=
      data.terminal.excludes_terminalSectorAt blockSample.point
        (by simpa only [determinant, Mat2.det] using
          RawParser.parse_det_ne current.core.word)
        oldDenominator (nextRefinesTerminal.contains inside)
    have parserEq : RawParser.parse current.core.word =
        ⟨.sector kind exponent (.two first second),
          (RawParser.parse current.core.word).matrix,
          (RawParser.parse current.core.word).history⟩ := by
      cases parsed : RawParser.parse current.core.word with
      | mk parserPhase matrix history =>
          have phase' : parserPhase =
              .sector kind exponent (.two first second) := by
            simpa only [parsed] using phase
          subst parserPhase
          rfl
    have incremental :
        (inputIncrementalAdvanceFormula
          ⟨.sector kind exponent (.two first second),
            (RawParser.parse current.core.word).matrix,
            (RawParser.parse current.core.word).history⟩ bit).Holds
          blockSample.point := by
      rw [← parserEq]
      simpa only [bit] using
        blockSectorBoxSample_inputIncremental_holds_completed_of_phase
          blockSample phase selection.candidate oldDenominator notTerminal
    have newDenominator := separation_denominator_ne successorSeparation
      (nextRefines.contains inside)
    rw [DecoderBlock.matrixProduct_parserBlocks current.core.word]
    apply BlockObservationSample.ofCompletedIncremental
      (RawParser.parse current.core.word).matrix
      (RawParser.parse current.core.word).history kind exponent first second
        bit next.box blockSample.point inside
    · simpa only [determinant, Mat2.det] using
        RawParser.parse_det_ne current.core.word
    · exact oldDenominator
    · rw [RawParserSemantics.step_eq_completeSector
          (RawParser.parse current.core.word) kind exponent first second bit
            phase] at newDenominator
      simpa only [RawParser.completeSector] using newDenominator
    · exact incremental
  let appended :=
    (current.observations.refine refinesCurrent).appendSingleton provider
  exact appended.castBlocks
    (parserBlocks_append_completedSector current.core.word bit phase).symm

/-- Install the selected third bit and return to the ordinary canonical
policy, since completing the block leaves the two-bit sector phase. -/
def nextOfCompletedSectorBoundary
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR))
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent (.two first second))
    (selection : CompletedSectorCanonicalSelection data kind exponent first
      second)
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR) data.output.state
      (adjugate (RawParser.step (RawParser.parse current.core.word)
        (sectorThirdBit selection.sector)).matrix)) :
    State p (RatBox.symmetric R hR) where
  core :=
    { numerical := successorSeparation.state
      word := current.core.word ++ [sectorThirdBit selection.sector] }
  samples := persistentActiveSamplesOfCompletedSectorBoundary data squarefree
    degreeNonzero elimination kind exponent first second phase selection
      successorSeparation
  observations := persistentObservationsOfCompletedSectorBoundary data
    squarefree degreeNonzero elimination kind exponent first second phase
      selection successorSeparation
  completedSector := .canonical (by
    intro completed
    rw [rawParser_parse_append_singleton] at completed
    exact (rawParser_step_not_completed_of_completedSector
      (RawParser.parse current.core.word) (sectorThirdBit selection.sector)
        phase completed).elim)

theorem nextOfCompletedSectorBoundary_refines
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR))
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent (.two first second))
    (selection : CompletedSectorCanonicalSelection data kind exponent first
      second)
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR) data.output.state
      (adjugate (RawParser.step (RawParser.parse current.core.word)
        (sectorThirdBit selection.sector)).matrix)) :
    (nextOfCompletedSectorBoundary current data squarefree degreeNonzero
      elimination kind exponent first second phase selection
        successorSeparation).core.numerical.box.Refines
          current.core.numerical.box :=
  successorSeparation.refines.trans
    (data.output_refines_separation.trans data.separation.refines)

/-- Execute denominator separation after the selected full-row third bit. -/
def resolveCompletedSectorBoundary
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (current : State p (RatBox.symmetric R hR))
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent (.two first second)) : StepResult current := by
  let selection := completedSectorCanonicalSelection data squarefree
    degreeNonzero elimination kind exponent first second phase
  let bit := sectorThirdBit selection.sector
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
      let next := nextOfCompletedSectorBoundary current data squarefree
        degreeNonzero elimination kind exponent first second phase selection
          successorSeparation
      .next bit next
        (nextOfCompletedSectorBoundary_refines current data squarefree
          degreeNonzero elimination kind exponent first second phase selection
            successorSeparation)
        rfl

/-- Resolve every residual sector boundary by a finite canonical-row scan. -/
def StepOrBoundary.resolveSectorBoundaries
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    StepOrBoundary current → StepOrBoundary current
  | .ready result => .ready result
  | .boundary data => by
      let state := RawParser.parse current.core.word
      match phaseEquality : state.phase with
      | .sector kind exponent .zero =>
          exact .ready (resolveSectorZeroBoundary track current data squarefree
            degreeNonzero elimination kind exponent (by
              simpa only [state] using phaseEquality))
      | .sector kind exponent (.one first) =>
          exact .ready (resolveSectorOneBoundary track current data squarefree
            degreeNonzero elimination kind exponent first (by
              simpa only [state] using phaseEquality))
      | .sector kind exponent (.two first second) =>
          exact .ready (resolveCompletedSectorBoundary track current data
            squarefree degreeNonzero elimination kind exponent first second
              (by simpa only [state] using phaseEquality))
      | .initial => exact .boundary data
      | .highUnary count => exact .boundary data
      | .lowUnary count => exact .boundary data
      | .loopUnary count => exact .boundary data

/-- Eliminate the residual boundary constructor in every parser phase. -/
def StepOrBoundary.resolve
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    StepOrBoundary current → StepResult current
  | .ready result => result
  | .boundary data => by
      let state := RawParser.parse current.core.word
      match phaseEquality : state.phase with
      | .initial =>
          exact resolveNonsectorBoundary track current data squarefree
            degreeNonzero zeroNonzero elimination (by
              rintro ⟨kind, exponent, bits, equality⟩
              simp [state, phaseEquality] at equality)
      | .highUnary count =>
          exact resolveNonsectorBoundary track current data squarefree
            degreeNonzero zeroNonzero elimination (by
              rintro ⟨kind, exponent, bits, equality⟩
              simp [state, phaseEquality] at equality)
      | .lowUnary count =>
          exact resolveNonsectorBoundary track current data squarefree
            degreeNonzero zeroNonzero elimination (by
              rintro ⟨kind, exponent, bits, equality⟩
              simp [state, phaseEquality] at equality)
      | .loopUnary count =>
          exact resolveNonsectorBoundary track current data squarefree
            degreeNonzero zeroNonzero elimination (by
              rintro ⟨kind, exponent, bits, equality⟩
              simp [state, phaseEquality] at equality)
      | .sector kind exponent .zero =>
          exact resolveSectorZeroBoundary track current data squarefree
            degreeNonzero elimination kind exponent (by
              simpa only [state] using phaseEquality)
      | .sector kind exponent (.one first) =>
          exact resolveSectorOneBoundary track current data squarefree
            degreeNonzero elimination kind exponent first (by
              simpa only [state] using phaseEquality)
      | .sector kind exponent (.two first second) =>
          exact resolveCompletedSectorBoundary track current data squarefree
            degreeNonzero elimination kind exponent first second (by
              simpa only [state] using phaseEquality)

/-- One total constructive active controller call.  Every branch returns an
exact rational root or one certified raw bit together with a refined winding
box and persistent box--cylinder sample provider. -/
def totalStep
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (current : State p (RatBox.symmetric R hR))
    (clearOwnerLabel : Bool)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    StepResult current :=
  (openStepOrBoundary track track.strict current clearOwnerLabel squarefree
    degreeNonzero zeroNonzero elimination).resolve track squarefree
      degreeNonzero zeroNonzero elimination

end CCLActiveMetricTrack
end FTA
