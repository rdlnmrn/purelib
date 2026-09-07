import CCL.Riemann.ExplicitLegendreGeneratedAPeriod
import CCL.Riemann.ExplicitLegendreGeneratedBPeriod
import CCL.Riemann.PeriodMatrix

/-!
# Finite normalization for the generated Legendre periods

This lightweight downstream module places the sharply initialized generated
A-period in a one-by-one named matrix and converts its uniform positive real
projection into the entry lower certificate required by finite genus-one
normalization.  Both cycle coordinates are the independently generated,
kernel-checked A- and B-period programs.  The proof consumes named transport
and Cauchy bounds; it does not execute either generated subdivision or a
normalization scan.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.PeriodMatrix

/-- The one-by-one matrix containing the generated sharp A-period. -/
def generatedSharpAMatrix (token : Unit) : NamedMatrix 1 :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun _differential _cycle =>
    (generatedSharpAPeriodProgram token).output

@[simp] theorem generatedSharpAMatrix_apply (token : Unit)
    (differential cycle : Fin 1) :
    generatedSharpAMatrix token differential cycle =
      (generatedSharpAPeriodProgram token).output := by
  exact RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

/-- The positive real projection of every public finite sample is already a
directional lower certificate for the sole A-matrix entry. -/
def generatedSharpAPeriodDirectionalLowerCertificate (token : Unit) :
    OneByOneEntryDirectionalLowerCertificate
      (generatedSharpAMatrix token) where
  direction := ⟨1, 0⟩
  directionNormSqPositive := by decide
  lower := generatedSharpUniformRealLower
  positive := generatedSharpUniformRealLower_positive
  sample_lower := by
    intro index
    simp only [generatedSharpAMatrix_apply,
      RFAP.ConstructiveGaussian.Gaussian.re,
      RFAP.ConstructiveGaussian.Gaussian.im, one_mul, zero_mul, add_zero]
    exact generatedSharpAPeriodProgram_sampleRealLower token index

/-- Headline finite nonvanishing certificate: every public sample of the
generated Legendre A-period has a common positive rational squared-norm
lower bound. -/
def generatedSharpAPeriodLowerCertificate (token : Unit) :
    OneByOneEntryCandidateLowerCertificate (generatedSharpAMatrix token) :=
  (generatedSharpAPeriodDirectionalLowerCertificate token
    ).toOneByOneEntryCandidateLowerCertificate

theorem generatedSharpAPeriodLowerCertificate_positive (token : Unit) :
    0 < (generatedSharpAPeriodLowerCertificate token).lowerSq :=
  (generatedSharpAPeriodLowerCertificate token).positive

theorem generatedSharpAPeriodLowerCertificate_sample_lower (token : Unit)
    (index : Nat) :
    (generatedSharpAPeriodLowerCertificate token).lowerSq <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
        ((CCL.ProgressiveSampling.approximation
          ((generatedSharpAMatrix token) 0 0).name).sample index) :=
  (generatedSharpAPeriodLowerCertificate token).sample_lower index

/-- The generated lower certificate directly apartifies the canonical
fraction-free scalar, so inverse acquisition needs no retry scan. -/
def generatedSharpScaledInverse (token : Unit) :
    ScaledInverseCertificate (generatedSharpAMatrix token) :=
  (generatedSharpAPeriodLowerCertificate token
    ).toScalarCandidateLowerCertificate.toScaledInverseCertificate

/-- A complete genus-one cycle family using both independently generated
sharp period cycles. -/
def generatedPeriodCycles (token : Unit) :
    CCL.Riemann.LiftedPaths.LiftedSymplecticCycles 2 1 where
  aCycle := fun _ => (generatedSharpSchedule token).cycle
  bCycle := fun _ =>
    (CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpSchedule
      token).cycle

/-- Explicit finite period data whose A and B entries are both generated,
sharply initialized certified programs. -/
def generatedPeriodData (token : Unit) :
    PeriodData CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve where
  cycles := generatedPeriodCycles token
  aProgram := by
    intro differential cycle
    have differentialZero : differential = 0 := by
      apply Fin.ext
      omega0
    have cycleZero : cycle = 0 := by
      apply Fin.ext
      omega0
    subst differential
    subst cycle
    exact generatedSharpAPeriodProgram token
  bProgram := by
    intro differential cycle
    have differentialZero : differential = 0 := by
      apply Fin.ext
      omega0
    have cycleZero : cycle = 0 := by
      apply Fin.ext
      omega0
    subst differential
    subst cycle
    exact
      CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpBPeriodProgram
        token

@[simp] theorem generatedPeriodData_aCycle (token : Unit) :
    (generatedPeriodData token).cycles.aCycle 0 =
      (generatedSharpSchedule token).cycle := rfl

@[simp] theorem generatedPeriodData_bCycle (token : Unit) :
    (generatedPeriodData token).cycles.bCycle 0 =
      (CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpSchedule
        token).cycle := rfl

@[simp] theorem generatedPeriodData_aProgram (token : Unit) :
    (generatedPeriodData token).aProgram 0 0 =
      generatedSharpAPeriodProgram token := rfl

@[simp] theorem generatedPeriodData_bProgram (token : Unit) :
    (generatedPeriodData token).bProgram 0 0 =
      CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpBPeriodProgram
        token := rfl

/-- A compact proof package connecting the public genus-one period data to
the actual generated traversal data.  In particular, the A and B parent
lists have checked consecutive-row coverage, their source runs close with
exactly two sheet switches, sharp preparation retains those source runs, and
the public period cycles and programs are the resulting generated objects. -/
structure GeneratedPeriodGeometryCertificate (token : Unit) : Prop where
  aRows : CCL.Riemann.GeneratedCycleProvenance.PositionTrace.Coverage
    GeneratedTransportParent.position
    (generatedClosedRun token).transportParents 0
    nonstationaryCellCount
  bRows : CCL.Riemann.GeneratedCycleProvenance.PositionTrace.Coverage
    CCL.Riemann.ExplicitLegendreGeneratedBCertificate.GeneratedTransportParent.position
    (CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedClosedRun
      token).transportParents 0
    CCL.Riemann.ExplicitLegendreGeneratedBCertificate.nonstationaryCellCount
  aPositions : (generatedClosedRun token).transportParents.map
      GeneratedTransportParent.position =
    List.range' 0 nonstationaryCellCount
  bPositions :
    (CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedClosedRun
      token).transportParents.map
        CCL.Riemann.ExplicitLegendreGeneratedBCertificate.GeneratedTransportParent.position =
      List.range' 0
        CCL.Riemann.ExplicitLegendreGeneratedBCertificate.nonstationaryCellCount
  aClosed : (generatedClosedRun token).finish =
    (generatedClosedRun token).start
  bClosed :
    (CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedClosedRun
      token).finish =
    (CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedClosedRun
      token).start
  aSwitchCount : (generatedSharpInitialState token).chain.switchCount = 2
  bSwitchCount :
    (CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpInitialState
      token).chain.switchCount = 2
  aPreparedSource : (generatedSharpPreparedRun token).source =
    generatedClosedRun token
  bPreparedSource :
    (CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpPreparedRun
      token).source =
    CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedClosedRun token
  aCycle : (generatedPeriodData token).cycles.aCycle 0 =
    (generatedSharpSchedule token).cycle
  bCycle : (generatedPeriodData token).cycles.bCycle 0 =
    (CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpSchedule
      token).cycle
  aProgram : (generatedPeriodData token).aProgram 0 0 =
    generatedSharpAPeriodProgram token
  bProgram : (generatedPeriodData token).bProgram 0 0 =
    CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpBPeriodProgram
      token

/-- Closed aggregate provenance for both generated period coordinates. -/
theorem generatedPeriodGeometryCertificate (token : Unit) :
    GeneratedPeriodGeometryCertificate token where
  aRows := generatedClosedRun_positionCoverage token
  bRows :=
    CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedClosedRun_positionCoverage
      token
  aPositions := generatedClosedRun_positions_eq_range token
  bPositions :=
    CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedClosedRun_positions_eq_range
      token
  aClosed := generatedClosedRun_closed token
  bClosed :=
    CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedClosedRun_closed
      token
  aSwitchCount := generatedSharpInitialState_switchCount token
  bSwitchCount :=
    CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpInitialState_switchCount
      token
  aPreparedSource := generatedSharpPreparedRun_source token
  bPreparedSource :=
    CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpPreparedRun_source
      token
  aCycle := generatedPeriodData_aCycle token
  bCycle := generatedPeriodData_bCycle token
  aProgram := generatedPeriodData_aProgram token
  bProgram := generatedPeriodData_bProgram token

/-! ## Canonical symplectic-basis provenance -/

/-- The finite symplectic basis built from the same three rational branch
owners as the generated A/B meshes. -/
def generatedCanonicalSymplecticBasis :=
  CCL.Riemann.BranchCutLifts.symplecticBasisOfData
    CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
    (CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseBranchData ())

private theorem generatedCanonicalACycle_eq_rawTarget :
    ((generatedCanonicalSymplecticBasis.cycles.aCycle
      (0 : Fin 1)).liftedPath 0) =
        CCL.Riemann.ExplicitLegendrePreparedPeriods.rawACycleTarget () := by
  change
    (((CCL.Riemann.ExplicitLegendrePreparedPeriods.branchFamily ()
      ).symplecticCycles.aCycle (0 : Fin 1)).liftedPath 0) =
      CCL.Riemann.ExplicitLegendrePreparedPeriods.rawACycleTarget ()
  unfold CCL.Riemann.ExplicitLegendrePreparedPeriods.rawACycleTarget
    CCL.Riemann.ExplicitLegendrePreparedPeriods.branchFamily
  rw [CCL.Riemann.BranchCutLifts.canonicalACycle_liftedPath_ofData]
  rfl

private theorem generatedCanonicalBCycle_eq_rawTarget :
    ((generatedCanonicalSymplecticBasis.cycles.bCycle
      (0 : Fin 1)).liftedPath 0) =
        CCL.Riemann.ExplicitLegendrePreparedPeriods.rawBCycleTarget () := by
  change
    (((CCL.Riemann.ExplicitLegendrePreparedPeriods.branchFamily ()
      ).symplecticCycles.bCycle (0 : Fin 1)).liftedPath 0) =
      CCL.Riemann.ExplicitLegendrePreparedPeriods.rawBCycleTarget ()
  unfold CCL.Riemann.ExplicitLegendrePreparedPeriods.rawBCycleTarget
    CCL.Riemann.ExplicitLegendrePreparedPeriods.branchFamily
  rfl

/-- A shallow, inspectable chain from the canonical genus-one intersection
table to the exact generated period cycles.  The row fields target the actual
retained parent lists, while the working-path and leg fields expose that their
canonical row lookup is built from scheduled subdivisions of the raw A/B
branch-cut representatives.  Thus the generated pair is not certified merely
by assigning two arbitrary closed cycles the labels `aCycle` and `bCycle`. -/
structure GeneratedSymplecticBasisProvenance (token : Unit) : Prop where
  canonicalA :
    ((generatedCanonicalSymplecticBasis.cycles.aCycle
      (0 : Fin 1)).liftedPath 0) =
        CCL.Riemann.ExplicitLegendrePreparedPeriods.rawACycleTarget ()
  canonicalB :
    ((generatedCanonicalSymplecticBasis.cycles.bCycle
      (0 : Fin 1)).liftedPath 0) =
        CCL.Riemann.ExplicitLegendrePreparedPeriods.rawBCycleTarget ()
  a_a : CCL.Riemann.CellularHomology.intersection
      (generatedCanonicalSymplecticBasis.aTrace (0 : Fin 1))
      (generatedCanonicalSymplecticBasis.aTrace (0 : Fin 1)) = 0
  b_b : CCL.Riemann.CellularHomology.intersection
      (generatedCanonicalSymplecticBasis.bTrace (0 : Fin 1))
      (generatedCanonicalSymplecticBasis.bTrace (0 : Fin 1)) = 0
  a_b : CCL.Riemann.CellularHomology.intersection
      (generatedCanonicalSymplecticBasis.aTrace (0 : Fin 1))
      (generatedCanonicalSymplecticBasis.bTrace (0 : Fin 1)) = 1
  preparedBasis :
    CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      (CCL.Riemann.ExplicitLegendrePreparedPeriods.periodData ()).cycles
      generatedCanonicalSymplecticBasis.cycles
  aConnector :
    CCL.Riemann.ExplicitLegendrePreparedPeriods.workingAConnector =
      CCL.Riemann.PreparedClearPathModels.dyadicRefinePathScheduled
        (CCL.Riemann.ExplicitLegendrePreparedPeriods.rawConnector 0 1)
        (CCL.Riemann.ExplicitLegendrePreparedPeriods.rawConnector_withinAmbient
          0 1)
        CCL.Riemann.ExplicitLegendrePreparedPeriods.aConnectorOuterDepths
  aRightBoundary :
    CCL.Riemann.ExplicitLegendrePreparedPeriods.workingRightBoundary =
      CCL.Riemann.PreparedClearPathModels.dyadicRefinePathScheduled
        (CCL.Riemann.ExplicitLegendrePreparedPeriods.rawBoundary 1)
        (CCL.Riemann.ExplicitLegendrePreparedPeriods.rawBoundary_withinAmbient
          1)
        CCL.Riemann.ExplicitLegendrePreparedPeriods.rightBoundaryOuterDepths
  aBackward :
    CCL.Riemann.ExplicitLegendrePreparedPeriods.workingABackwardConnector =
      CCL.Riemann.BranchCutLifts.ClearPath.reverse
        CCL.Riemann.ExplicitLegendrePreparedPeriods.workingAConnector
  aLeftBoundary :
    CCL.Riemann.ExplicitLegendrePreparedPeriods.workingLeftBoundary =
      CCL.Riemann.PreparedClearPathModels.dyadicRefinePathScheduled
        (CCL.Riemann.ExplicitLegendrePreparedPeriods.rawBoundary 0)
        (CCL.Riemann.ExplicitLegendrePreparedPeriods.rawBoundary_withinAmbient
          0)
        CCL.Riemann.ExplicitLegendrePreparedPeriods.leftBoundaryOuterDepths
  aLegs : generatedALegs =
      generatedLegPackages
          CCL.Riemann.ExplicitLegendrePreparedPeriods.workingAConnector
          CCL.Riemann.ExplicitLegendrePreparedPeriods.workingAConnector_withinAmbient
          (List.replicate
            CCL.Riemann.ExplicitLegendrePreparedPeriods.workingAConnector.segmentCount
            CCL.Riemann.ExplicitLegendrePreparedPeriods.connectorInnerDepth) ++
        (generatedLegPackages
            CCL.Riemann.ExplicitLegendrePreparedPeriods.workingRightBoundary
            CCL.Riemann.ExplicitLegendrePreparedPeriods.workingRightBoundary_withinAmbient
            (List.replicate 4
                CCL.Riemann.ExplicitLegendrePreparedPeriods.rightBoundaryInnerDepth ++
              List.replicate 4
                (CCL.Riemann.ExplicitLegendrePreparedPeriods.rightBoundaryInnerDepth + 1) ++
              List.replicate 4
                CCL.Riemann.ExplicitLegendrePreparedPeriods.rightBoundaryInnerDepth ++
              List.replicate 8
                (CCL.Riemann.ExplicitLegendrePreparedPeriods.rightBoundaryInnerDepth + 1)) ++
          (generatedLegPackages
              CCL.Riemann.ExplicitLegendrePreparedPeriods.workingABackwardConnector
              CCL.Riemann.ExplicitLegendrePreparedPeriods.workingABackwardConnector_withinAmbient
              (List.replicate
                CCL.Riemann.ExplicitLegendrePreparedPeriods.workingABackwardConnector.segmentCount
                CCL.Riemann.ExplicitLegendrePreparedPeriods.connectorInnerDepth) ++
            generatedLegPackages
              CCL.Riemann.ExplicitLegendrePreparedPeriods.workingLeftBoundary
              CCL.Riemann.ExplicitLegendrePreparedPeriods.workingLeftBoundary_withinAmbient
              (List.replicate
                CCL.Riemann.ExplicitLegendrePreparedPeriods.workingLeftBoundary.segmentCount
                CCL.Riemann.ExplicitLegendrePreparedPeriods.leftBoundaryInnerDepth)))
  bConnector :
    CCL.Riemann.ExplicitLegendrePreparedPeriods.workingBConnector =
      CCL.Riemann.PreparedClearPathModels.dyadicRefinePathScheduled
        (CCL.Riemann.ExplicitLegendrePreparedPeriods.rawConnector 0 2)
        (CCL.Riemann.ExplicitLegendrePreparedPeriods.rawConnector_withinAmbient
          0 2)
        CCL.Riemann.ExplicitLegendrePreparedPeriods.bConnectorOuterDepths
  bBackward :
    CCL.Riemann.ExplicitLegendrePreparedPeriods.workingBBackwardConnector =
      CCL.Riemann.BranchCutLifts.ClearPath.reverse
        CCL.Riemann.ExplicitLegendrePreparedPeriods.workingBConnector
  bLegs :
    CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedBLegs =
      CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedLegPackages
          CCL.Riemann.ExplicitLegendrePreparedPeriods.workingBConnector
          CCL.Riemann.ExplicitLegendrePreparedPeriods.workingBConnector_withinAmbient
          (List.replicate
            CCL.Riemann.ExplicitLegendrePreparedPeriods.workingBConnector.segmentCount
            CCL.Riemann.ExplicitLegendrePreparedPeriods.bConnectorInnerDepth) ++
        CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedLegPackages
          CCL.Riemann.ExplicitLegendrePreparedPeriods.workingBBackwardConnector
          CCL.Riemann.ExplicitLegendrePreparedPeriods.workingBBackwardConnector_withinAmbient
          (List.replicate
            CCL.Riemann.ExplicitLegendrePreparedPeriods.workingBBackwardConnector.segmentCount
            CCL.Riemann.ExplicitLegendrePreparedPeriods.bConnectorInnerDepth)
  aRows : CCL.Riemann.GeneratedCycleProvenance.PositionTrace.Coverage
    GeneratedTransportParent.position
    (generatedClosedRun token).transportParents 0 nonstationaryCellCount
  bRows : CCL.Riemann.GeneratedCycleProvenance.PositionTrace.Coverage
    CCL.Riemann.ExplicitLegendreGeneratedBCertificate.GeneratedTransportParent.position
    (CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedClosedRun
      token).transportParents 0
    CCL.Riemann.ExplicitLegendreGeneratedBCertificate.nonstationaryCellCount
  aPreparedSource : (generatedSharpPreparedRun token).source =
    generatedClosedRun token
  bPreparedSource :
    (CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpPreparedRun
      token).source =
      CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedClosedRun token
  aScheduleInitial : (generatedSharpSchedule token).initial =
    (generatedSharpPreparedRun token).state
  bScheduleInitial :
    (CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpSchedule
      token).initial =
      (CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpPreparedRun
        token).state
  aCycle : (generatedPeriodData token).cycles.aCycle 0 =
    (generatedSharpSchedule token).cycle
  bCycle : (generatedPeriodData token).cycles.bCycle 0 =
    (CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpSchedule
      token).cycle

/-- Closed data-level proof that the generated A/B pair comes from the exact
rational branch-cut symplectic basis and its scheduled finite meshes. -/
theorem generatedSymplecticBasisProvenance (token : Unit) :
    GeneratedSymplecticBasisProvenance token where
  canonicalA :=
    generatedCanonicalACycle_eq_rawTarget
  canonicalB :=
    generatedCanonicalBCycle_eq_rawTarget
  a_a := generatedCanonicalSymplecticBasis.a_a 0 0
  b_b := generatedCanonicalSymplecticBasis.b_b 0 0
  a_b := by
    simpa using generatedCanonicalSymplecticBasis.a_b (0 : Fin 1) (0 : Fin 1)
  preparedBasis :=
    CCL.Riemann.ExplicitLegendrePreparedPeriods.periodData_realizes_basis
  aConnector := rfl
  aRightBoundary := rfl
  aBackward := rfl
  aLeftBoundary := rfl
  aLegs := rfl
  bConnector := rfl
  bBackward := rfl
  bLegs := rfl
  aRows := generatedClosedRun_positionCoverage token
  bRows :=
    CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedClosedRun_positionCoverage
      token
  aPreparedSource := generatedSharpPreparedRun_source token
  bPreparedSource :=
    CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpPreparedRun_source
      token
  aScheduleInitial := rfl
  bScheduleInitial := rfl
  aCycle := generatedPeriodData_aCycle token
  bCycle := generatedPeriodData_bCycle token

theorem generatedPeriodData_aMatrix_eq (token : Unit) :
    (generatedPeriodData token).aMatrix = generatedSharpAMatrix token := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro differential cycle
  have differentialZero : differential = 0 := by
    apply Fin.ext
    omega0
  have cycleZero : cycle = 0 := by
    apply Fin.ext
    omega0
  subst differential
  subst cycle
  rfl

/-- The same finite lower certificate, reindexed onto the A matrix of the
complete generated period data. -/
def generatedPeriodAPeriodLowerCertificate (token : Unit) :
    OneByOneEntryCandidateLowerCertificate
      (generatedPeriodData token).aMatrix := by
  rw [generatedPeriodData_aMatrix_eq]
  exact generatedSharpAPeriodLowerCertificate token

def generatedPeriodScaledInverse (token : Unit) :
    ScaledInverseCertificate (generatedPeriodData token).aMatrix :=
  (generatedPeriodAPeriodLowerCertificate token
    ).toScalarCandidateLowerCertificate.toScaledInverseCertificate

/-- Fully normalized explicit period data obtained directly from the named
finite A-period lower theorem. -/
def generatedNormalizedPeriodData (token : Unit) :
    NormalizedPeriodData
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve :=
  NormalizedPeriodData.ofScaledInverse (generatedPeriodData token)
    (generatedPeriodScaledInverse token)

/-- The normalization wrapper retains exactly the generated period data and
the scaled inverse derived from its finite A-entry lower certificate. -/
structure GeneratedNormalizationCertificate (token : Unit) : Prop where
  periodData : (generatedNormalizedPeriodData token).toPeriodData =
    generatedPeriodData token
  scaledInverse : (generatedNormalizedPeriodData token).aInverse =
    generatedPeriodScaledInverse token

/-- Closed provenance for the data used by generated normalization. -/
theorem generatedNormalizationCertificate (token : Unit) :
    GeneratedNormalizationCertificate token where
  periodData := rfl
  scaledInverse := rfl

/-- The productive normalized genus-one ratio supplied by the generated
finite period data. -/
def generatedNormalizedRatio (token : Unit) :=
  (generatedNormalizedPeriodData token).omega 0 0

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
