import CCL.Riemann.PreparedDirectDyadicRefinements
import CCL.Riemann.PreparedCycleModels
import CCL.Riemann.PreparedSwitchedRefinements

/-!
# Persistent integration from prepared subdivision schedules

This module turns a displayed family of accepted prepared subdivisions into a
Gaussian refinement program.  The schedule retains the finite cross-level
partition and rational bound calculations; root transport, coefficient-state
alignment, and uniform algebraic semantics are constructed automatically from
each accepted subdivision.
-/

namespace CCL.Riemann.PreparedRefinementPrograms

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.BranchCuts
open CCL.Riemann.BranchCutLifts
open CCL.Riemann.LiftedPaths

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Box := RFAP.Boxes.Box
abbrev Owner := CCL.Riemann.SquareRootContinuationChain.Owner
abbrev Endpoint := CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint
abbrev PathModel := CCL.ProgressiveGaussianIntegration.PathModel
abbrev RefinementProgram :=
  CCL.ProgressiveGaussianIntegration.RefinementProgram
abbrev CompatibleConstantPathRefinement :=
  CCL.ProgressiveGaussianIntegration.PathModel.CompatibleConstantPathRefinement
abbrev PreparedSubdivision {polynomial :
    RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter))) :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision segment within left owner

/-- The automatically aligned, uniformly certified path model attached to one
accepted prepared subdivision. -/
def alignedModel {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) : PathModel :=
  CCL.Riemann.PreparedSubdivisionModels.pathModel
    (CCL.Riemann.PreparedSubdivisionModels.certifyAutomaticallyAlignedSubdivision
      curve differential sheet subdivision)

/-- A finite prepared refinement schedule.

Every index computes one finite accepted subdivision.  The remaining fields
are explicit rational partition, allowance, and boundedness certificates; no
completed integral or limiting path is stored. -/
structure Schedule {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : Endpoint)
    (owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter)))
    (sheet : Fin 2) where
  subdivision : Nat -> PreparedSubdivision segment within left owner
  refinements : forall {earlier later : Nat}, earlier <= later ->
    CompatibleConstantPathRefinement
      (alignedModel curve differential sheet (subdivision earlier)).cells
      (alignedModel curve differential sheet (subdivision later)).cells
  errorScale : Coordinate
  errorScale_nonnegative : 0 <= errorScale
  modelAllowance_le : forall index,
    (alignedModel curve differential sheet
      (subdivision index)).aggregateAllowance <=
        CCL.FiniteGeometric.quarterRadius errorScale index
  comparisonAllowance_le : forall {earlier later : Nat}
      (order : earlier <= later),
    (refinements order).comparisonAllowance <=
      CCL.FiniteGeometric.quarterRadius errorScale earlier
  centerBound : Coordinate
  centerBound_nonnegative : 0 <= centerBound
  sample_bounded : forall index,
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (alignedModel curve differential sheet
        (subdivision index)).integralSample <= centerBound

namespace Schedule

/-- Forget only the prepared origin of the models, retaining the stronger
compatible constant-refinement program. -/
def toCompatibleConstantRefinementProgram {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    {sheet : Fin 2}
    (schedule : Schedule curve differential segment within left owner sheet) :
    CCL.ProgressiveGaussianIntegration.CompatibleConstantRefinementProgram
      where
  model := fun index =>
    alignedModel curve differential sheet (schedule.subdivision index)
  refinements := schedule.refinements
  errorScale := schedule.errorScale
  errorScale_nonneg := schedule.errorScale_nonnegative
  modelAllowance_le := schedule.modelAllowance_le
  comparisonAllowance_le := schedule.comparisonAllowance_le
  centerBound := schedule.centerBound
  centerBound_nonneg := schedule.centerBound_nonnegative
  sample_bounded := schedule.sample_bounded

/-- The persistent Gaussian integral computed by a prepared schedule. -/
def integral {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    {sheet : Fin 2}
    (schedule : Schedule curve differential segment within left owner sheet) :
    RefinementProgram :=
  schedule.toCompatibleConstantRefinementProgram.toRefinementProgram

@[simp] theorem integral_model {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    {sheet : Fin 2}
    (schedule : Schedule curve differential segment within left owner sheet)
    (index : Nat) :
    schedule.integral.model index =
      alignedModel curve differential sheet (schedule.subdivision index) :=
  rfl

/-- Uniform algebraic semantics are automatic at every finite refinement
index of a prepared schedule. -/
def certificates {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    {sheet : Fin 2}
    (schedule : Schedule curve differential segment within left owner sheet)
    (index : Nat) :
    UniformPathCertificates curve differential
      (schedule.integral.model index).cells
      (ClearPath.liftOnSheet sheet
        (schedule.subdivision index).toClearPath) :=
  (CCL.Riemann.PreparedSubdivisionModels.certifyAutomaticallyAlignedSubdivision
    curve differential sheet (schedule.subdivision index)).certificates

/-- Every positive request is answered by a finite prepared subdivision whose
aggregate semantic allowance is below the request. -/
theorem finite_subdivision_accurate {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    {sheet : Fin 2}
    (schedule : Schedule curve differential segment within left owner sheet)
    (current : Nat) (target : Coordinate) (positive : 0 < target) :
    let index := schedule.integral.approximation.refineIndex current target
      positive
    (schedule.integral.model index).aggregateAllowance < target :=
  schedule.integral.finite_subdivision_accurate current target positive

end Schedule

/-! ## Total direct open-path schedules -/

/-- One open direct state whose recursively refined geometry is shared by
every differential in a displayed finite family.  Keeping this interface
open is essential for branch-cut cycles: the nonstationary banks are refined
here, while exact stationary sheet transitions are inserted only when the
closed cycle is assembled. -/
structure FiniteDifferentialDirectPathSchedule {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus) where
  initial :
    CCL.Riemann.PreparedDirectDyadicRefinements.DirectRefinementState curve
      source
  targets : List (Differential genus)

namespace FiniteDifferentialDirectPathSchedule

/-- The differential-independent lifted bank at one finite refinement
index. -/
def path {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (schedule : FiniteDifferentialDirectPathSchedule curve source)
    (index : Nat) : LiftedPath 2 schedule.initial.start
      schedule.initial.finish :=
  CCL.Riemann.PreparedDirectDyadicRefinements.finiteDifferentialRefinementPath
    schedule.initial schedule.targets index

/-- Certified finite model of any differential on the exact common open
bank. -/
def certifiedLift {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (schedule : FiniteDifferentialDirectPathSchedule curve source)
    (differential : Differential genus) (index : Nat) :
    CCL.Riemann.PreparedCycleModels.CertifiedLift curve differential
      (schedule.path index) where
  cells :=
    (CCL.Riemann.PreparedDirectDyadicRefinements.finiteDifferentialRefinementModel
      schedule.initial schedule.targets differential index).cells
  certificates :=
    CCL.Riemann.PreparedDirectDyadicRefinements.finiteDifferentialRefinementPathCertificates
      schedule.initial schedule.targets differential index

/-- Executable refinement program of one displayed family member on the
common open bank. -/
def integral {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (schedule : FiniteDifferentialDirectPathSchedule curve source)
    (differential : Differential genus)
    (member : differential ∈ schedule.targets) : RefinementProgram :=
  (CCL.Riemann.PreparedDirectDyadicRefinements.finiteDifferentialSequentialProgram
    schedule.initial schedule.targets differential member).toRefinementProgram

@[simp] theorem integral_model_cells {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (schedule : FiniteDifferentialDirectPathSchedule curve source)
    (differential : Differential genus)
    (member : differential ∈ schedule.targets) (index : Nat) :
    ((schedule.integral differential member).model index).cells =
      (schedule.certifiedLift differential index).cells := rfl

/-- Extract the shared direct bank schedule from a checked finite dyadic
path on one sheet. -/
def ofCheckedDyadic {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus) (targets : List (Differential genus))
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (checked :
      CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic depth
        rootDiameter rootDiameterPositive path owner) :
    FiniteDifferentialDirectPathSchedule curve source where
  initial :=
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.stateOfCheckedDyadic
      curve source sheet checked
  targets := targets

end FiniteDifferentialDirectPathSchedule

/-! ## Total direct closed-path schedules -/

/-- One closed centered prepared path from which all later certified finite
models and the consecutive integration program are computed. -/
structure DirectClosedSchedule {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus) where
  initial :
    CCL.Riemann.PreparedDirectDyadicRefinements.DirectRefinementState curve
      differential
  closed : initial.finish = initial.start

namespace DirectClosedSchedule

/-- Certified closed lifted model at one requested direct-refinement index. -/
def certifiedModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (schedule : DirectClosedSchedule curve differential)
    (index : Nat) :
    CCL.Riemann.PreparedCycleModels.CertifiedClosedModel curve differential where
  lifted :=
    CCL.Riemann.PreparedDirectDyadicRefinements.directRefinementClosedLift
      schedule.initial schedule.closed index
  cells :=
    (CCL.Riemann.PreparedDirectDyadicRefinements.directRefinementStates
      schedule.initial index).parents.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model
  certificates :=
    CCL.Riemann.PreparedDirectDyadicRefinements.directRefinementClosedCertificates
      schedule.initial schedule.closed index

/-- The executable Gaussian refinement program attached to the closed path. -/
def integral {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (schedule : DirectClosedSchedule curve differential) : RefinementProgram :=
  (CCL.Riemann.PreparedDirectDyadicRefinements.directSequentialProgram
    schedule.initial).toRefinementProgram

@[simp] theorem integral_model_cells {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (schedule : DirectClosedSchedule curve differential)
    (index : Nat) :
    (schedule.integral.model index).cells =
      (schedule.certifiedModel index).cells := rfl

/-- Forget only the direct prepared origin, retaining the ordinary certified
closed-model schedule consumed by the period layer. -/
def toCertifiedSchedule {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (schedule : DirectClosedSchedule curve differential) :
    CCL.Riemann.PreparedCycleModels.Schedule curve differential where
  model := schedule.certifiedModel
  integral := schedule.integral
  cells_eq := schedule.integral_model_cells

/-- Build the total closed schedule from an already canonical centered chain. -/
def ofCenteredPathChain {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parents : List
      (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredEdge curve
        differential)}
    {start finish : LiftedPoint 2}
    (chain :
      CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain parents
        (start := start) (finish := finish))
    (proper : CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents)
    (closed : finish = start) : DirectClosedSchedule curve differential where
  initial := chain.toDirectRefinementState proper
  closed := closed

end DirectClosedSchedule

/-! ## Common geometry for a finite differential family -/

/-- One closed direct state whose recursively refined geometry is shared by
every differential in a displayed finite family. -/
structure FiniteDifferentialDirectClosedSchedule {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus) where
  initial :
    CCL.Riemann.PreparedDirectDyadicRefinements.DirectRefinementState curve
      source
  targets : List (Differential genus)
  closed : initial.finish = initial.start

namespace FiniteDifferentialDirectClosedSchedule

/-- The differential-independent persistent closed lifted cycle. -/
def cycle {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (schedule : FiniteDifferentialDirectClosedSchedule curve source) :
    LiftedCycleRefinement 2 where
  liftedPath := fun index =>
    CCL.Riemann.PreparedDirectDyadicRefinements.finiteDifferentialRefinementClosedLift
      schedule.initial schedule.targets
        schedule.closed index

/-- Certified finite model of any target differential on the exact common
closed lifted path. -/
def certifiedModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (schedule : FiniteDifferentialDirectClosedSchedule curve source)
    (differential : Differential genus) (index : Nat) :
    CCL.Riemann.PreparedCycleModels.CertifiedClosedModel curve differential
    where
  lifted := schedule.cycle.liftedPath index
  cells :=
    (CCL.Riemann.PreparedDirectDyadicRefinements.finiteDifferentialRefinementModel
      schedule.initial schedule.targets
        differential index).cells
  certificates :=
    CCL.Riemann.PreparedDirectDyadicRefinements.finiteDifferentialRefinementClosedCertificates
      schedule.initial
        schedule.targets differential schedule.closed index

/-- Executable refinement program of one displayed family member. -/
def integral {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (schedule : FiniteDifferentialDirectClosedSchedule curve source)
    (differential : Differential genus)
    (member : differential ∈ schedule.targets) : RefinementProgram :=
  (CCL.Riemann.PreparedDirectDyadicRefinements.finiteDifferentialSequentialProgram
    schedule.initial schedule.targets
      differential member).toRefinementProgram

@[simp] theorem integral_model_cells {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (schedule : FiniteDifferentialDirectClosedSchedule curve source)
    (differential : Differential genus)
    (member : differential ∈ schedule.targets) (index : Nat) :
    ((schedule.integral differential member).model index).cells =
      (schedule.certifiedModel differential index).cells := rfl

/-- Certified period program whose cycle is definitionally the common family
cycle, independent of the selected differential. -/
def certifiedPeriodProgram {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (schedule : FiniteDifferentialDirectClosedSchedule curve source)
    (differential : Differential genus)
    (member : differential ∈ schedule.targets) :
    CertifiedPeriodProgram curve differential schedule.cycle where
  integral := schedule.integral differential member
  certificates := by
    intro index
    rw [schedule.integral_model_cells differential member index]
    exact (schedule.certifiedModel differential index).certificates

end FiniteDifferentialDirectClosedSchedule

/-- Materialized finite list of the standard basis differentials. -/
def standardDifferentials (genus : Nat) : List (Differential genus) :=
  List.ofFn CCL.Riemann.PeriodMatrix.standardDifferential

@[simp] theorem standardDifferentials_one :
    standardDifferentials 1 =
      [CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1)] := rfl

theorem standardDifferential_mem_standardDifferentials {genus : Nat}
    (index : Fin genus) :
    CCL.Riemann.PeriodMatrix.standardDifferential index ∈
      standardDifferentials genus :=
  List.mem_ofFn.mpr ⟨index, rfl⟩

/-! ## Standard schedules with exact sheet transitions -/

/-- A prepared branch-cut cycle equipped with the total common-geometry
switched schedule for every standard differential. -/
structure StandardSwitchedClosedSchedule {genus : Nat}
    (curve : HyperellipticCurve genus) where
  source : Differential genus
  prepared : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve

namespace StandardSwitchedClosedSchedule

/-- The underlying finite-family switched schedule. -/
def toFiniteDifferential {genus : Nat}
    {curve : HyperellipticCurve genus}
    (schedule : StandardSwitchedClosedSchedule curve) :
    CCL.Riemann.PreparedSwitchedRefinements.FiniteDifferentialSwitchedClosedSchedule
      curve schedule.source :=
  CCL.Riemann.PreparedSwitchedRefinements.scheduleOfPreparedCycleData curve
    schedule.source (standardDifferentials genus) schedule.prepared

/-- The persistent closed cycle containing the exact stationary switch cells. -/
def cycle {genus : Nat}
    {curve : HyperellipticCurve genus}
    (schedule : StandardSwitchedClosedSchedule curve) :
    LiftedCycleRefinement 2 :=
  schedule.toFiniteDifferential.cycle

/-- Certified program for one standard differential on the exact common
switched geometry. -/
def certifiedPeriodProgram {genus : Nat}
    {curve : HyperellipticCurve genus}
    (schedule : StandardSwitchedClosedSchedule curve)
    (differential : Fin genus) :
    CertifiedPeriodProgram curve
      (CCL.Riemann.PeriodMatrix.standardDifferential differential)
      schedule.cycle :=
  schedule.toFiniteDifferential.certifiedPeriodProgram
    (CCL.Riemann.PeriodMatrix.standardDifferential differential)
    (standardDifferential_mem_standardDifferentials differential)

/-- Exact switched scale of a standard period program, exposed without
unfolding the dependent certificate fields of the enclosing program. -/
theorem certifiedPeriodProgram_errorScale {genus : Nat}
    {curve : HyperellipticCurve genus}
    (schedule : StandardSwitchedClosedSchedule curve)
    (differential : Fin genus) :
    (schedule.certifiedPeriodProgram differential).integral.errorScale =
      schedule.toFiniteDifferential.initial.chain.switchFactor *
        (4 * (3 * schedule.toFiniteDifferential.initial.scheduleBase
          schedule.toFiniteDifferential.targets)) :=
  CCL.Riemann.PreparedSwitchedRefinements.DirectSwitchedState.integral_errorScale
    schedule.toFiniteDifferential.initial schedule.toFiniteDifferential.targets
      (CCL.Riemann.PeriodMatrix.standardDifferential differential)
      (standardDifferential_mem_standardDifferentials differential)

/-- Every prepared standard period program retains the two exact stationary
sheet-transition cells, hence has a nonempty finite model at every request. -/
theorem certifiedPeriodProgram_model_cells_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    (schedule : StandardSwitchedClosedSchedule curve)
    (differential : Fin genus) (index : Nat) :
    0 < ((schedule.certifiedPeriodProgram differential).integral.model
      index).cells.length := by
  unfold certifiedPeriodProgram toFiniteDifferential
  apply
    CCL.Riemann.PreparedSwitchedRefinements.scheduleOfPreparedCycleData_integral_model_cells_positive

end StandardSwitchedClosedSchedule

/-- Exact switched schedules for every standard A- and B-cycle. -/
structure StandardSwitchedSymplecticSchedule {genus : Nat}
    (curve : HyperellipticCurve genus) where
  aCycle : Fin genus -> StandardSwitchedClosedSchedule curve
  bCycle : Fin genus -> StandardSwitchedClosedSchedule curve

namespace StandardSwitchedSymplecticSchedule

/-- Fully prepared finite-cut geometry for one standard A-cycle.  The first
`g` standard pairs are finite even in odd degree, so no endpoint or owner
certificate is supplied by the caller. -/
def preparedACycle {genus : Nat} (curve : HyperellipticCurve genus)
    (index : Fin genus) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData curve := by
  let configuration :=
    CCL.Riemann.BranchConfiguration.configuration curve
  let higher :=
    CCL.Riemann.BranchCutLifts.degreeGtOne_of_cycleIndex curve index
  exact .finiteCut
    (CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath.ofFiniteConnectorAt
      configuration.branches higher
        (CCL.Riemann.BranchConfiguration.basisPairLeftIndex curve index)
        (CCL.Riemann.BranchConfiguration.basisPairRightIndex curve index) 0)

/-- The prepared A-cycle is the canonical owner-boundary lift of the same
finite basis cut at refinement zero. -/
theorem preparedACycle_realizesRaw_zero {genus : Nat}
    (curve : HyperellipticCurve genus) (index : Fin genus) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw
      (preparedACycle curve index)
      (((CCL.Riemann.BranchCutLifts.family curve).symplecticCycles.aCycle
        index).liftedPath 0) := by
  rw [CCL.Riemann.BranchCutLifts.canonicalACycle_liftedPath]
  unfold preparedACycle
  exact .finiteCut _ rfl rfl

/-- Fully prepared two-bank geometry for one standard B-cycle, joining the
finite representative of cut `i` to that of the final reference cut. -/
def preparedBCycle {genus : Nat} (curve : HyperellipticCurve genus)
    (index : Fin genus) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData curve := by
  let family := CCL.Riemann.BranchCutLifts.family curve
  let higher :=
    CCL.Riemann.BranchCutLifts.degreeGtOne_of_cycleIndex curve index
  let branches := family.cuts.configuration.branches
  let sourceCut := family.cuts.cutAt
    (CCL.Riemann.BranchCutLifts.basisCutIndex index)
  let targetCut := family.cuts.cutAt
    (CCL.Riemann.BranchCutLifts.referenceCutIndex genus)
  let source :=
    CCL.Riemann.BranchCutLifts.Geometry.finiteRepresentative sourceCut
  let target :=
    CCL.Riemann.BranchCutLifts.Geometry.finiteRepresentative targetCut
  exact .bridge
    (CCL.Riemann.PreparedCycleModels.PreparedDoublePath.ofFiniteConnectorAt
      branches higher source target 0)

/-- The prepared B-cycle is the canonical raw branch bridge at refinement
zero; preparation changes only its finite subdivision and square-root data. -/
theorem preparedBCycle_realizesRaw_zero {genus : Nat}
    (curve : HyperellipticCurve genus) (index : Fin genus) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw
      (preparedBCycle curve index)
      (((CCL.Riemann.BranchCutLifts.family curve).symplecticCycles.bCycle
        index).liftedPath 0) := by
  exact .bridge _

/-! Explicit-data variants used by finite worked examples and independently
audited branch certificates. -/

/-- Prepared A-cycle built from caller-supplied degree-complete branch data. -/
def preparedACycleOfData {genus : Nat}
    (curve : HyperellipticCurve genus)
    (branches : CCL.Riemann.BranchIsolation.Data curve)
    (index : Fin genus) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData curve := by
  let configuration :=
    CCL.Riemann.BranchConfiguration.configurationOfData curve branches
  let higher :=
    CCL.Riemann.BranchCutLifts.degreeGtOne_of_cycleIndex curve index
  exact .finiteCut
    (CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath.ofFiniteConnectorAt
      configuration.branches higher
        (CCL.Riemann.BranchConfiguration.basisPairLeftIndexOfData
          curve branches index)
        (CCL.Riemann.BranchConfiguration.basisPairRightIndexOfData
          curve branches index) 0)

/-- The explicit-data prepared A-cycle realizes the corresponding lifted
branch-cut cycle at refinement zero. -/
theorem preparedACycleOfData_realizesRaw_zero {genus : Nat}
    (curve : HyperellipticCurve genus)
    (branches : CCL.Riemann.BranchIsolation.Data curve)
    (index : Fin genus) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw
      (preparedACycleOfData curve branches index)
      (((CCL.Riemann.BranchCutLifts.familyOfData curve branches).symplecticCycles.aCycle
        index).liftedPath 0) := by
  rw [CCL.Riemann.BranchCutLifts.canonicalACycle_liftedPath_ofData]
  unfold preparedACycleOfData
  exact .finiteCut _ rfl rfl

/-- Prepared B-cycle built from the same explicit lifted branch family. -/
def preparedBCycleOfData {genus : Nat}
    (curve : HyperellipticCurve genus)
    (branches : CCL.Riemann.BranchIsolation.Data curve)
    (index : Fin genus) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData curve := by
  let family := CCL.Riemann.BranchCutLifts.familyOfData curve branches
  let higher :=
    CCL.Riemann.BranchCutLifts.degreeGtOne_of_cycleIndex curve index
  let familyBranches := family.cuts.configuration.branches
  let sourceCut := family.cuts.cutAt
    (CCL.Riemann.BranchCutLifts.basisCutIndex index)
  let targetCut := family.cuts.cutAt
    (CCL.Riemann.BranchCutLifts.referenceCutIndex genus)
  let source :=
    CCL.Riemann.BranchCutLifts.Geometry.finiteRepresentative sourceCut
  let target :=
    CCL.Riemann.BranchCutLifts.Geometry.finiteRepresentative targetCut
  exact .bridge
    (CCL.Riemann.PreparedCycleModels.PreparedDoublePath.ofFiniteConnectorAt
      familyBranches higher source target 0)

/-- The explicit-data prepared B-cycle realizes the corresponding raw bridge
at refinement zero. -/
theorem preparedBCycleOfData_realizesRaw_zero {genus : Nat}
    (curve : HyperellipticCurve genus)
    (branches : CCL.Riemann.BranchIsolation.Data curve)
    (index : Fin genus) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw
      (preparedBCycleOfData curve branches index)
      (((CCL.Riemann.BranchCutLifts.familyOfData curve branches).symplecticCycles.bCycle
        index).liftedPath 0) := by
  exact .bridge _

/-- Total switched schedules for a standard symplectic basis constructed from
explicit degree-complete branch data. -/
def ofData {genus : Nat} (curve : HyperellipticCurve genus)
    (branches : CCL.Riemann.BranchIsolation.Data curve) :
    StandardSwitchedSymplecticSchedule curve where
  aCycle := fun index =>
    { source := CCL.Riemann.PeriodMatrix.standardDifferential index
      prepared := preparedACycleOfData curve branches index }
  bCycle := fun index =>
    { source := CCL.Riemann.PeriodMatrix.standardDifferential index
      prepared := preparedBCycleOfData curve branches index }

/-- Total switched schedules for the complete automatically constructed
standard symplectic branch-cut basis. -/
def ofCurve {genus : Nat} (curve : HyperellipticCurve genus) :
    StandardSwitchedSymplecticSchedule curve :=
  let branches := CCL.Riemann.BranchIsolation.data curve
  ofData curve branches

/-- Assemble a genus-one switched schedule from two already prepared cycle
seeds.  Keeping this constructor generic in the seed values lets large
executable examples instantiate one compact cached schedule constant. -/
def ofGenusOnePrepared (curve : HyperellipticCurve 1)
    (aData bData :
      CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    StandardSwitchedSymplecticSchedule curve where
  aCycle := fun index =>
    { source := CCL.Riemann.PeriodMatrix.standardDifferential index
      prepared := aData }
  bCycle := fun index =>
    { source := CCL.Riemann.PeriodMatrix.standardDifferential index
      prepared := bData }

/-- Differential-independent persistent switched symplectic cycle family. -/
def cycles {genus : Nat}
    {curve : HyperellipticCurve genus}
    (schedule : StandardSwitchedSymplecticSchedule curve) :
    LiftedSymplecticCycles 2 genus where
  aCycle := fun index => (schedule.aCycle index).cycle
  bCycle := fun index => (schedule.bCycle index).cycle

/-- Assemble unconditional finite refinement programs for the complete
standard period data on the prepared switched cycles. -/
def periodData {genus : Nat}
    {curve : HyperellipticCurve genus}
    (schedule : StandardSwitchedSymplecticSchedule curve) :
    CCL.Riemann.PeriodMatrix.PeriodData curve where
  cycles := schedule.cycles
  aProgram := fun differential cycle =>
    (schedule.aCycle cycle).certifiedPeriodProgram differential
  bProgram := fun differential cycle =>
    (schedule.bCycle cycle).certifiedPeriodProgram differential

/-- Exact A-entry scale without unfolding the remaining period-data fields. -/
theorem periodData_aProgram_errorScale {genus : Nat}
    {curve : HyperellipticCurve genus}
    (schedule : StandardSwitchedSymplecticSchedule curve)
    (differential cycle : Fin genus) :
    ((schedule.periodData.aProgram differential cycle).integral.errorScale) =
      (schedule.aCycle cycle).toFiniteDifferential.initial.chain.switchFactor *
        (4 * (3 *
          (schedule.aCycle cycle).toFiniteDifferential.initial.scheduleBase
            (schedule.aCycle cycle).toFiniteDifferential.targets)) :=
  (schedule.aCycle cycle).certifiedPeriodProgram_errorScale differential

/-- Exact B-entry counterpart of `periodData_aProgram_errorScale`. -/
theorem periodData_bProgram_errorScale {genus : Nat}
    {curve : HyperellipticCurve genus}
    (schedule : StandardSwitchedSymplecticSchedule curve)
    (differential cycle : Fin genus) :
    ((schedule.periodData.bProgram differential cycle).integral.errorScale) =
      (schedule.bCycle cycle).toFiniteDifferential.initial.chain.switchFactor *
        (4 * (3 *
          (schedule.bCycle cycle).toFiniteDifferential.initial.scheduleBase
            (schedule.bCycle cycle).toFiniteDifferential.targets)) :=
  (schedule.bCycle cycle).certifiedPeriodProgram_errorScale differential

end StandardSwitchedSymplecticSchedule

/-! ## Unified finite cycle realization -/

/-- Finite evidence that a persistent period-cycle family represents a raw
symplectic basis.  The legacy constructor retains schedules whose prepared
geometry follows the raw family at every request.  The switched constructor
is tied to the total refiner above: each persistent cycle is generated from
one prepared seed, while the seed itself is checked against refinement zero
of the raw cut.  Every later state is therefore produced only by the certified
direct subdivision recursion with its stationary switches retained. -/
inductive FiniteSymplecticCycleRealization {genus : Nat}
    (curve : HyperellipticCurve genus) :
    LiftedSymplecticCycles 2 genus -> LiftedSymplecticCycles 2 genus -> Prop
  | legacy {computed raw : LiftedSymplecticCycles 2 genus}
      (realization :
        CCL.Riemann.PreparedCycleModels.SymplecticCycleRealization curve
          computed raw) :
      FiniteSymplecticCycleRealization curve computed raw
  | switched
      (schedule : StandardSwitchedSymplecticSchedule curve)
      {raw : LiftedSymplecticCycles 2 genus}
      (aSeed : forall index,
        CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw
          (schedule.aCycle index).prepared
          ((raw.aCycle index).liftedPath 0))
      (bSeed : forall index,
        CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw
          (schedule.bCycle index).prepared
          ((raw.bCycle index).liftedPath 0)) :
      FiniteSymplecticCycleRealization curve schedule.cycles raw

namespace FiniteSymplecticCycleRealization

/-- Two realized genus-one prepared seeds realize the switched schedule built
from them.  The proof is generic in the seed data, so concrete executable
banks never have to be unfolded while assembling their schedule witness. -/
theorem ofGenusOnePrepared
    {curve : HyperellipticCurve 1}
    {raw : LiftedSymplecticCycles 2 1}
    (aData bData :
      CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
    (aSeed :
      CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw aData
        ((raw.aCycle 0).liftedPath 0))
    (bSeed :
      CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw bData
        ((raw.bCycle 0).liftedPath 0)) :
    FiniteSymplecticCycleRealization curve
      (StandardSwitchedSymplecticSchedule.ofGenusOnePrepared
        curve aData bData).cycles raw := by
  apply FiniteSymplecticCycleRealization.switched
    (StandardSwitchedSymplecticSchedule.ofGenusOnePrepared curve aData bData)
  · intro index
    have indexZero : index = 0 := by
      apply Fin.ext
      omega0
    subst index
    exact aSeed
  · intro index
    have indexZero : index = 0 := by
      apply Fin.ext
      omega0
    subst index
    exact bSeed

/-- Period data produced by two realized genus-one prepared seeds carries the
same finite symplectic-cycle realization. -/
theorem periodDataOfGenusOnePrepared
    {curve : HyperellipticCurve 1}
    {raw : LiftedSymplecticCycles 2 1}
    (aData bData :
      CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
    (aSeed :
      CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw aData
        ((raw.aCycle 0).liftedPath 0))
    (bSeed :
      CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw bData
        ((raw.bCycle 0).liftedPath 0)) :
    FiniteSymplecticCycleRealization curve
      (StandardSwitchedSymplecticSchedule.ofGenusOnePrepared
        curve aData bData).periodData.cycles raw :=
  ofGenusOnePrepared aData bData aSeed bSeed

/-- Literal equality is the degenerate finite realization. -/
theorem ofEq {genus : Nat} {curve : HyperellipticCurve genus}
    {left right : LiftedSymplecticCycles 2 genus}
    (equal : left = right) :
    FiniteSymplecticCycleRealization curve left right :=
  .legacy
    (CCL.Riemann.PreparedCycleModels.SymplecticCycleRealization.ofEq equal)

/-- The total switched schedule constructed from explicit branch data realizes
the symplectic basis constructed from those same tracks. -/
theorem ofData {genus : Nat} (curve : HyperellipticCurve genus)
    (branches : CCL.Riemann.BranchIsolation.Data curve) :
    FiniteSymplecticCycleRealization curve
      (StandardSwitchedSymplecticSchedule.ofData curve branches).cycles
      (CCL.Riemann.BranchCutLifts.symplecticBasisOfData
        curve branches).cycles := by
  exact FiniteSymplecticCycleRealization.switched
    (StandardSwitchedSymplecticSchedule.ofData curve branches)
    (fun index =>
      StandardSwitchedSymplecticSchedule.preparedACycleOfData_realizesRaw_zero
        curve branches index)
    (fun index =>
      StandardSwitchedSymplecticSchedule.preparedBCycleOfData_realizesRaw_zero
        curve branches index)

/-- The total standard switched schedule realizes the automatically
constructed branch-cut basis without any caller-supplied topology witness. -/
theorem standard {genus : Nat} (curve : HyperellipticCurve genus) :
    FiniteSymplecticCycleRealization curve
      (StandardSwitchedSymplecticSchedule.ofCurve curve).cycles
      (CCL.Riemann.BranchCutLifts.symplecticBasis curve).cycles := by
  change FiniteSymplecticCycleRealization curve
    (StandardSwitchedSymplecticSchedule.ofData curve
      (CCL.Riemann.BranchIsolation.data curve)).cycles
    (CCL.Riemann.BranchCutLifts.symplecticBasisOfData curve
      (CCL.Riemann.BranchIsolation.data curve)).cycles
  exact FiniteSymplecticCycleRealization.ofData curve
    (CCL.Riemann.BranchIsolation.data curve)

end FiniteSymplecticCycleRealization

/-- Executable standard period programs built from explicit degree-complete
branch tracks. -/
def standardPeriodDataOfData {genus : Nat}
    (curve : HyperellipticCurve genus)
    (branches : CCL.Riemann.BranchIsolation.Data curve) :
    CCL.Riemann.PeriodMatrix.PeriodData curve :=
  (StandardSwitchedSymplecticSchedule.ofData curve branches).periodData

/-- Explicit-data period programs realize the symplectic basis built from the
same branch tracks. -/
theorem standardPeriodDataOfData_realization {genus : Nat}
    (curve : HyperellipticCurve genus)
    (branches : CCL.Riemann.BranchIsolation.Data curve) :
    FiniteSymplecticCycleRealization curve
      (standardPeriodDataOfData curve branches).cycles
      (CCL.Riemann.BranchCutLifts.symplecticBasisOfData curve branches).cycles :=
  FiniteSymplecticCycleRealization.ofData curve branches

/-- Unconditional executable period programs for every standard
differential and every standard A/B branch-cut cycle. -/
def automaticStandardPeriodData {genus : Nat}
    (curve : HyperellipticCurve genus) :
    CCL.Riemann.PeriodMatrix.PeriodData curve :=
  (StandardSwitchedSymplecticSchedule.ofCurve curve).periodData

/-- Automatic standard A-period models are nonempty at every finite request. -/
theorem automaticStandardPeriodData_aProgram_model_cells_positive {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential cycle : Fin genus) (index : Nat) :
    0 < ((((automaticStandardPeriodData curve).aProgram differential cycle).integral.model
      index).cells.length) :=
  ((StandardSwitchedSymplecticSchedule.ofCurve curve).aCycle cycle).certifiedPeriodProgram_model_cells_positive
    differential index

/-- Automatic standard B-period models are nonempty at every finite request. -/
theorem automaticStandardPeriodData_bProgram_model_cells_positive {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential cycle : Fin genus) (index : Nat) :
    0 < ((((automaticStandardPeriodData curve).bProgram differential cycle).integral.model
      index).cells.length) :=
  ((StandardSwitchedSymplecticSchedule.ofCurve curve).bCycle cycle).certifiedPeriodProgram_model_cells_positive
    differential index

/-- The unconditional period programs follow the canonical symplectic
branch-cut basis through the certified switched subdivision recursion. -/
theorem automaticStandardPeriodData_realization {genus : Nat}
    (curve : HyperellipticCurve genus) :
    FiniteSymplecticCycleRealization curve
      (automaticStandardPeriodData curve).cycles
      (CCL.Riemann.BranchCutLifts.symplecticBasis curve).cycles :=
  FiniteSymplecticCycleRealization.standard curve

/-- A closed common direct schedule specialized to the complete standard
differential basis.  The source differential may be any convenient member;
all target models are recentered constructively. -/
structure StandardDirectClosedSchedule {genus : Nat}
    (curve : HyperellipticCurve genus) where
  source : Differential genus
  initial :
    CCL.Riemann.PreparedDirectDyadicRefinements.DirectRefinementState curve
      source
  closed : initial.finish = initial.start

namespace StandardDirectClosedSchedule

def toFiniteDifferential {genus : Nat}
    {curve : HyperellipticCurve genus}
    (schedule : StandardDirectClosedSchedule curve) :
    FiniteDifferentialDirectClosedSchedule curve schedule.source where
  initial := schedule.initial
  targets := standardDifferentials genus
  closed := schedule.closed

def cycle {genus : Nat}
    {curve : HyperellipticCurve genus}
    (schedule : StandardDirectClosedSchedule curve) :
    LiftedCycleRefinement 2 := schedule.toFiniteDifferential.cycle

def certifiedPeriodProgram {genus : Nat}
    {curve : HyperellipticCurve genus}
    (schedule : StandardDirectClosedSchedule curve)
    (differential : Fin genus) :
    CertifiedPeriodProgram curve
      (CCL.Riemann.PeriodMatrix.standardDifferential differential)
      schedule.cycle :=
  schedule.toFiniteDifferential.certifiedPeriodProgram
    (CCL.Riemann.PeriodMatrix.standardDifferential differential)
    (standardDifferential_mem_standardDifferentials differential)

end StandardDirectClosedSchedule

/-- Common-geometry direct schedules for every A- and B-cycle. -/
structure StandardDirectSymplecticSchedule {genus : Nat}
    (curve : HyperellipticCurve genus) where
  aCycle : Fin genus -> StandardDirectClosedSchedule curve
  bCycle : Fin genus -> StandardDirectClosedSchedule curve

namespace StandardDirectSymplecticSchedule

def cycles {genus : Nat}
    {curve : HyperellipticCurve genus}
    (schedule : StandardDirectSymplecticSchedule curve) :
    LiftedSymplecticCycles 2 genus where
  aCycle := fun index => (schedule.aCycle index).cycle
  bCycle := fun index => (schedule.bCycle index).cycle

/-- Assemble all standard differential programs over one exact persistent
symplectic cycle family. -/
def periodData {genus : Nat}
    {curve : HyperellipticCurve genus}
    (schedule : StandardDirectSymplecticSchedule curve) :
    CCL.Riemann.PeriodMatrix.PeriodData curve where
  cycles := schedule.cycles
  aProgram := fun differential cycle =>
    (schedule.aCycle cycle).certifiedPeriodProgram differential
  bProgram := fun differential cycle =>
    (schedule.bCycle cycle).certifiedPeriodProgram differential

end StandardDirectSymplecticSchedule

end CCL.Riemann.PreparedRefinementPrograms
