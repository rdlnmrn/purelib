module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.LinearAlgebra.Gaussian.Energy

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousBoundaryComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousCutRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.NewtonCombinedPeriodArea
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Riemann.RootContinuation.NewtonHomogeneousAnnularRequest
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.CoercivitySchedule
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SourceSurfaceAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BoundaryBudget
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CenteredBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Topology.Surface.Sewing.SewnEnergyCombination
public import Purelib.Topology.Surface.Sewing.SewnSelectedEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.CoercivityBounds
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.RawComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorEnergy
public import Purelib.Riemann.RootContinuation.NewtonRawOddEnergyBudget
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SurfaceAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SpatialAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SynchronizedSourceInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetRefinement
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.CoercivityBounds.CommonBasisPreparation
open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

public section

/-! Combine the independent sewn lower bound with every odd exterior loss on the same corrected periods. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.RawLower

open Purelib

open Purelib.Riemann.Normalization

open Purelib.Riemann.RootContinuation.NewtonHomogeneousAnnularRequest

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {oldLifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank oldLifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  {periodPrepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {gridTarget radius : Normalization.InverseRootPolynomial.Coordinate}
  (allocated : Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests.FamilyFineAreaRequest preparation gridTarget
    radius)
  {lifted : Meshes.LiftedPuncturedGrid allocated.family.single.grid.punctured} {firstIndex : Fin genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    allocated.family.single.grid.faces.regulars}
  {component :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
    regular domains (Periods.PeriodMatrix.standardDifferential firstIndex)}

namespace CommonBasisPreparation.RequestedSurfaceRuns.SourceSurfaceAcquisition

variable {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation component.prepared}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {energyTarget coefficientTarget requested : Normalization.InverseRootPolynomial.Coordinate} {traceFloor floor
    seedIndex minimum : Nat}
  {seedInputs : retained.Inputs seedIndex}
  {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations base.bank.toBranchCellBank}
  {partitions : Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations allocated.family.single.grid}
  {preparations : Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular domains}
  (shared : Branches.NewtonSharedExteriorCuts.SharedExteriorCuts partitions preparations)
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet}
  {meshTarget : Normalization.InverseRootPolynomial.Coordinate}
  {meshRequest : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
    (fun sheet => Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains
      (shared.source.select firstIndex).cuts sheet coarseDepth) fixed meshTarget}
  {seedSchedules : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.Schedules
    (shared.source.select firstIndex) meshRequest retained seedInputs requested minimum}
  {pieceDepth : Nat} {surfaceFixed : (sheet : Fin 2) → RootContinuation.NewtonRequestedObservationEnergy.Preflights
    domains sheet}
  {error : Normalization.InverseRootPolynomial.Coordinate}
  {initialSurface : Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests
    (fun sheet => Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface
      sheet pieceDepth) surfaceFixed error}
  (acquired : SourceSurfaceAcquisition
    seedSchedules initialSurface basis energyTarget coefficientTarget traceFloor floor)

  (vertices : (outer : Fin component.prepared.occurrences.length) →
    Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.capacities
      (shared.source.select firstIndex) acquired.geometry.spatial.refined outer) → Nat)
  (energyFloor faceFloor : Nat)

  (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision allocated.family.single.grid lifted)

  (compatible : Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility.Compatible partitions) (allowance :
    Normalization.InverseRootPolynomial.Coordinate)

namespace CoercivitySchedule
variable {allocated shared acquired vertices energyFloor faceFloor excision compatible allowance}
  (schedule : CoercivitySchedule shared
    acquired vertices energyFloor faceFloor excision compatible allowance)
  {stage : Nat} (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
  (member : ∀ outer, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    component.prepared.occurrences outer ∈ (preparations.get firstIndex).occurrences)
  (later : schedule.index ≤ stage)
  (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank allocated.family.single.grid.faces)
  (positive : 0 < allowance)
  (triangles : Data.Vector.DependentVector (fun row : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get row) lifted.mesh))

include schedule member later neighbors positive
open Purelib.Data.Rat.Fraction.Compatibility

variable
  (surfaces : Topology.Surface.Sewing.SewnEnergyCombination.EnergySurfaces lifted.cutPolygon.patch (fun row =>
    (triangles.get row).values))
  (pairs : Topology.Surface.Sewing.SewnEnergyCombination.EnergyPairs surfaces)
  (selected : Topology.Surface.Sewing.SewnSelectedEnergy.SelectedEnergySamples surfaces pairs
    (fun source => !(excision.entries.any (fun entry => Topology.NewtonSewnExcision.AllHoleExcision.sourceMask entry
      source))))
  {magnitudes : Data.Vector.DependentVector (fun row : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential row))}
  {newSheet : Fin 2} {periodFloor : Nat}
  {periodRequest : Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request periodPrepared newSheet excision
    magnitudes
    (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance / 4)
      periodFloor}

include selected

/-- The source comparison and odd restoration leave only the displayed, explicitly paid scalar losses. -/
theorem raw_lower
    (samples : Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request.Samples triangles surfaces pairs
      periodRequest)
    {cutFloor : Nat} (cut : Hyperelliptic.Meshes.Newton.HomogeneousCutRequest.Request.CutRequest periodRequest
      (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance / 4)
        cutFloor)
    (cutLater : cut.index ≤ stage)
    {sewingPrepared : Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation lifted.cutPolygon domains}
      {sewingFloor : Nat}
    (sewing : Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation.Request sewingPrepared
      (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance)
        sewingFloor)
    (sewingLater : sewing.index ≤ stage)
    {joiningFloor : Nat} (joining :
      OddCanonicalExteriorRequest
      magnitudes allowance joiningFloor)
    (joiningLater : joining.index ≤ stage)
    {annularPrepared :
      Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations excision}
      {annularFloor : Nat}
    (annularRequest : RootContinuation.NewtonHomogeneousAnnularRequest.HomogeneousAnnularRequest.Request (domains :=
      domains) annularPrepared annularFloor)
    (annularSamples : RootContinuation.NewtonHomogeneousAnnularRequest.HomogeneousAnnularRequest.Samples triangles
      surfaces pairs annularRequest)
    (annularLater : annularRequest.index ≤ stage)
    (holes : Hyperelliptic.Meshes.Newton.HomogeneousBoundaryComparison.Request.HoleSamples triangles excision)
    (canonical : component =
      PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent.build
      regular domains
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted
        (Periods.PeriodMatrix.standardDifferential firstIndex) 0))
    (requestedPositive : 0 < requested) (paid : requested ≤ 16 * allowance ^ 2)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (degree : curve.polynomial.natDegree = 2 * genus + 1)
    (targetLe : gridTarget ≤
      Complement.BoundaryBudget.ProtectedObservations.SynchronizedSurfaceRequests.remainingBoundaryTarget
      genus (Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation) allowance)
    (annularPaid : (82 / 4 : Normalization.InverseRootPolynomial.Coordinate) * gridTarget ≤
      Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance) :
    let values := fun row => Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      (triangles.get row).values
    let aMatrix := Periods.NewtonCombinedPeriodArea.resplitPeriodMatrix periodPrepared
      allocated.family.single.grid.shrunk.included lifted.edges lifted.vertices newSheet values false
    let bMatrix := Periods.NewtonCombinedPeriodArea.resplitPeriodMatrix periodPrepared
      allocated.family.single.grid.shrunk.included lifted.edges lifted.vertices newSheet values true
    (2 * (Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations - error - allowance - allowance -
      allowance) - allowance - allowance -
      (5 * energyTarget + allowance + allowance + allowance) - (allowance + allowance)) *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      LinearAlgebra.Gaussian.Energy.unnormalizedEnergyForm coefficients aMatrix bMatrix := by
  intro values aMatrix bMatrix
  let remaining :=
    Complement.CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
    excision

      (CoercivityBounds.CommonBasisPreparation.RequestedSurfaceRuns.SourceSurfaceAcquisition.CoercivitySchedule.evaluate
      schedule cache coefficients member later).observed neighbors
  have lower :=
    CoercivityBounds.CommonBasisPreparation.RequestedSurfaceRuns.SourceSurfaceAcquisition.CoercivitySchedule.sewn_lower
    schedule cache coefficients member later neighbors positive triangles sewing sewingLater surfaces pairs selected
  have upper :=

      RequestedSurfaceRuns.SourceSurfaceAcquisition.CoercivitySchedule.remaining_upper
    schedule cache coefficients member later neighbors positive triangles canonical requestedPositive paid branch
    targetLe
  have exterior := Hyperelliptic.Meshes.Newton.OddCanonicalExteriorEnergy.Samples.remaining_odd_exterior_energy_upper
    samples joining joiningLater degree coefficients remaining upper
  have reduced := Fraction.Order.Arithmetic.sub_le_sub_direct lower exterior
  have cancel : (selected.energy coefficients + remaining).im / 4 -
      (remaining + 2 * samples.exterior coefficients).im / 4 =
      (selected.energy coefficients - 2 * samples.exterior coefficients).im / 4 := by
    simp only [Gaussian.Basic.add_im, Gaussian.Basic.sub_im, Fraction.Field.div_eq_mul_inv_direct, -eq_self, -iff_self]
    ring1
  change _ ≤ (selected.energy coefficients + remaining).im / 4 - (remaining + 2 * samples.exterior coefficients).im / 4
    at reduced
  rw [cancel] at reduced
  have period := Hyperelliptic.Meshes.Newton.Complement.RawComparison.Request.Samples.remaining_raw_lower
    samples cut cutLater positive annularRequest annularSamples annularLater selected holes
    coefficients positive annularPaid
  have combined := (Fraction.Order.Arithmetic.sub_le_sub_direct reduced (le_refl (a := (allowance + allowance) *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))).trans period
  exact (le_of_eq (by ring1)).trans combined

/-- The computed odd allocation preserves the strictly positive observation lower constant. -/
theorem raw_positive_lower
    (samples : Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request.Samples triangles surfaces pairs
      periodRequest)
    {cutFloor : Nat} (cut : Hyperelliptic.Meshes.Newton.HomogeneousCutRequest.Request.CutRequest periodRequest
      (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance / 4)
        cutFloor)
    (cutLater : cut.index ≤ stage)
    {sewingPrepared : Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation lifted.cutPolygon domains}
      {sewingFloor : Nat}
    (sewing : Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation.Request sewingPrepared
      (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance)
        sewingFloor)
    (sewingLater : sewing.index ≤ stage)
    {joiningFloor : Nat} (joining :
      OddCanonicalExteriorRequest
      magnitudes allowance joiningFloor)
    (joiningLater : joining.index ≤ stage)
    {annularPrepared :
      Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations excision}
      {annularFloor : Nat}
    (annularRequest : RootContinuation.NewtonHomogeneousAnnularRequest.HomogeneousAnnularRequest.Request (domains :=
      domains) annularPrepared annularFloor)
    (annularSamples : RootContinuation.NewtonHomogeneousAnnularRequest.HomogeneousAnnularRequest.Samples triangles
      surfaces pairs annularRequest)
    (annularLater : annularRequest.index ≤ stage)
    (holes : Hyperelliptic.Meshes.Newton.HomogeneousBoundaryComparison.Request.HoleSamples triangles excision)
    (canonical : component =
      PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent.build
      regular domains
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted
        (Periods.PeriodMatrix.standardDifferential firstIndex) 0))
    (requestedPositive : 0 < requested) (paid : requested ≤ 16 * allowance ^ 2)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (degree : curve.polynomial.natDegree = 2 * genus + 1)
    (targetLe : gridTarget ≤
      Complement.BoundaryBudget.ProtectedObservations.SynchronizedSurfaceRequests.remainingBoundaryTarget
      genus (Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation) allowance)
    (annularPaid : (82 / 4 : Normalization.InverseRootPolynomial.Coordinate) * gridTarget ≤
      Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance)
    (error_eq : error = RootContinuation.NewtonRawEnergyBudget.rawEnergyAllowance observations)
    (allowance_eq : allowance = RootContinuation.NewtonRawEnergyBudget.rawEnergyAllowance observations)
    (source_eq : energyTarget = RootContinuation.NewtonRawOddEnergyBudget.rawOddSourceTarget observations) :
    let values := fun row => Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      (triangles.get row).values
    let aMatrix := Periods.NewtonCombinedPeriodArea.resplitPeriodMatrix periodPrepared
      allocated.family.single.grid.shrunk.included lifted.edges lifted.vertices newSheet values false
    let bMatrix := Periods.NewtonCombinedPeriodArea.resplitPeriodMatrix periodPrepared
      allocated.family.single.grid.shrunk.included lifted.edges lifted.vertices newSheet values true
    Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      LinearAlgebra.Gaussian.Energy.unnormalizedEnergyForm coefficients aMatrix bMatrix := by
  have lower :=
    raw_lower
    schedule cache coefficients member later neighbors positive triangles surfaces pairs selected
    samples cut cutLater sewing sewingLater joining joiningLater annularRequest annularSamples annularLater holes
      canonical
    requestedPositive paid branch degree targetLe annularPaid
  have scalar : 2 * (Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations - error - allowance -
    allowance - allowance) - allowance - allowance -
      (5 * energyTarget + allowance + allowance + allowance) - (allowance + allowance) =
        Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations := by
    rw [error_eq, allowance_eq, source_eq]
    exact RootContinuation.NewtonRawOddEnergyBudget.rawOddEnergy_paid observations
  exact (congrArg (fun value : Normalization.InverseRootPolynomial.Coordinate => value *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) scalar).symm.trans_le lower

end CoercivitySchedule
end CommonBasisPreparation.RequestedSurfaceRuns.SourceSurfaceAcquisition
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.RawLower
