module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunFaceSynchronization
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SpatialAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPerimeterEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.AcquiredCanonicalJoining
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunDepthSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.Trace.Family
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary.RequestedSurfaceRuns

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Bound the actual acquired Newton component with its canonical exterior polygon. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.AcquiredCanonicalEnergy

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable {bounds : Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {retained : Preparation.CommonBasisPreparation prepared}
  {basis : Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : InverseRootPolynomial.Coordinate} {coverFloor floor index minimum stage
    energyFloor radialDepth : Nat}
  {box : Rational.Box} {capSample : Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box}

namespace CommonBasisRequest

variable {request : Preparation.CommonBasisRequest retained basis
  target coefficientTarget coverFloor floor}
  {plans : request.Plans capSample polynomials minimum} {inputs : retained.Inputs index}
  {readings : Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings retained.anchors retained.sources
    request.schedule.bank plans inputs stage}

variable {fans : Connection.CommonBasisRequest.FanPreparation request
  plans inputs readings energyFloor}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Sampled

open Purelib.Data.Rat.Fraction.Compatibility

variable (sample : Connection.CommonBasisRequest.Sampled fans
  coefficients radialDepth) (comparisons :
  CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample)
  {whole :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential}
  {previous : RegularDomainMeshes.RegularMeshes.CommonCuts domains}
  {selected : SourceCuts whole previous}
  {coarseDepth : Nat}
  {fixed : (sheet : Fin 2) → RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet}
  {meshTarget : InverseRootPolynomial.Coordinate}
  {meshRequest : TwoSheetBilinearRequest.TwoSheetRequest
    (fun sheet => RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet
      coarseDepth) fixed meshTarget}
  {requested : InverseRootPolynomial.Coordinate} {runMinimum : Nat}
  {initialSchedules :
    SurfaceRunSchedules.RequestedSurfaceRuns.Schedules
    selected meshRequest retained inputs requested runMinimum}
  (spatial :
    SpatialAcquisition
    initialSchedules)
  {faceIndex : Nat}
  {traces : RequestedPhysicalComponent.RequestedSurfaceRuns.Traces
    (prepared := prepared) selected spatial.refined}
  {cache : RegularDomainMeshes.RegularMeshes.Numerics domains faceIndex}
  {vertices : (outer : Fin prepared.occurrences.length) →
    Fin (SurfaceRunSchedules.RequestedSurfaceRuns.capacities selected
      spatial.refined outer) → Nat}
  {owners :
    RunFaceSynchronization.CommonBasisPreparation.ParentRunSchedules.SharedOwnerBanks
    spatial.requests
    (RequestedPhysicalComponent.RequestedSurfaceRuns.pieceCounts
      selected spatial.refined) vertices}
  {perimeters :
    RequestedPhysicalComponent.RequestedSurfaceRuns.Perimeters
    selected spatial.refined traces cache}
  (face :
    RunFaceSynchronization.CommonBasisPreparation.ParentRunSchedules.FaceStage
    owners spatial.refined.index)
  (facePaid : face.stage ≤ faceIndex)
  (sourcePaid : ∀ outer, (initialSchedules.get outer).sourceIndex ≤ index)
  (coverPaid : spatial.depths.depth ≤ coverFloor)

variable (member : ∀ outer, ParentIndices.occurrenceAt
  prepared.occurrences outer ∈ whole.occurrences)
  (triangles : (row : Fin genus) → TrianglePrimitiveReadings.TriangleReadings
    (cache.get row) lifted.mesh)
  (positive : 0 < requested) {allowance : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ allowance)
  (paid : requested ≤ 16 * allowance ^ 2) (trace :
    CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedTrace sample
    comparisons)
  (branch : Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) (later : request.readingStage
    plans ≤ stage)

include facePaid sourcePaid coverPaid positive nonnegative paid trace branch later

/-- The acquired odd component bounds the canonical Newton polygon with its actual side correction. -/
theorem acquired_canonical_energy_upper :
    let physical :=
      RequestedPhysicalComponent.RequestedSurfaceRuns.acquirePhysicalSamples
      selected spatial.refined traces cache
      coefficients spatial.requests owners perimeters member face facePaid

    (PhysicalSamples.originalSides
      physical -
      PhysicalSamples.endpointSides
      physical + Path.PairedIncrementArea.area (program.indexed.map (fun edge =>
        Path.ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
          CanonicalEdgeValues.edgeValuation lifted.mesh (triangles row).values
            edge)))).im / 4 ≤
      (5 * target + allowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  let physical :=
    RequestedPhysicalComponent.RequestedSurfaceRuns.acquirePhysicalSamples
    selected spatial.refined traces cache
      coefficients spatial.requests owners perimeters member face facePaid
  have bound :=
    RequestedPerimeterEnergy.CommonBasisRequest.Sampled.requested_perimeter_energy_upper
    sample comparisons spatial physical face facePaid sourcePaid coverPaid
    positive nonnegative paid trace branch later faceIndex
  have joining :=
    AcquiredCanonicalJoining.RequestedSurfaceRuns.acquired_canonical_joiningArea
    selected spatial.refined traces cache coefficients spatial.requests owners perimeters member face facePaid triangles
  change
    PhysicalSamples.joiningArea
    physical = _ at joining
  rw [joining] at bound
  exact bound

/-- Read the side correction through the retained Newton assembly before the global surface sum. -/
theorem acquired_newton_canonical_energy_upper
    (assemblies :
      PhysicalSamples.Assemblies
      (selected := selected) (request := spatial.refined) (cache := cache) (coefficients := coefficients))
    (perimeter :
      PhysicalSamples.AssemblyPerimeters
      assemblies) :
    let physical :=
      RequestedPhysicalComponent.RequestedSurfaceRuns.acquirePhysicalSamples
      selected spatial.refined traces cache
      coefficients spatial.requests owners perimeters member face facePaid
    (Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn fun outer =>
      let side := PerimeterReadback.SharedPerimeter.sideArea cache
        coefficients (perimeter outer)
        (ParentIndices.occurrenceAt prepared.occurrences
          outer).sideOccurrence.side
      if (ParentIndices.occurrenceAt prepared.occurrences
        outer).sourceForward then side else -side) -

          PhysicalSamples.endpointSides
          physical + Path.PairedIncrementArea.area (program.indexed.map (fun edge =>
        Path.ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
          CanonicalEdgeValues.edgeValuation lifted.mesh (triangles row).values
            edge)))).im / 4 ≤
      (5 * target + allowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  let physical :=
    RequestedPhysicalComponent.RequestedSurfaceRuns.acquirePhysicalSamples
    selected spatial.refined traces cache
      coefficients spatial.requests owners perimeters member face facePaid
  have bound :=
    acquired_canonical_energy_upper
    sample (traces := traces) (perimeters := perimeters) comparisons spatial face facePaid sourcePaid coverPaid member
    triangles
    positive nonnegative paid trace branch later
  change
    (PhysicalSamples.originalSides
    physical -
    PhysicalSamples.endpointSides
    physical + _).im / 4 ≤ _ at bound
  rw
    [PhysicalSamples.originalSides_eq
    physical assemblies perimeter] at bound
  exact bound

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.AcquiredCanonicalEnergy
