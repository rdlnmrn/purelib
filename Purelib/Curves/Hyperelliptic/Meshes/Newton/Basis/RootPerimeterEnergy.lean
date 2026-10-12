module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootBoundaryEnergy
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.EndpointReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedEndpoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRootEnergy
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunDepthSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.Trace.Family
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure

open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback.SynchronizedSurfaceRequests

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Use the original Newton endpoint cache in the acquired root perimeter bound. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.RootPerimeterEnergy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfacePreparation AllSurfacePreparation)
open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns
  (Traces Perimeters PhysicalSamples pieceCounts)
open
  PuncturedGrid.Exterior.Basis.RunFaceSynchronization.CommonBasisPreparation.ParentRunSchedules
  (SharedOwnerBanks FaceStage)
open
  PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary.RequestedSurfaceRuns.PhysicalSamples
  (endpointSides originalSides)
open
  PuncturedGrid.Exterior.Basis.RequestedEndpoints.RequestedSurfaceRuns.PhysicalSamples
  (endpointSides_eq_cached)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootBoundaryEnergy.CommonBasisRequest.Sampled
  (rootJoiningArea rootJoiningCost)

open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback.SynchronizedSurfaceRequests.PerimeterSamples
  (cachedSideEndpoint)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.EndpointReadback.SynchronizedSurfaceRequests.PerimeterSamples
  (commonBasis_endpoint_eq_cached)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {gridTarget radius :
    Normalization.InverseRootPolynomial.Coordinate}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation gridTarget radius}
  {lifted : Meshes.LiftedPuncturedGrid grid.punctured} {differential : Hyperelliptic.Differentials.Basic.Differential
    genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor index minimum stage
    energyFloor radialDepth : Nat}
  {box : Rational.Box} {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

namespace CommonBasisRequest

variable {request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisRequest retained basis
  target coefficientTarget coverFloor floor}
  {plans : request.Plans capSample polynomials minimum} {inputs : retained.Inputs index}
  {readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings retained.anchors retained.sources
    request.schedule.bank plans inputs stage}

variable {fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.FanPreparation request
  plans inputs readings energyFloor}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Sampled

open Purelib.Data.Rat.Fraction.Compatibility

variable (sample : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled fans
  coefficients radialDepth) (comparisons :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample)
  {whole :
    PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential}
  {previous : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
  {selected : PuncturedGrid.Exterior.SourceCuts whole previous}
  {coarseDepth : Nat}
  {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet}
  {meshTarget : Normalization.InverseRootPolynomial.Coordinate}
  {meshRequest : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
    (fun sheet => Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet
      coarseDepth) fixed meshTarget}
  {requested : Normalization.InverseRootPolynomial.Coordinate} {runMinimum : Nat}
  {initialSchedules :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.Schedules
    selected meshRequest retained inputs requested runMinimum}
  (spatial :
    PuncturedGrid.Exterior.Basis.SpatialAcquisition
    initialSchedules)
  {faceIndex : Nat}
  {traces : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.Traces
    (prepared := prepared) selected spatial.refined}
  {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains faceIndex}
  {vertices : (outer : Fin prepared.occurrences.length) →
    Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.capacities selected
      spatial.refined outer) → Nat}
  {owners :
    PuncturedGrid.Exterior.Basis.RunFaceSynchronization.CommonBasisPreparation.ParentRunSchedules.SharedOwnerBanks
    spatial.requests
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.pieceCounts
      selected spatial.refined) vertices}
  {perimeters :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.Perimeters
    selected spatial.refined traces cache}
  (physical :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.PhysicalSamples
    selected spatial.refined traces cache
    coefficients spatial.requests owners perimeters)
  (face :
    PuncturedGrid.Exterior.Basis.RunFaceSynchronization.CommonBasisPreparation.ParentRunSchedules.FaceStage
    owners spatial.refined.index)
  (facePaid : face.stage ≤ faceIndex)
  (sourcePaid : ∀ outer, (initialSchedules.get outer).sourceIndex ≤ index)
  (coverPaid : spatial.depths.depth ≤ coverFloor)

/-- The acquired physical endpoint subtraction is the literal Newton cache
on the same face, sheet, coefficient vector, and numerical stage. -/
theorem requested_newton_endpoints :
  PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary.RequestedSurfaceRuns.PhysicalSamples.endpointSides
  physical =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn fun outer =>
      let occurrence := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
        prepared.occurrences outer
      let endpoint :=
        PerimeterSamples.cachedSideEndpoint
        cache coefficients occurrence.sideOccurrence.position
        occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side
      if occurrence.sourceForward then endpoint else -endpoint) := by
  rw
    [PuncturedGrid.Exterior.Basis.RequestedEndpoints.RequestedSurfaceRuns.PhysicalSamples.endpointSides_eq_cached]
  apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
  apply Data.List.OfFn.Basic.ofFn_congr
  intro outer
  exact congrArg (fun endpoint => if (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).sourceForward then endpoint else -endpoint)

      (EndpointReadback.SynchronizedSurfaceRequests.PerimeterSamples.commonBasis_endpoint_eq_cached
      (cache := cache) (coefficients := coefficients)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).sideOccurrence.position
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).sideOccurrence.sheet
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).sideOccurrence.side)

include comparisons facePaid sourcePaid coverPaid

/-- The root-corrected bound now uses Newton's original cached endpoint chords,
without changing its retained root polygon or paying another approximation. -/
theorem requested_newton_cached_root_upper (positive : 0 < requested)
    {physicalAllowance rootAllowance : Normalization.InverseRootPolynomial.Coordinate}
    (physicalNN : 0 ≤ physicalAllowance) (rootNN : 0 ≤ rootAllowance)
    (physicalPaid : requested ≤ 16 * physicalAllowance ^ 2)
    (rootPaid :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootBoundaryEnergy.CommonBasisRequest.Sampled.rootJoiningCost
      (request := request) (inputs := inputs) requested ≤ 16 * rootAllowance ^ 2)
    (trace :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedTrace
      sample comparisons) (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (later : request.readingStage plans ≤ stage) :

      (PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary.RequestedSurfaceRuns.PhysicalSamples.originalSides
      physical - Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn fun outer =>
      let occurrence := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
        prepared.occurrences outer
      let endpoint :=
        PerimeterSamples.cachedSideEndpoint
        cache coefficients occurrence.sideOccurrence.position
        occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side
      if occurrence.sourceForward then endpoint else -endpoint) +
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootBoundaryEnergy.CommonBasisRequest.Sampled.rootJoiningArea
        sample).im / 4 ≤
      (5 * target + physicalAllowance + rootAllowance) * Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients := by
  have upper :=
    PuncturedGrid.Exterior.Basis.RequestedRootEnergy.CommonBasisRequest.Sampled.requested_root_perimeter_upper
    sample comparisons spatial physical face facePaid sourcePaid coverPaid
    positive physicalNN rootNN physicalPaid rootPaid trace branch later
  rw [Hyperelliptic.Meshes.Newton.Basis.RootPerimeterEnergy.CommonBasisRequest.Sampled.requested_newton_endpoints
    spatial physical] at upper
  exact upper

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.RootPerimeterEnergy
