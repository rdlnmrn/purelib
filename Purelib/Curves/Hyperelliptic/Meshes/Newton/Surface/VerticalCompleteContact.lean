module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointGeometry
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointOrigins
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LiftedEntries
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonGlobalContactEnergy
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryContactAccuracy
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.VerticalBoundaryRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LiftedEndpointRequests
public import Purelib.Integration.Budget.Surface.Contact
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.PairedEndpointPolygon
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularPairedEndpointReadings
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Topology.Mesh.IndexedQuadrilaterals
meta import Mathlib.Tactic.Linter.Lint

public section

/-! A complete neighboring-face contact is built from the actual lifted
corner owner, retained perimeter traces and the global error allowance. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.VerticalCompleteContact

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointOrigins
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.VerticalBoundaryRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonPreparation
open Purelib.Data.Rat
open Purelib.Integration.Budget.Surface
open Purelib.LinearAlgebra.Gaussian.Energy
open Purelib.Riemann.Readings
open Purelib.Riemann.RootContinuation.NewtonGlobalContactEnergy
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Topology.NewtonObservationSurfacePartition (SurfacePartition)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces (HorizontalPieces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointGeometry
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (PiecePerimeterTraces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceRequests (horizontalPieceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonEnergy.EndpointPolygonPreparation (EnergyRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.HorizontalBoundaryRequest (Traces
  Request)

open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LiftedEntries

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius
    : Data.Rat.Fraction.Rational} {grid : Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid
    preparation target radius}
  {observations : Riemann.RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars}
    {partitions : Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid}
  {surfaceCuts : Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.SurfaceCuts partitions domains}
  {first last : Fin grid.faces.regulars.length}
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) → Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights
    domains sheet} {error : Data.Rat.Fraction.Rational}

variable (requests : Riemann.Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests
  (fun sheet => Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains
    surfaceCuts sheet coarseDepth) fixed error)

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (FacePerimeterTraces)

variable {vertices : Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid.shrunk.prepared.grid} {edges :
  Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {mesh : Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges grid.faces} {sheet : Fin 2}
  (source : mesh.LocatedFace first sheet)

section VerticalCompleteContact

variable
  (firstTraces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces (requests.entries.get
    sheet) first)
  (lastTraces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces (requests.entries.get
    (Curves.Hyperelliptic.Meshes.Newton.Surface.LiftedEntries.VerticalContact.next (last := last) source).sheet) last)
  (matching : Riemann.Meshes.GridLiftedDualSteps.GridSide.Matches .right
    (grid.faces.regulars[first.val]'first.isLt).cell.box
    (grid.faces.regulars[last.val]'last.isLt).cell.box)
  (equal : (partitions.get first).cuts.y.intervals = (partitions.get last).cuts.y.intervals)

/-- The endpoint-polygon preparation on the actual lifted vertical contact owner and matched perimeter pieces. -/
@[expose] def Endpoints := PuncturedGrid.EndpointPolygonPreparation
  (leftEntry := (VerticalContact.firstEntry (domains := domains) source)) (rightEntry := (VerticalContact.lastEntry
    (domains := domains) source matching.1 matching.2.1 matching.2.2))
  (EndpointGeometry.verticalPieces firstTraces.pieces lastTraces.pieces (VerticalPieces.build _ _ equal matching.2.2))

namespace Endpoints

/-- Prepare the matched vertical endpoint polygon using the actual lifted corner coordinate. -/
@[expose] def build :
  Endpoints requests source
  firstTraces lastTraces matching equal :=
  EndpointPolygonPreparation.build _
    ((EndpointGeometry.vertical_origin firstTraces.pieces lastTraces.pieces equal matching.2.2).trans
      source.lifted.coordinates.2.1.symm)

end Endpoints

/-- The retained comparison traces on the matched vertical boundary pieces. -/
@[expose] def Traces := VerticalBoundaryRequest.Traces (VerticalContact.firstEntry (domains := domains) source)
  (VerticalContact.lastEntry (domains := domains) source matching.1 matching.2.1 matching.2.2) requests
  (VerticalPieces.build _ _ equal matching.2.2)

namespace Traces

/-- Prepare the retained vertical comparison traces on the original matched pieces. -/
@[expose] def build :
  Traces requests source
  matching equal :=
  VerticalBoundaryRequest.Traces.build (VerticalContact.firstEntry (domains := domains) source)
    (VerticalContact.lastEntry (domains := domains) source matching.1 matching.2.1 matching.2.2) requests
    (VerticalPieces.build _ _ equal matching.2.2)

end Traces

/-- The complete vertical contact request with both piece and polygon allowances chosen from the retained rows count. -/
@[expose] def Request (endpoints :
  Endpoints requests source
  firstTraces lastTraces matching equal)
    (traces : Traces requests
      source matching equal) (allowance : Fraction.Rational) (floor : Nat) :=
  let part := Contact.pieceContactTarget genus grid.faces.regulars.length
    ((PieceIndices.rows (partitions.get first)) + 1) allowance
  VerticalBoundaryRequest.Request (VerticalContact.firstEntry (domains := domains) source) (VerticalContact.lastEntry
    (domains := domains) source matching.1 matching.2.1 matching.2.2) requests firstTraces.pieces lastTraces.pieces
    (VerticalPieces.build _ _ equal matching.2.2) endpoints traces part part floor

set_option genInjectivity false in
/-- A complete paid vertical contact on the actual lifted corner owner.

Its endpoint preparation, perimeter traces and request retain the original neighboring faces and shared global
allowance. -/
structure Prepared (allowance : Fraction.Rational) (floor : Nat) where
  /-- The actual matched vertical endpoint-polygon preparation. -/ endpoints :
    Endpoints requests source
    firstTraces lastTraces matching equal
  /-- The retained vertical boundary comparison traces. -/ traces :
    Traces requests source
    matching equal
  /-- The paid complete contact request on those same retained endpoints and traces. -/ request :
    Request requests source
    firstTraces lastTraces matching equal endpoints traces allowance floor

constructive_injectivity Prepared

namespace Prepared

/-- Construct the actual vertical endpoint and trace preparations and allocate their positive piece and polygon
allowances. -/
@[expose] def build (allowance : Fraction.Rational) (positive : 0 < allowance) (floor : Nat) :
    Prepared requests source
      firstTraces lastTraces matching equal allowance floor := by
  let endpoints :=
    Endpoints.build requests
    source firstTraces lastTraces matching equal
  let traces := Traces.build
    requests source matching equal
  let part := Contact.pieceContactTarget genus grid.faces.regulars.length
    ((PieceIndices.rows (partitions.get first)) + 1) allowance
  have partPositive : 0 < part := Contact.pieceContactTarget_positive positive
  exact ⟨endpoints, traces, VerticalBoundaryRequest.Request.build (VerticalContact.firstEntry (domains := domains)
    source) (VerticalContact.lastEntry (domains := domains) source matching.1 matching.2.1 matching.2.2)
    requests firstTraces.pieces lastTraces.pieces (VerticalPieces.build _ _ equal matching.2.2) endpoints traces part
      part partPositive partPositive floor⟩

end Prepared

open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {requests source firstTraces lastTraces matching equal}

namespace Prepared

/-- At the paid common stage, the actual right and left centered-area discrepancy fits the global contact target with
its homogeneous coefficient factor. -/
theorem accurate {allowance : Fraction.Rational} {floor stage : Nat}
    (prepared : Prepared
      requests source firstTraces lastTraces matching equal allowance floor)
    (later : prepared.request.index ≤ stage)
    (cache : LocalMeshes.Numerics domains stage) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (firstSamples : FacePerimeterTraces.Centered firstTraces cache coefficients)
    (lastSamples : FacePerimeterTraces.Centered lastTraces cache coefficients) :
    Data.Gaussian.Norm.Basic.normSq (firstSamples.right.centeredArea - lastSamples.left.centeredArea) ≤
      (genus : Fraction.Rational)^2 * PreparedObservationCoercivity.coefficientNormSq coefficients^2 *
        SynchronizedSurfaceRequests.contactTarget genus grid.faces.regulars.length allowance / 4 := by
  have bound := BoundaryContactAccuracy.verticalBoundary_accurate (VerticalContact.firstEntry (domains := domains)
    source) (VerticalContact.lastEntry (domains := domains) source matching.1 matching.2.1 matching.2.2) requests
    firstTraces lastTraces
    equal matching.2.2 prepared.endpoints prepared.traces prepared.request later cache coefficients firstSamples
      lastSamples
  have estimate := bound.trans_eq (Contact.pieceContactTarget_face _ _ _ _ _)
  have coefficientIdentity :
      FiniteSum.Fin.sumFin (fun row : Fin genus => (coefficients row).normSq) =
        coefficientNormSq coefficients := by
    unfold coefficientNormSq
    rfl
  rw [← coefficientIdentity]
  convert estimate using 1
  rw [FiniteSum.Fin.sumFin_congr
    (fun row : Fin genus => (Data.Gaussian.Norm.Basic.normSq_eq_canonical (coefficients row)).symm)]

end Prepared

end VerticalCompleteContact
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.VerticalCompleteContact
