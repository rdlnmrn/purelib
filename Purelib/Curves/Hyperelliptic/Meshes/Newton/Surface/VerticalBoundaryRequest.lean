module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CrossFaceSides
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointGeometry
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceOrigins
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointTraceHandoffs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalConjugateEnergy
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.RectangularEndpointPieceOrigins
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceRequests
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.PairedEndpointPolygon
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularPairedEndpointReadings
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
meta import Mathlib.Tactic.Linter.Lint

public section

/-! One retained request bank and common tail cover the endpoint polygon
and every matched piece on a complete face boundary. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.VerticalBoundaryRequest

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceOrigins
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonEnergy
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonEnergy.EndpointPolygonPreparation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointTraceHandoffs
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalConjugateEnergy
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Riemann.Integration.RectangularEndpointPieceOrigins
open Purelib.Riemann.Paths
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide

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
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces (VerticalPieces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointGeometry
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (PiecePerimeterTraces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceRequests (verticalPieceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (EndpointPolygonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonEnergy.EndpointPolygonPreparation (EnergyRequest)

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
  {start : Data.Gaussian.Basic.Canonical} {owner : Riemann.Topology.SquareRootContinuationChain.Owner
    (curve.polynomial.eval start)}
  (firstEntry : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry (domains.get first).models start
    owner)
  (lastEntry : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry (domains.get last).models start
    owner)
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) → Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights
    domains sheet} {error : Data.Rat.Fraction.Rational}

variable (requests : Riemann.Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests
  (fun sheet => Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains
    surfaceCuts sheet coarseDepth) fixed error)

variable
  (firstTraces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.PiecePerimeterTraces (requests.entries.get
    firstEntry.sheet) first)
  (lastTraces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.PiecePerimeterTraces (requests.entries.get
    lastEntry.sheet) last)

section VerticalBoundaryRequest

variable {count : Nat}
  (pieces : Fin (count + 1) → Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.VerticalPieces (partitions.get
    first) (partitions.get last))
  (endpoints : PuncturedGrid.EndpointPolygonPreparation
    (leftEntry := firstEntry) (rightEntry := lastEntry)
    (EndpointGeometry.verticalPieces firstTraces lastTraces
      pieces))

/-- The original matched vertical trace on every retained cross-face piece at the shared surface depth. -/
@[expose] def Traces := Data.Vector.DependentVector (fun piece =>
  (CrossFaceSides.verticalFaceSide (requests.entries.get firstEntry.sheet) (requests.entries.get lastEntry.sheet)
    first last (pieces piece).firstPiece (pieces piece).lastPiece
    (pieces piece).lower_eq (pieces piece).upper_eq (pieces piece).joined).Trace requests.depth)

namespace Traces

/-- Construct each original matched vertical trace on its retained cross-face side and common surface depth. -/
@[expose] def build :
  Traces firstEntry lastEntry
  requests pieces :=
  DependentVector.ofFn fun piece =>
    Trace.build
      (CrossFaceSides.verticalFaceSide (requests.entries.get firstEntry.sheet) (requests.entries.get lastEntry.sheet)
        first last (pieces piece).firstPiece (pieces piece).lastPiece
        (pieces piece).lower_eq (pieces piece).upper_eq (pieces piece).joined) requests.depth

end Traces

variable (traces : Traces
  firstEntry lastEntry requests pieces)

/-- The original vertical conjugate energy request bank, using the retained endpoint contacts and piece origins. -/
@[expose] def PieceRequests (allowance : Fraction.Rational) (floor : Nat) := Data.Vector.DependentVector (fun piece =>
  let vertex := VertexTrace.pairedEndpointStart
    (fun index => RectangularOwnedPerimeterTraces.rightOwned (firstTraces.get (pieces index).firstPiece))
    (fun index => RectangularOwnedPerimeterTraces.leftOwned (lastTraces.get (pieces index).lastPiece)) piece
  let contact := EndpointPolygonPreparation.verticalAt endpoints vertex (traces.get piece)
    (EndpointGeometry.verticalPiece_origin firstTraces lastTraces pieces piece (traces.get piece))
  MatchedVerticalSidePreparation.EnergyRequest contact allowance (max requests.index floor))

namespace PieceRequests

/-- Prepare every original vertical piece energy request from its retained endpoint contact and actual piece origin. -/
@[expose] def build (allowance : Fraction.Rational) (positive : 0 < allowance) (floor : Nat) :
    PieceRequests firstEntry
      lastEntry requests firstTraces lastTraces pieces endpoints traces allowance floor :=
  DependentVector.ofFn fun piece => PieceRequests.verticalPieceRequest firstEntry lastEntry requests
    firstTraces lastTraces pieces endpoints piece (traces.get piece) allowance positive floor

end PieceRequests

variable {pieceAllowance polygonAllowance : Data.Rat.Fraction.Rational} {floor : Nat}

namespace PieceRequests

/-- The supplied common stage pays every original vertical piece request. -/
@[expose] def IndexBound
    (entries : PieceRequests
      firstEntry lastEntry requests firstTraces lastTraces pieces endpoints traces pieceAllowance floor)
    (index : Nat) : Prop := ∀ piece, (entries.get piece).index ≤ index

end PieceRequests

set_option genInjectivity false in
/-- A complete vertical boundary schedule retaining its endpoint polygon and every original matched piece request.

One common stage pays both request families, the original surface schedule and the supplied floor. -/
structure Request (pieceAllowance polygonAllowance : Fraction.Rational) (floor : Nat) where
  /-- The original endpoint polygon energy request with the retained surface and numerical floors. -/ polygon :
    EndpointPolygonPreparation.EnergyRequest endpoints polygonAllowance (max requests.index floor)
  /-- All original vertical matched-piece energy requests on the same retained endpoint preparation. -/ entries :
    PieceRequests firstEntry
    lastEntry requests firstTraces lastTraces pieces endpoints traces pieceAllowance floor
  /-- The cached common stage paying the original complete boundary schedule. -/ index : Nat
  /-- The common stage pays the original retained endpoint polygon request. -/ polygon_le : polygon.index ≤ index
  /-- The common stage pays every original retained piece request. -/ entries_le :
    PieceRequests.IndexBound
    firstEntry lastEntry requests firstTraces lastTraces pieces endpoints traces entries index
  /-- The common stage pays the original synchronized surface requests. -/ surface_le : requests.index ≤ index
  /-- The common stage is no smaller than the original requested floor. -/ floor_le : floor ≤ index

constructive_injectivity Request

namespace Request

/-- Prepare the original endpoint polygon and all vertical piece requests, then retain one maximum stage paying the
complete boundary schedule. -/
@[expose] def build (pieceAllowance polygonAllowance : Fraction.Rational)
    (piecePositive : 0 < pieceAllowance) (polygonPositive : 0 < polygonAllowance) (floor : Nat) :
    Request firstEntry
      lastEntry requests firstTraces lastTraces pieces endpoints traces pieceAllowance polygonAllowance floor := by
  let polygon := EnergyRequest.build endpoints polygonAllowance polygonPositive
    (max requests.index floor)
  let entries :=
    PieceRequests.build
    firstEntry lastEntry requests firstTraces lastTraces pieces endpoints traces
    pieceAllowance piecePositive floor
  let maximum := entries.maximum fun _ request => request.index
  refine ⟨polygon, entries, max polygon.index maximum, Data.Nat.Order.le_max_left _ _, ?_, ?_, ?_⟩
  · intro piece
    exact (entries.get_le_maximum (fun _ request => request.index) piece).trans (Data.Nat.Order.le_max_right _ _)
  · exact (Data.Nat.Order.le_max_left _ _).trans (polygon.floor_le.trans (Data.Nat.Order.le_max_left _ _))
  · exact (Data.Nat.Order.le_max_right _ _).trans (polygon.floor_le.trans (Data.Nat.Order.le_max_left _ _))

end Request

end VerticalBoundaryRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.VerticalBoundaryRequest
