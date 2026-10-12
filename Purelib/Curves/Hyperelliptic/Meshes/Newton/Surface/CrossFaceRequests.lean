module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CrossFaceSides
public import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.ConjugateEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalConjugateEnergy
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! Coefficient-independent numerical contacts on the actual complete-surface
cross-face traces. The supplied entries certify the common root and the sheets
of the already retained domains. The trace uses the shared spatial depth,
and every contact index covers the synchronized surface-energy requests. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CrossFaceRequests

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational} {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars} {partitions
    : Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid}
  {surfaceCuts : Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.SurfaceCuts partitions domains}
  {first last : Fin grid.faces.regulars.length}
  {start : Gaussian.Basic.Canonical} {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
  (firstEntry : Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry (domains.get first).models start owner)
  (lastEntry : Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry (domains.get last).models start owner)
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) → RootContinuation.NewtonRequestedObservationEnergy.Preflights domains
    sheet} {error : Fraction.Rational}

variable (requests : Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests
  (fun sheet => Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts sheet
    coarseDepth) fixed error)

/-- Prepare coefficient-independent energy contacts on the actual horizontal cross-face trace, meeting both the
synchronized request stage and supplied floor. -/
def horizontalFaceRequest
    (pieces : Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.HorizontalPieces (partitions.get first) (partitions.get
      last))
    (trace : (Hyperelliptic.Meshes.Newton.Surface.CrossFaceSides.horizontalFaceSide (requests.entries.get
      firstEntry.sheet) (requests.entries.get lastEntry.sheet)
      first last pieces.firstPiece pieces.lastPiece
      pieces.lower_eq pieces.upper_eq pieces.joined).Trace requests.depth)
    (origin : trace.point (trace.vertices.indexed 0) = start)
    (allowance : Fraction.Rational) (positive : 0 < allowance) (floor : Nat) :
    let contacts := Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation.MatchedSidePreparation.build
      (leftEntry := firstEntry) (rightEntry := lastEntry) trace origin
    Hyperelliptic.Meshes.PuncturedGrid.Matched.ConjugateEnergy.MatchedSidePreparation.EnergyRequest contacts allowance
      (max requests.index floor) :=
  Hyperelliptic.Meshes.PuncturedGrid.Matched.ConjugateEnergy.MatchedSidePreparation.EnergyRequest.build
    (Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation.MatchedSidePreparation.build (leftEntry := firstEntry)
      (rightEntry := lastEntry) trace origin)
    allowance positive (max requests.index floor)

/-- Prepare coefficient-independent energy contacts on the actual vertical cross-face trace, meeting both the
synchronized request stage and supplied floor. -/
def verticalFaceRequest
    (pieces : Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.VerticalPieces (partitions.get first) (partitions.get
      last))
    (trace : (Hyperelliptic.Meshes.Newton.Surface.CrossFaceSides.verticalFaceSide (requests.entries.get
      firstEntry.sheet) (requests.entries.get lastEntry.sheet)
      first last pieces.firstPiece pieces.lastPiece
      pieces.lower_eq pieces.upper_eq pieces.joined).Trace requests.depth)
    (origin : trace.point (trace.vertices.indexed 0) = start)
    (allowance : Fraction.Rational) (positive : 0 < allowance) (floor : Nat) :
    let contacts :=
      Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation.MatchedVerticalSidePreparation.build
      (leftEntry := firstEntry) (rightEntry := lastEntry) trace origin
    Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalConjugateEnergy.MatchedVerticalSidePreparation.EnergyRequest
      contacts allowance (max requests.index floor) :=
  Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalConjugateEnergy.MatchedVerticalSidePreparation.EnergyRequest.build
    (Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation.MatchedVerticalSidePreparation.build (leftEntry
      := firstEntry) (rightEntry := lastEntry) trace origin)
    allowance positive (max requests.index floor)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CrossFaceRequests
