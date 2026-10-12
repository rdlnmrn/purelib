module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CrossFaceSides
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CrossFaceRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.ConjugateEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalConjugateEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation
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
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters

open Purelib.Data.Rat

open Purelib.Riemann.Paths

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh

open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly

@[expose] public section

/-! The synchronized contact request controls the actual retained surface
piece perimeters on the same numerical bank and common spatial depth. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceContactAccuracy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces (HorizontalPieces VerticalPieces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CrossFaceSides (horizontalFaceSide verticalFaceSide)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CrossFaceRequests (horizontalFaceRequest verticalFaceRequest)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational} {grid :
    NewtonGrid preparation target radius}
  {observations : ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : FaceDomainBank frames
    grid.faces.regulars} {partitions : SurfacePartitions
    observations grid}
  {surfaceCuts : SurfaceCuts partitions domains}
  {first last : Fin grid.faces.regulars.length}
  {start : Purelib.Data.Gaussian.Basic.Canonical} {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    (curve.polynomial.eval start)}
  (firstEntry : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry (domains.get
    first).models start owner)
  (lastEntry : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry (domains.get last).models
    start owner)
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet} {error :
    Rational}

variable (requests : SynchronizedSurfaceRequests
  (fun sheet => Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains
    surfaceCuts sheet coarseDepth) fixed error)

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (PiecePerimeterTraces FacePerimeterTraces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces (ownerValues)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas (seamValues)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)

variable {stage : Nat} (cache : Numerics
  domains stage) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

/-- The synchronized original horizontal face request bounds the difference of its actual two centered piece areas.

The same retained banks, shared root owner and arbitrary coefficient vector are used at the paid common stage and depth.
-/
theorem horizontalFaceRequest_accurate
    (pieces : BoundaryPieces.HorizontalPieces (partitions.get first) (partitions.get last))
    (trace : (CrossFaceSides.horizontalFaceSide (requests.entries.get firstEntry.sheet) (requests.entries.get
      lastEntry.sheet)
      first last pieces.firstPiece pieces.lastPiece
      pieces.lower_eq pieces.upper_eq pieces.joined).Trace requests.depth)
    (origin : trace.point (trace.vertices.indexed 0) = start)
    (allowance : Fraction.Rational) (positive : 0 < allowance) (floor : Nat)
    (later : (CrossFaceRequests.horizontalFaceRequest firstEntry lastEntry requests pieces trace origin allowance
      positive floor).index ≤ stage)
    (firstTraces : PerimeterTraces.PiecePerimeterTraces (requests.entries.get firstEntry.sheet) first)
    (lastTraces : PerimeterTraces.PiecePerimeterTraces (requests.entries.get lastEntry.sheet) last)
    (left : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients first
      ((RectangularOwnedPerimeterTraces.topOwned (firstTraces.get pieces.firstPiece)).indexed vertex)))
    (right : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients last
      ((RectangularOwnedPerimeterTraces.bottomOwned (lastTraces.get pieces.lastPiece)).indexed vertex))) :
    Data.Gaussian.Norm.Basic.normSq (left.centeredArea - right.centeredArea) ≤
      (genus : Fraction.Rational)^2 * (FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Norm.Basic.normSq
        (coefficients i)))^2 * allowance := by
  let request := CrossFaceRequests.horizontalFaceRequest firstEntry lastEntry requests pieces trace origin allowance
    positive floor
  let leftAssembly := ClippedAssembly.build
    (((requests.entries.get firstEntry.sheet).meshes.get first).entries.get pieces.firstPiece)
    (SeamAreas.seamValues (sheet := firstEntry.sheet) cache coefficients first)
  let rightAssembly := ClippedAssembly.build
    (((requests.entries.get lastEntry.sheet).meshes.get last).entries.get pieces.lastPiece)
    (SeamAreas.seamValues (sheet := lastEntry.sheet) cache coefficients last)
  exact request.owned_accurate later (fun i => cache.atDomain first firstEntry.sheet i)
    (fun i => cache.atDomain last lastEntry.sheet i) coefficients
    (firstTraces.get pieces.firstPiece) (lastTraces.get pieces.lastPiece) left right
    leftAssembly rightAssembly (Perimeter.build leftAssembly) (Perimeter.build rightAssembly)
    (((requests.entries.get firstEntry.sheet).mesh_depth first pieces.firstPiece).trans (requests.depth_eq
      firstEntry.sheet)).symm
    (((requests.entries.get lastEntry.sheet).mesh_depth last pieces.lastPiece).trans (requests.depth_eq
      lastEntry.sheet)).symm
    rfl pieces.joined

/-- The synchronized original vertical face request bounds the difference of its actual two centered piece areas.

The original right and left piece traces are evaluated with the same coefficients at their paid common stage and depth.
-/
theorem verticalFaceRequest_accurate
    (pieces : BoundaryPieces.VerticalPieces (partitions.get first) (partitions.get last))
    (trace : (CrossFaceSides.verticalFaceSide (requests.entries.get firstEntry.sheet) (requests.entries.get
      lastEntry.sheet)
      first last pieces.firstPiece pieces.lastPiece
      pieces.lower_eq pieces.upper_eq pieces.joined).Trace requests.depth)
    (origin : trace.point (trace.vertices.indexed 0) = start)
    (allowance : Fraction.Rational) (positive : 0 < allowance) (floor : Nat)
    (later : (CrossFaceRequests.verticalFaceRequest firstEntry lastEntry requests pieces trace origin allowance positive
      floor).index ≤ stage)
    (firstTraces : PerimeterTraces.PiecePerimeterTraces (requests.entries.get firstEntry.sheet) first)
    (lastTraces : PerimeterTraces.PiecePerimeterTraces (requests.entries.get lastEntry.sheet) last)
    (left : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients first
      ((RectangularOwnedPerimeterTraces.rightOwned (firstTraces.get pieces.firstPiece)).indexed vertex)))
    (right : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients last
      ((RectangularOwnedPerimeterTraces.leftOwned (lastTraces.get pieces.lastPiece)).indexed vertex))) :
    Data.Gaussian.Norm.Basic.normSq (left.centeredArea - right.centeredArea) ≤
      (genus : Fraction.Rational)^2 * (FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Norm.Basic.normSq
        (coefficients i)))^2 * allowance := by
  let request := CrossFaceRequests.verticalFaceRequest firstEntry lastEntry requests pieces trace origin allowance
    positive floor
  let leftAssembly := ClippedAssembly.build
    (((requests.entries.get firstEntry.sheet).meshes.get first).entries.get pieces.firstPiece)
    (SeamAreas.seamValues (sheet := firstEntry.sheet) cache coefficients first)
  let rightAssembly := ClippedAssembly.build
    (((requests.entries.get lastEntry.sheet).meshes.get last).entries.get pieces.lastPiece)
    (SeamAreas.seamValues (sheet := lastEntry.sheet) cache coefficients last)
  exact request.owned_accurate later (fun i => cache.atDomain first firstEntry.sheet i)
    (fun i => cache.atDomain last lastEntry.sheet i) coefficients
    (firstTraces.get pieces.firstPiece) (lastTraces.get pieces.lastPiece) left right
    leftAssembly rightAssembly (Perimeter.build leftAssembly) (Perimeter.build rightAssembly)
    (((requests.entries.get firstEntry.sheet).mesh_depth first pieces.firstPiece).trans (requests.depth_eq
      firstEntry.sheet)).symm
    (((requests.entries.get lastEntry.sheet).mesh_depth last pieces.lastPiece).trans (requests.depth_eq
      lastEntry.sheet)).symm
    rfl pieces.joined

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceContactAccuracy
