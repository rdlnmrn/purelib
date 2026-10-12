module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Integration.Path.JoinedCenteredArea
import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPieces
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
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Integration.Path.JoinedTrace

open Purelib.Riemann.Periods

@[expose] public section

/-! Complete-face centered comparisons pay both piece areas and endpoint
polygons. Adjacent faces keep their distinct indexing and primitive owners. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredComparison

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (FacePerimeterTraces)

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

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
  {firstSheet lastSheet : Fin 2} {firstDepth lastDepth : Nat}
  {firstFixed : Preflights domains firstSheet}
    {lastFixed : Preflights domains lastSheet}
  {firstError lastError : Rational}

variable {firstRequest : SurfaceRequest partitions
  (Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
  firstSheet firstDepth) firstFixed firstError}
  {lastRequest : SurfaceRequest partitions
    (Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
    lastSheet lastDepth) lastFixed lastError}
  {first last : Fin grid.faces.regulars.length}
  {stage : Nat} {cache : Numerics domains
    stage} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {firstTraces : FacePerimeterTraces firstRequest
    first} {lastTraces : FacePerimeterTraces
    lastRequest last}

namespace FacePerimeterComparison

/-- Casting the original finite piece indices along their count equality preserves the complete retained concatenated
trace. -/
private theorem concatenate_cast {Vertex : Type} {firstCount lastCount : Nat}
    (equal : firstCount + 1 = lastCount + 1) (traces : Fin (lastCount + 1) → JoinedTrace.VertexTrace Vertex) :
    VertexTrace.concatenate (fun index => traces (Fin.cast equal index)) = VertexTrace.concatenate traces := by
  have same := Nat.succ.inj equal
  cases same
  rfl

/-- The original complete top-versus-bottom centered area discrepancy is bounded by its retained piece errors and full
endpoint polygon error.

The distinct face owners and actual count transport remain explicit. -/
theorem horizontal
    (counts : (PieceIndices.columns (partitions.get first)) + 1 = (PieceIndices.columns (partitions.get last)) + 1)
    (firstSamples : FacePerimeterTraces.Centered firstTraces cache coefficients)
    (lastSamples : FacePerimeterTraces.Centered lastTraces cache coefficients)
    (firstPieces : (index : Fin ((PieceIndices.columns (partitions.get first)) + 1)) →
      CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients first
        ((firstTraces.pieces.topPieces index).indexed vertex)))
    (lastPieces : (index : Fin ((PieceIndices.columns (partitions.get first)) + 1)) →
      CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients last
        ((lastTraces.pieces.bottomPieces (Fin.cast counts index)).indexed vertex)))
    (firstPolygon : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients first
      ((JoinedCenteredArea.endpointPolygon firstTraces.pieces.topPieces).indexed vertex)))
    (lastPolygon : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients last
      ((JoinedCenteredArea.endpointPolygon (fun index => lastTraces.pieces.bottomPieces (Fin.cast counts
        index))).indexed vertex)))
    {pieceAllowance polygonAllowance : Fraction.Rational}
    (piecesBound : ∀ index, Data.Gaussian.Norm.Basic.normSq ((firstPieces index).centeredArea - (lastPieces
      index).centeredArea) ≤ pieceAllowance)
    (polygonBound : Data.Gaussian.Norm.Basic.normSq (firstPolygon.centeredArea - lastPolygon.centeredArea) ≤
      polygonAllowance) :
    Data.Gaussian.Norm.Basic.normSq (firstSamples.top.centeredArea - lastSamples.bottom.centeredArea) ≤
      2 * ((((PieceIndices.columns (partitions.get first)) + 1 : Nat) : Fraction.Rational)^2 * pieceAllowance +
        polygonAllowance) :=
  JoinedCenteredArea.centered_comparison_bound firstTraces.pieces.topPieces
    (fun index => lastTraces.pieces.bottomPieces (Fin.cast counts index))
    (FacePerimeterTraces.ownerValues cache coefficients first) (FacePerimeterTraces.ownerValues cache coefficients last)
    firstTraces.top_eq (lastTraces.bottom_eq.trans
      (concatenate_cast counts
      lastTraces.pieces.bottomPieces).symm)
    firstPieces lastPieces firstSamples.top lastSamples.bottom firstPolygon lastPolygon piecesBound polygonBound

/-- The original complete right-versus-left centered area discrepancy is bounded by its retained piece errors and full
endpoint polygon error.

The distinct face owners and actual count transport remain explicit. -/
theorem vertical
    (counts : (PieceIndices.rows (partitions.get first)) + 1 = (PieceIndices.rows (partitions.get last)) + 1)
    (firstSamples : FacePerimeterTraces.Centered firstTraces cache coefficients)
    (lastSamples : FacePerimeterTraces.Centered lastTraces cache coefficients)
    (firstPieces : (index : Fin ((PieceIndices.rows (partitions.get first)) + 1)) →
      CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients first
        ((firstTraces.pieces.rightPieces index).indexed vertex)))
    (lastPieces : (index : Fin ((PieceIndices.rows (partitions.get first)) + 1)) →
      CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients last
        ((lastTraces.pieces.leftPieces (Fin.cast counts index)).indexed vertex)))
    (firstPolygon : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients first
      ((JoinedCenteredArea.endpointPolygon firstTraces.pieces.rightPieces).indexed vertex)))
    (lastPolygon : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients last
      ((JoinedCenteredArea.endpointPolygon (fun index => lastTraces.pieces.leftPieces (Fin.cast counts index))).indexed
        vertex)))
    {pieceAllowance polygonAllowance : Fraction.Rational}
    (piecesBound : ∀ index, Data.Gaussian.Norm.Basic.normSq ((firstPieces index).centeredArea - (lastPieces
      index).centeredArea) ≤ pieceAllowance)
    (polygonBound : Data.Gaussian.Norm.Basic.normSq (firstPolygon.centeredArea - lastPolygon.centeredArea) ≤
      polygonAllowance) :
    Data.Gaussian.Norm.Basic.normSq (firstSamples.right.centeredArea - lastSamples.left.centeredArea) ≤
      2 * ((((PieceIndices.rows (partitions.get first)) + 1 : Nat) : Fraction.Rational)^2 * pieceAllowance +
        polygonAllowance) :=
  JoinedCenteredArea.centered_comparison_bound firstTraces.pieces.rightPieces
    (fun index => lastTraces.pieces.leftPieces (Fin.cast counts index))
    (FacePerimeterTraces.ownerValues cache coefficients first) (FacePerimeterTraces.ownerValues cache coefficients last)
    firstTraces.right_eq (lastTraces.left_eq.trans
      (concatenate_cast counts
      lastTraces.pieces.leftPieces).symm)
    firstPieces lastPieces firstSamples.right lastSamples.left firstPolygon lastPolygon piecesBound polygonBound

end FacePerimeterComparison
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredComparison
