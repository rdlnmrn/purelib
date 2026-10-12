module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
public import Purelib.Integration.Path.JoinedCenteredArea
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters

open Purelib.Integration.Path

open Purelib.Riemann.Periods

@[expose] public section

/-! The complete face's centered perimeter equals its cached piece-centered
areas plus the actual polygon of piece endpoints, retaining all owner joins. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes SurfaceRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest (Assemblies)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly (Perimeters)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (FacePerimeterTraces)

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
    grid.faces.regulars} {sheet : Fin 2}
  {partitions : SurfacePartitions observations grid} {coarse :
    SurfaceMeshes partitions domains sheet}
  {fixed : Preflights domains sheet} {error :
    Rational}
  {energy : SurfaceRequest partitions coarse fixed error}
  {stage : Nat} {cache : Numerics domains
    stage} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {assemblies : ExteriorRequest.Assemblies energy
    cache coefficients} {perimeters : Perimeters
    assemblies}
  {position : Fin grid.faces.regulars.length}

open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub)

namespace Centered

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

variable {traces : FacePerimeterTraces energy
  position}

/-- The complete original bottom centered area equals its retained piece-centered area sum plus the actual
piece-endpoint polygon area. -/
theorem bottom_concatenate (samples : FacePerimeterTraces.Centered traces cache coefficients)
    (pieces : (index : Fin ((PieceIndices.columns (partitions.get position)) + 1)) →
      CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients position
        ((traces.pieces.bottomPieces index).indexed vertex)))
    (polygon : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients position
      ((JoinedCenteredArea.endpointPolygon traces.pieces.bottomPieces).indexed vertex))) :
    samples.bottom.centeredArea = FiniteSum.Fin.sumFin (fun index => (pieces index).centeredArea) + polygon.centeredArea
      :=
  JoinedCenteredArea.centered_concatenate traces.pieces.bottomPieces (FacePerimeterTraces.ownerValues cache coefficients
    position)
    traces.bottom_eq pieces samples.bottom polygon

/-- The complete original right centered area equals its retained piece-centered area sum plus the actual piece-endpoint
polygon area. -/
theorem right_concatenate (samples : FacePerimeterTraces.Centered traces cache coefficients)
    (pieces : (index : Fin ((PieceIndices.rows (partitions.get position)) + 1)) →
      CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients position
        ((traces.pieces.rightPieces index).indexed vertex)))
    (polygon : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients position
      ((JoinedCenteredArea.endpointPolygon traces.pieces.rightPieces).indexed vertex))) :
    samples.right.centeredArea = FiniteSum.Fin.sumFin (fun index => (pieces index).centeredArea) + polygon.centeredArea
      :=
  JoinedCenteredArea.centered_concatenate traces.pieces.rightPieces (FacePerimeterTraces.ownerValues cache coefficients
    position)
    traces.right_eq pieces samples.right polygon

/-- The complete original top centered area equals its retained piece-centered area sum plus the actual piece-endpoint
polygon area. -/
theorem top_concatenate (samples : FacePerimeterTraces.Centered traces cache coefficients)
    (pieces : (index : Fin ((PieceIndices.columns (partitions.get position)) + 1)) →
      CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients position
        ((traces.pieces.topPieces index).indexed vertex)))
    (polygon : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients position
      ((JoinedCenteredArea.endpointPolygon traces.pieces.topPieces).indexed vertex))) :
    samples.top.centeredArea = FiniteSum.Fin.sumFin (fun index => (pieces index).centeredArea) + polygon.centeredArea :=
  JoinedCenteredArea.centered_concatenate traces.pieces.topPieces (FacePerimeterTraces.ownerValues cache coefficients
    position)
    traces.top_eq pieces samples.top polygon

/-- The complete original left centered area equals its retained piece-centered area sum plus the actual piece-endpoint
polygon area. -/
theorem left_concatenate (samples : FacePerimeterTraces.Centered traces cache coefficients)
    (pieces : (index : Fin ((PieceIndices.rows (partitions.get position)) + 1)) →
      CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients position
        ((traces.pieces.leftPieces index).indexed vertex)))
    (polygon : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients position
      ((JoinedCenteredArea.endpointPolygon traces.pieces.leftPieces).indexed vertex))) :
    samples.left.centeredArea = FiniteSum.Fin.sumFin (fun index => (pieces index).centeredArea) + polygon.centeredArea
      :=
  JoinedCenteredArea.centered_concatenate traces.pieces.leftPieces (FacePerimeterTraces.ownerValues cache coefficients
    position)
    traces.left_eq pieces samples.left polygon

end Centered
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces
