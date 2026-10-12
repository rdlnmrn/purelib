module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Polynomial.Rectangle.StitchedSideAreas
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
public import Purelib.Integration.Polynomial.Rectangle.ClippedPerimeterEntries
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters

open Purelib.Integration.Polynomial.Rectangle.ClippedPerimeterEntries

open Purelib.Integration.Polynomial.Rectangle.StitchedSideAreas

@[expose] public section

/-! Exact readback from the original-area samples of each complete face to
the concatenated cached piece perimeters, with all joining chords retained. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterEntries

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes SurfaceRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest (Assemblies)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly (Perimeters)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (FacePerimeterTraces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces (Centered)
open Purelib.Integration.Polynomial.Rectangle.ClippedPerimeterEntries.Perimeter

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

open Purelib.Algebra.FiniteSum.Fin (sumFin_congr)
namespace FacePerimeterTraces.Centered
variable {traces : FacePerimeterTraces energy
  position}

/-- The original complete bottom sample area equals its concatenated cached piece-perimeter area with every joining
chord retained. -/
theorem bottom_eq_joined (samples : FacePerimeterTraces.Centered traces cache coefficients)
    (face : FaceAssembly perimeters position) :
    samples.bottom.originalArea =
      (Entry.concatenate (fun column : Fin ((PieceIndices.columns (partitions.get position)) + 1) =>
        Perimeter.bottomEntry ((perimeters.get position).get (PieceIndices.pieceIndex (partitions.get position) column
          0)))).area := by
  apply samples.bottom.decomposition.trans
  apply samples.bottom_area.symm.trans
  apply (traces.bottom_area face).trans
  rw [Entry.concatenate_area]
  apply congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => a + b)
  · rfl
  · apply FiniteSum.Fin.sumFin_congr
    intro index
    rw [face.corners_eq, face.corners_eq]
    rfl

/-- The original complete top sample area equals its concatenated cached piece-perimeter area with every joining chord
retained. -/
theorem top_eq_joined (samples : FacePerimeterTraces.Centered traces cache coefficients)
    (face : FaceAssembly perimeters position) :
    samples.top.originalArea =
      (Entry.concatenate (fun column : Fin ((PieceIndices.columns (partitions.get position)) + 1) =>
        Perimeter.topEntry ((perimeters.get position).get (PieceIndices.pieceIndex (partitions.get position) column
          (Fin.last (PieceIndices.rows (partitions.get position))))))).area := by
  apply samples.top.decomposition.trans
  apply samples.top_area.symm.trans
  apply (traces.top_area face).trans
  rw [Entry.concatenate_area]
  apply congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => a + b)
  · rfl
  · apply FiniteSum.Fin.sumFin_congr
    intro index
    rw [face.corners_eq, face.corners_eq]
    rfl

/-- The original complete left sample area equals its concatenated cached piece-perimeter area with every joining chord
retained. -/
theorem left_eq_joined (samples : FacePerimeterTraces.Centered traces cache coefficients)
    (face : FaceAssembly perimeters position) :
    samples.left.originalArea =
      (Entry.concatenate (fun row : Fin ((PieceIndices.rows (partitions.get position)) + 1) =>
        Perimeter.leftEntry ((perimeters.get position).get (PieceIndices.pieceIndex (partitions.get position) 0
          row)))).area := by
  apply samples.left.decomposition.trans
  apply samples.left_area.symm.trans
  apply (traces.left_area face).trans
  rw [Entry.concatenate_area]
  apply congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => a + b)
  · rfl
  · apply FiniteSum.Fin.sumFin_congr
    intro index
    rw [face.corners_eq, face.corners_eq]
    rfl

/-- The original complete right sample area equals its concatenated cached piece-perimeter area with every joining chord
retained. -/
theorem right_eq_joined (samples : FacePerimeterTraces.Centered traces cache coefficients)
    (face : FaceAssembly perimeters position) :
    samples.right.originalArea =
      (Entry.concatenate (fun row : Fin ((PieceIndices.rows (partitions.get position)) + 1) =>
        Perimeter.rightEntry ((perimeters.get position).get (PieceIndices.pieceIndex (partitions.get position) (Fin.last
          (PieceIndices.columns (partitions.get position))) row)))).area := by
  apply samples.right.decomposition.trans
  apply samples.right_area.symm.trans
  apply (traces.right_area face).trans
  rw [Entry.concatenate_area]
  apply congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => a + b)
  · rfl
  · apply FiniteSum.Fin.sumFin_congr
    intro index
    rw [face.corners_eq, face.corners_eq]
    rfl

end FacePerimeterTraces.Centered
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterEntries
