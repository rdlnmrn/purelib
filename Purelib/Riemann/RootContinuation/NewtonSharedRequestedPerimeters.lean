module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest
import Purelib.Integration.Polynomial.Rectangle.StitchedSideAreas
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Integration.Polynomial.Rectangle.StitchedSideRegrouping
import Purelib.Riemann.RootContinuation.NewtonSharedExteriorCellLists
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterEntries
import Purelib.Integration.Polynomial.Rectangle.ClippedPerimeterTransport
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.FramedPuncturedGrid
public import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Integration.RectangularOwnedTriangulation

public section

/-! The requested Newton face samples read the exact whole-face perimeter
on the shared exterior cut bank. Equality transport reuses all piece caches. -/
namespace Purelib.Riemann.RootContinuation.NewtonSharedRequestedPerimeters

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (surfaceMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest (BasisArcPreparations)
open Purelib.Riemann.Branches.NewtonSharedExteriorCuts (SharedExteriorCuts)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices (columns rows pieceIndex)
open Purelib.Riemann.Normalization
variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : NewtonPreparation original} {target radius : Data.Rat.Fraction.Rational} {grid : NewtonGrid preparation
    target radius}
  {observations : ProtectedObservations original} {lifted : LiftedPuncturedGrid grid.punctured}
  {domains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    grid.faces.regulars}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {partitions : SurfacePartitions observations grid} {preparations :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular domains}

open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)
open Purelib.Integration.Polynomial.Rectangle.StitchedSideAreas (Entry)

open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest (Assemblies)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface (FaceAssembly)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly (Perimeters)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (FacePerimeterTraces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas (seamValues)
variable {sheet : Fin 2} {initialDepth : Nat} {fixed : Preflights domains sheet} {error : Data.Rat.Fraction.Rational}
  {stage : Nat} {cache : Numerics domains stage} {coefficients :
    LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Riemann.Topology in
/-- The requested piece mesh is the shared surface mesh at the request depth.

Reduces the retained dependent-vector readbacks and uses the exact request depth equality, preserving the original
partition and domain owners. -/
theorem request_mesh_eq (shared : SharedExteriorCuts partitions preparations)
    (request : SurfaceRequest partitions (Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains
      shared.surface sheet initialDepth) fixed error)
    (position : Fin grid.faces.regulars.length) (piece : Fin (partitions.get position).cuts.boxes.length) :
    ((request.meshes.get position).entries.get piece) =
      (((Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet
        request.depth).get position).entries.get piece) := by
  rw [NewtonRequestedSurfaceEnergy.SurfaceRequest.mesh_eq request position piece,
    Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest.mesh_eq, request.depth_eq]
  dsimp only [Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes]
  rw [Vector.DependentVector.ofFn_get, Vector.DependentVector.ofFn_get]
  dsimp only [NewtonObservationSurfaceEnergy.LocalMeshes.build]
  rw [Vector.DependentVector.ofFn_get, Vector.DependentVector.ofFn_get]
  rfl

variable (shared : SharedExteriorCuts partitions preparations)
  {request : SurfaceRequest partitions (Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes
    partitions domains shared.surface sheet initialDepth) fixed error}
  {assemblies : Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest.Assemblies request cache
    coefficients} {perimeters : Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters assemblies}
  {position : Fin grid.faces.regulars.length} {traces :
    Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces request position}

open Purelib.Curves.Hyperelliptic in
open Purelib.LinearAlgebra.Gaussian in
/-- Whole clipped assembly at the requested surface depth.

Uses the original shared source cuts and coefficient-combined seam values from the retained numerical cache. -/
@[expose] def RequestedWholeAssembly
    (request : SurfaceRequest partitions (Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains
      shared.surface sheet initialDepth) fixed error)
    (cache : Numerics domains stage) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (position : Fin grid.faces.regulars.length) :=
  ClippedAssembly ((Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
    request.depth).entries.get position)
    (Meshes.Newton.Surface.SeamAreas.seamValues (sheet := sheet) cache coefficients position)

section
open Purelib.Curves.Hyperelliptic
open Purelib.Integration.Polynomial.Rectangle
open Purelib.Riemann.RootContinuation
/-- Identify the requested bottom sample area with the whole perimeter.

Transports each retained piece perimeter along its exact request-mesh equality and joins the column entries at the first
row without rebuilding the samples. -/
theorem bottom_sample_eq_whole
    (samples : Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered traces cache coefficients) (face :
      Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly perimeters position)
    {whole : RequestedWholeAssembly shared request cache coefficients position} (perimeter : whole.Perimeter) :
    samples.bottom.originalArea = perimeter.bottom := by
  let piece := fun column : Fin ((Meshes.Newton.Surface.PieceIndices.columns (partitions.get position)) + 1) =>
    (Meshes.Newton.Surface.PieceIndices.pieceIndex (partitions.get position)) column 0
  let transported := fun column => request_mesh_eq shared request position (piece column) ▸
    ((assemblies.get position).get (piece column))
  let transportedPerimeters := fun column => ClippedPerimeterTransport.cast (request_mesh_eq shared request position
    (piece column)) ((perimeters.get position).get (piece column))
  have joined := NewtonSharedExteriorCellLists.bottom_perimeter shared position sheet request.depth
    (Meshes.Newton.Surface.SeamAreas.seamValues (sheet := sheet) cache coefficients position) whole transported
      perimeter transportedPerimeters
  have retained := StitchedSideRegrouping.concatenate_congr (fun column =>
    (ClippedPerimeterTransport.cast_entries (request_mesh_eq shared request position (piece column)) ((perimeters.get
      position).get (piece column))).1)
  exact (Meshes.Newton.Surface.PerimeterEntries.FacePerimeterTraces.Centered.bottom_eq_joined samples face).trans
    (congrArg StitchedSideAreas.Entry.area (joined.trans retained)).symm

/-- Identify the requested top sample area with the whole perimeter.

Transports each retained piece perimeter along its exact request-mesh equality and joins the column entries at the last
row without rebuilding the samples. -/
theorem top_sample_eq_whole
    (samples : Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered traces cache coefficients) (face :
      Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly perimeters position)
    {whole : RequestedWholeAssembly shared request cache coefficients position} (perimeter : whole.Perimeter) :
    samples.top.originalArea = perimeter.top := by
  let piece := fun column : Fin ((Meshes.Newton.Surface.PieceIndices.columns (partitions.get position)) + 1) =>
    (Meshes.Newton.Surface.PieceIndices.pieceIndex (partitions.get position)) column (Fin.last
      (Meshes.Newton.Surface.PieceIndices.rows (partitions.get position)))
  let transported := fun column => request_mesh_eq shared request position (piece column) ▸
    ((assemblies.get position).get (piece column))
  let transportedPerimeters := fun column => ClippedPerimeterTransport.cast (request_mesh_eq shared request position
    (piece column)) ((perimeters.get position).get (piece column))
  have joined := NewtonSharedExteriorCellLists.top_perimeter shared position sheet request.depth
    (Meshes.Newton.Surface.SeamAreas.seamValues (sheet := sheet) cache coefficients position) whole transported
      perimeter transportedPerimeters
  have retained := StitchedSideRegrouping.concatenate_congr (fun column =>
    (ClippedPerimeterTransport.cast_entries (request_mesh_eq shared request position (piece column)) ((perimeters.get
      position).get (piece column))).2.2.1)
  exact (Meshes.Newton.Surface.PerimeterEntries.FacePerimeterTraces.Centered.top_eq_joined samples face).trans (congrArg
    StitchedSideAreas.Entry.area (joined.trans retained)).symm

/-- Identify the requested left sample area with the whole perimeter.

Transports each retained piece perimeter along its exact request-mesh equality and joins the row entries at the first
column without rebuilding the samples. -/
theorem left_sample_eq_whole
    (samples : Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered traces cache coefficients) (face :
      Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly perimeters position)
    {whole : RequestedWholeAssembly shared request cache coefficients position} (perimeter : whole.Perimeter) :
    samples.left.originalArea = perimeter.left := by
  let piece := fun row : Fin ((Meshes.Newton.Surface.PieceIndices.rows (partitions.get position)) + 1) =>
    (Meshes.Newton.Surface.PieceIndices.pieceIndex (partitions.get position)) 0 row
  let transported := fun row => request_mesh_eq shared request position (piece row) ▸
    ((assemblies.get position).get (piece row))
  let transportedPerimeters := fun row => ClippedPerimeterTransport.cast (request_mesh_eq shared request position (piece
    row)) ((perimeters.get position).get (piece row))
  have joined := NewtonSharedExteriorCellLists.left_perimeter shared position sheet request.depth
    (Meshes.Newton.Surface.SeamAreas.seamValues (sheet := sheet) cache coefficients position) whole transported
      perimeter transportedPerimeters
  have retained := StitchedSideRegrouping.concatenate_congr (fun row =>
    (ClippedPerimeterTransport.cast_entries (request_mesh_eq shared request position (piece row)) ((perimeters.get
      position).get (piece row))).2.2.2)
  exact (Meshes.Newton.Surface.PerimeterEntries.FacePerimeterTraces.Centered.left_eq_joined samples face).trans
    (congrArg StitchedSideAreas.Entry.area (joined.trans retained)).symm

/-- Identify the requested right sample area with the whole perimeter.

Transports each retained piece perimeter along its exact request-mesh equality and joins the row entries at the last
column without rebuilding the samples. -/
theorem right_sample_eq_whole
    (samples : Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered traces cache coefficients) (face :
      Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly perimeters position)
    {whole : RequestedWholeAssembly shared request cache coefficients position} (perimeter : whole.Perimeter) :
    samples.right.originalArea = perimeter.right := by
  let piece := fun row : Fin ((Meshes.Newton.Surface.PieceIndices.rows (partitions.get position)) + 1) =>
    (Meshes.Newton.Surface.PieceIndices.pieceIndex (partitions.get position)) (Fin.last
      (Meshes.Newton.Surface.PieceIndices.columns (partitions.get position))) row
  let transported := fun row => request_mesh_eq shared request position (piece row) ▸
    ((assemblies.get position).get (piece row))
  let transportedPerimeters := fun row => ClippedPerimeterTransport.cast (request_mesh_eq shared request position (piece
    row)) ((perimeters.get position).get (piece row))
  have joined := NewtonSharedExteriorCellLists.right_perimeter shared position sheet request.depth
    (Meshes.Newton.Surface.SeamAreas.seamValues (sheet := sheet) cache coefficients position) whole transported
      perimeter transportedPerimeters
  have retained := StitchedSideRegrouping.concatenate_congr (fun row =>
    (ClippedPerimeterTransport.cast_entries (request_mesh_eq shared request position (piece row)) ((perimeters.get
      position).get (piece row))).2.1)
  exact (Meshes.Newton.Surface.PerimeterEntries.FacePerimeterTraces.Centered.right_eq_joined samples face).trans
    (congrArg StitchedSideAreas.Entry.area (joined.trans retained)).symm

end

open Purelib.Curves.Hyperelliptic in
/-- The requested face exterior equals the whole clipped exterior.

Combines the four exact side readbacks with the retained face and whole-perimeter decompositions, preserving orientation
and endpoint corrections. -/
theorem face_exterior_eq_whole
    (samples : Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered traces cache coefficients) (face :
      Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly perimeters position)
    {whole : RequestedWholeAssembly shared request cache coefficients position} (perimeter : whole.Perimeter) :
    face.exterior = whole.exterior := by
  have original := Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces.exterior_eq traces face
  change face.exterior =
    traces.bottom.area (Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.ownerValues cache coefficients
      position) +
      traces.right.area (Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.ownerValues cache coefficients
        position) -
      traces.top.area (Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.ownerValues cache coefficients
        position) -
      traces.left.area (Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.ownerValues cache coefficients
        position) at original
  rw [samples.bottom_area, samples.right_area, samples.top_area, samples.left_area,
    ← samples.bottom.decomposition, ← samples.right.decomposition,
    ← samples.top.decomposition, ← samples.left.decomposition,
    bottom_sample_eq_whole shared samples face perimeter, right_sample_eq_whole shared samples face perimeter,
    top_sample_eq_whole shared samples face perimeter, left_sample_eq_whole shared samples face perimeter] at original
  exact original.trans perimeter.exterior_eq.symm

end Purelib.Riemann.RootContinuation.NewtonSharedRequestedPerimeters
