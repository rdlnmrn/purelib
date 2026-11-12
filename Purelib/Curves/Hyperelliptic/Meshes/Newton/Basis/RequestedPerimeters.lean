module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest
import Purelib.Integration.Polynomial.Rectangle.StitchedSideAreas

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
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Polynomial.Rectangle.ClippedPerimeterTransport
public import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.PerimeterReadback
import Purelib.Riemann.RootContinuation.NewtonSharedRequestedPerimeters
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.PerimeterReadback

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.Vector

open Purelib.Integration.Polynomial.Rectangle

open Purelib.Integration.Polynomial.Rectangle.StitchedSideAreas

open Purelib.Riemann.Periods

open Purelib.Riemann.RootContinuation

public section

/-! Acquired common-basis sides read the observation perimeters on the existing shared cut bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.RequestedPerimeters

open Purelib

open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (surfaceMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest (BasisArcPreparations)
open Purelib.Riemann.Branches.NewtonSharedExteriorCuts (SharedExteriorCuts)
open Purelib.Riemann.Normalization
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve branches
    higher}
  {preparation : NewtonPreparation original} {target radius
    : Rational} {grid : NewtonGrid
    preparation target radius}
  {observations : ProtectedObservations original} {lifted :
    LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank lifted.frames
    grid.faces.regulars}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {partitions : SurfacePartitions observations grid} {preparations :
    BasisArcPreparations regular domains}

open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)
open Purelib.Integration.Polynomial.Rectangle.StitchedSideAreas (Entry)

open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest (Assemblies)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface (FaceAssembly)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly (Perimeters)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (FacePerimeterTraces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces (Centered)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas (seamValues)
variable {differential : Differential genus}
  {occurrence :
    PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}
  {initialDepth : Nat} {fixed : Preflights domains
    occurrence.sideOccurrence.sheet} {error : Rational}
  {stage : Nat} {cache : Numerics domains stage}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback.SharedPerimeter (values)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.PerimeterReadback.SharedPerimeter (bottom_original_area_seam
  right_original_area_seam top_original_area_seam left_original_area_seam)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)

variable (shared : SharedExteriorCuts partitions preparations)
  {wholeDepth : Nat} {wholeFixed : (sheet : Fin 2) →
    RegularMeshes.Preflights domains sheet}
  {wholeTarget : Rational}
  (wholeRequest : TwoSheetRequest
    (fun sheet => RegularMeshes.build domains
      shared.source.cuts sheet wholeDepth) wholeFixed wholeTarget)
  {request : SurfaceRequest partitions
    (Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface
      occurrence.sideOccurrence.sheet initialDepth) fixed error}

/-- The requested source mesh and observation whole-face mesh agree at the synchronized depth. -/
theorem common_mesh_eq_build (sameDepth : wholeRequest.depth = request.depth) :
    ((wholeRequest.entries.get occurrence.sideOccurrence.sheet).meshes.entries.get occurrence.sideOccurrence.position) =
      ((RegularMeshes.build domains shared.source.cuts occurrence.sideOccurrence.sheet request.depth).entries.get
        occurrence.sideOccurrence.position) := by
  rw [RegularMeshes.Request.mesh_eq, EnergyRequest.mesh_eq, wholeRequest.depth_eq, sameDepth]
  simp only [RegularMeshes.build, DependentVector.ofFn_get, -eq_self, -iff_self]

  rfl

variable (sameDepth : wholeRequest.depth = request.depth)
  {assemblies : Assemblies request cache
    coefficients} {perimeters : Perimeters assemblies}
  {observationTraces : FacePerimeterTraces request
    occurrence.sideOccurrence.position}
  (observed : Centered
    observationTraces cache coefficients)
  (face : FaceAssembly perimeters
    occurrence.sideOccurrence.position)
  (traces : PerimeterTraces
    ((wholeRequest.entries.get occurrence.sideOccurrence.sheet).meshes.entries.get occurrence.sideOccurrence.position))
  {wholeAssembly : ClippedAssembly
    ((wholeRequest.entries.get occurrence.sideOccurrence.sheet).meshes.entries.get occurrence.sideOccurrence.position)
    (Surface.SeamAreas.seamValues (sheet := occurrence.sideOccurrence.sheet) cache
      coefficients occurrence.sideOccurrence.position)}
  (wholePerimeter : wholeAssembly.Perimeter)

include sameDepth face wholePerimeter

/-- The acquired bottom side reads the observation boundary on the shared source bank. -/
theorem common_bottom_sample_eq
    (sample : Sample (SharedPerimeter.values (occurrence := occurrence) traces cache coefficients
      .bottom)) :
    sample.originalArea = observed.bottom.originalArea := by
  let equal := common_mesh_eq_build shared wholeRequest
    sameDepth
  let retained := ClippedPerimeterTransport.cast equal wholePerimeter
  have observation := NewtonSharedRequestedPerimeters.bottom_sample_eq_whole shared observed face retained
  have readback := ClippedPerimeterTransport.cast_entries equal wholePerimeter
  exact (SharedPerimeter.bottom_original_area_seam traces cache coefficients wholeAssembly wholePerimeter sample).trans
    ((congrArg Entry.area readback.1).symm.trans observation.symm)

/-- The acquired right side reads the observation boundary on the shared source bank. -/
theorem common_right_sample_eq
    (sample : Sample (SharedPerimeter.values (occurrence := occurrence) traces cache coefficients
      .right)) :
    sample.originalArea = observed.right.originalArea := by
  let equal := common_mesh_eq_build shared wholeRequest
    sameDepth
  let retained := ClippedPerimeterTransport.cast equal wholePerimeter
  have observation := NewtonSharedRequestedPerimeters.right_sample_eq_whole shared observed face retained
  have readback := ClippedPerimeterTransport.cast_entries equal wholePerimeter
  exact (SharedPerimeter.right_original_area_seam traces cache coefficients wholeAssembly wholePerimeter sample).trans
    ((congrArg Entry.area readback.2.1).symm.trans observation.symm)

/-- The acquired top side reads the observation boundary on the shared source bank. -/
theorem common_top_sample_eq
    (sample : Sample (SharedPerimeter.values (occurrence := occurrence) traces cache coefficients
      .top)) :
    sample.originalArea = observed.top.originalArea := by
  let equal := common_mesh_eq_build shared wholeRequest
    sameDepth
  let retained := ClippedPerimeterTransport.cast equal wholePerimeter
  have observation := NewtonSharedRequestedPerimeters.top_sample_eq_whole shared observed face retained
  have readback := ClippedPerimeterTransport.cast_entries equal wholePerimeter
  exact (SharedPerimeter.top_original_area_seam traces cache coefficients wholeAssembly wholePerimeter sample).trans
    ((congrArg Entry.area readback.2.2.1).symm.trans observation.symm)

/-- The acquired left side reads the observation boundary on the shared source bank. -/
theorem common_left_sample_eq
    (sample : Sample (SharedPerimeter.values (occurrence := occurrence) traces cache coefficients
      .left)) :
    sample.originalArea = observed.left.originalArea := by
  let equal := common_mesh_eq_build shared wholeRequest
    sameDepth
  let retained := ClippedPerimeterTransport.cast equal wholePerimeter
  have observation := NewtonSharedRequestedPerimeters.left_sample_eq_whole shared observed face retained
  have readback := ClippedPerimeterTransport.cast_entries equal wholePerimeter
  exact (SharedPerimeter.left_original_area_seam traces cache coefficients wholeAssembly wholePerimeter sample).trans
    ((congrArg Entry.area readback.2.2.2).symm.trans observation.symm)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.RequestedPerimeters
