module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBilinearRequest
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
public import Purelib.Geometry.Rectangle.Partition.PreparedPartitionBoundary

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Data.List.Flatten

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rectangle.Partition

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Integration.RectangularOwnedTriangulation

open Purelib.Riemann.Meshes

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.RectangularPrimitiveBoundary

open Purelib.Topology.Polygon

@[expose] public section

/-! The actual two-function boundary on a refining domain mesh, expressed
on its coordinate polygons. Subdivided boundary paths are retained. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedTriangulation ModelTriangle)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy (BasisReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds (EnergyPreflight)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest (EnergyRequest)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeListArea triangleWedgeArea)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    Purelib.Riemann.Meshes.PuncturedGridFaces.RegularFace bank} {models :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face} {sheet :
    Fin 2}
  {domain : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet} {stage : Nat}
  {cached : (row : Fin genus) → Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives
    domain (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential row) stage}
  {triangles : List (Purelib.Riemann.Integration.RectangularOwnedTriangulation.ModelTriangle domain.geometry)} {surface
    : Purelib.Riemann.Integration.RectangularOwnedTriangulation.OwnedTriangulation triangles}

/-- Read the supplied coefficient combination of the actual cached basis primitive values at one coordinate point. -/
def DomainBasisEnergy.BasisReadings.atPoint
    (readings : DomainBasisEnergy.BasisReadings cached surface) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (point : Data.Gaussian.Basic.Canonical) : Gaussian :=
  FiniteSum.Fin.sumFin (fun row => coefficients row *
    SharedPrimitiveValues.atPoint (readings.rows.get row) point)

/-- At an actual retained mesh vertex, the coordinate reading equals the original affine basis combination. -/
theorem DomainBasisEnergy.BasisReadings.atPoint_coordinate
    (readings : DomainBasisEnergy.BasisReadings cached surface)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (vertex : Fin surface.mesh.vertices.length) :
    readings.atPoint coefficients (surface.mesh.coordinate vertex) = readings.affine.value coefficients vertex := by
  apply FiniteSum.Fin.sumFin_congr
  intro row
  rw [SharedPrimitiveValues.atPoint_coordinate, readings.values_eq]

/-- The actual two-row mesh boundary area equals the sum of coordinate wedge areas of its original retained triangles.
-/
theorem
  DomainBasisEnergy.BasisReadings.bilinear_boundary_eq_wedges
    (readings : DomainBasisEnergy.BasisReadings cached surface)
    (left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Stokes.edgeListArea (fun vertex => ⟨readings.affine.value left vertex, readings.affine.value right vertex⟩)
      surface.mesh.triangulation.boundary =
      PreparedBoxBoundary.sumCoordinateWedges
        (fun point => ⟨readings.atPoint left point, readings.atPoint right point⟩)
        (triangles.map ModelTriangle.triangle) := by
  rw [← surface.mesh.triangulation.wedgeSum_eq_boundaryArea, PreparedBoxBoundary.sumCoordinateWedges_eq_sumFin]
  apply FiniteSum.Fin.sumFin_congr
  intro face
  have coordinates := surface.mesh.face_coordinates face
  change Stokes.triangleWedgeArea
    ⟨readings.affine.value left (surface.mesh.triangulation.faces face).first,
      readings.affine.value right (surface.mesh.triangulation.faces face).first⟩
    ⟨readings.affine.value left (surface.mesh.triangulation.faces face).second,
      readings.affine.value right (surface.mesh.triangulation.faces face).second⟩
    ⟨readings.affine.value left (surface.mesh.triangulation.faces face).third,
      readings.affine.value right (surface.mesh.triangulation.faces face).third⟩ = _
  rw [← readings.atPoint_coordinate left, ← readings.atPoint_coordinate right,
    ← readings.atPoint_coordinate left, ← readings.atPoint_coordinate right,
    ← readings.atPoint_coordinate left, ← readings.atPoint_coordinate right,
    coordinates.1, coordinates.2.1, coordinates.2.2]
  rfl

/-- The actual two-row observation-mesh boundary equals the complete coordinate boundary sum of its retained boxes. -/
theorem
  DomainBasisEnergy.BasisReadings.bilinear_boundary_eq_boxes
    {box : Rational.Box} {mesh : RectangularObservationMesh.ObservationMesh domain.cuts box}
    (readings : DomainBasisEnergy.BasisReadings cached mesh.surface) (left right :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Stokes.edgeListArea (fun vertex => ⟨readings.affine.value left vertex, readings.affine.value right vertex⟩)
      mesh.surface.mesh.triangulation.boundary =
      PreparedBoxBoundary.sumBoxBoundaries
        (fun point => ⟨readings.atPoint left point, readings.atPoint right point⟩) mesh.boxes := by
  rw [readings.bilinear_boundary_eq_wedges, mesh.coordinates,
    PreparedBoxBoundary.sumCoordinateWedges_boxTriangles]

/-- Summing all actual refined-cell boundaries gives the sum of the original boxes' retained subdivided rectangle
boundaries. -/
private theorem DomainBilinearBoundary.refined_boundaries (primitive : Data.Gaussian.Basic.Canonical →
  Stokes.PrimitivePoint) (depth : Nat)
  (boxes : List Rational.Box) :
    PreparedBoxBoundary.sumBoxBoundaries primitive (boxes.flatMap (PreparedBoxPartitions.cells depth)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (boxes.map (PreparedBoxBoundary.rectangleBoundary primitive depth))
        := by
  induction boxes with
  | nil => rfl
  | cons box boxes ih =>
      rw [Data.List.Flatten.flatMap_cons, PreparedBoxBoundary.sumBoxBoundaries_append,
        PreparedBoxBoundary.sumBoxBoundaries_cells, ih]
      rfl

/-- The actual two-row observation boundary is the sum of the retained coarse partition boxes at their original
refinement depth. -/
theorem
  DomainBasisEnergy.BasisReadings.bilinear_boundary_eq_partition
    {box : Rational.Box} {mesh : RectangularObservationMesh.ObservationMesh domain.cuts box}
    (readings : DomainBasisEnergy.BasisReadings cached mesh.surface) (left right :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Stokes.edgeListArea (fun vertex => ⟨readings.affine.value left vertex, readings.affine.value right vertex⟩)
      mesh.surface.mesh.triangulation.boundary =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (mesh.partition.boxes.map
        (PreparedBoxBoundary.rectangleBoundary
          (fun point => ⟨readings.atPoint left point, readings.atPoint right point⟩) mesh.depth)) := by
  rw [readings.bilinear_boundary_eq_boxes, mesh.boxes_eq,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBilinearBoundary.refined_boundaries]

/-- The actual two-row mesh boundary reads exactly the retained partition's exterior boundary at its original depth. -/
theorem
  DomainBasisEnergy.BasisReadings.bilinear_boundary_eq_exterior
    {box : Rational.Box} {mesh : RectangularObservationMesh.ObservationMesh domain.cuts box}
    (readings : DomainBasisEnergy.BasisReadings cached mesh.surface) (left right :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Stokes.edgeListArea (fun vertex => ⟨readings.affine.value left vertex, readings.affine.value right vertex⟩)
      mesh.surface.mesh.triangulation.boundary =
      mesh.partition.boundary (fun point => ⟨readings.atPoint left point, readings.atPoint right point⟩) mesh.depth :=
        by
  rw [readings.bilinear_boundary_eq_partition, mesh.partition.boundary_eq_sum]

/-- The complete actual two-row box boundary satisfies the paid energy target scaled by both original coefficient
squared norms. -/
theorem DomainBilinearBoundary.bilinear_boxes_bound {box : Rational.Box} {preflight :
  DomainBasisBounds.EnergyPreflight domain}
    {coarse : RectangularObservationMesh.ObservationMesh domain.cuts box} {target : Fraction.Rational}
    (request : DomainEnergyRequest.EnergyRequest preflight coarse target) (stage_eq : stage =
      request.modelRequest.index)
    (readings : DomainBasisEnergy.BasisReadings cached request.mesh.surface) (left right :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus)
      :
    Data.Gaussian.Norm.Basic.normSq (PreparedBoxBoundary.sumBoxBoundaries
      (fun point => ⟨readings.atPoint left point, readings.atPoint right point⟩) request.mesh.boxes) ≤
      PreparedObservationCoercivity.coefficientNormSq left * PreparedObservationCoercivity.coefficientNormSq right *
        (64 * target ^ 2) := by
  rw [← readings.bilinear_boundary_eq_boxes]
  exact request.bilinear_bound stage_eq readings left right

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
