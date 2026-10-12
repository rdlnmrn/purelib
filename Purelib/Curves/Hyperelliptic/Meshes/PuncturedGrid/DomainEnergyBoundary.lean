module
import Purelib.Data.List.Flatten
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.Polygon

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBilinearBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rectangle.Partition.PreparedPartitionBoundary
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Topology.Mesh.CoordinateTriangulation

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-!
# Conjugate/value energy on the actual rectangular boundary

Read the boundary of a retained affine energy sample through its shared
basis values. Finite Stokes cancels interior triangulation edges and the
rectangular partition cancels its internal sides. The exterior retains all
model cuts and spatial subdivision; no endpoint-chord replacement is made.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyBoundary

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : Meshes.PuncturedGridFaces.RegularFace bank}
      {models
    : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face} {sheet : Fin 2}
  {domain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet} {stage : Nat}
  {cached : (row : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives domain
    (Periods.PeriodMatrix.standardDifferential row) stage}
  {triangles : List (Integration.RectangularOwnedTriangulation.ModelTriangle domain.geometry)} {surface :
    Integration.RectangularOwnedTriangulation.OwnedTriangulation triangles}

/-- The retained energy-sample boundary area equals the sum of its original coordinate-triangle wedges. -/
theorem energy_boundary_eq_wedges (readings : Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy.BasisReadings cached
  surface)
    (budget : Readings.AffineBasisEnergy.AffineBasis.SurfaceBudget readings.affine) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    (budget.sample coefficients).boundaryArea =
      Rectangle.Partition.PreparedBoxBoundary.sumCoordinateWedges (fun point => Energy.Polygon.energyPrimitivePoint
        (readings.atPoint coefficients point))
        (triangles.map Integration.RectangularOwnedTriangulation.ModelTriangle.triangle) := open Purelib.Algebra in by
  rw [(budget.sample coefficients).boundaryArea_eq]
  change Topology.Polygon.Stokes.edgeListArea
    (fun vertex => Energy.Polygon.energyPrimitivePoint ((budget.sample coefficients).primitiveValue vertex))
    surface.mesh.triangulation.boundary = _
  rw [← surface.mesh.wedgeSum_eq_boundaryArea, Rectangle.Partition.PreparedBoxBoundary.sumCoordinateWedges_eq_sumFin]
  apply FiniteSum.Fin.sumFin_congr
  intro face
  have coordinates := surface.mesh.face_coordinates face
  change Topology.Polygon.Stokes.triangleWedgeArea
    (Energy.Polygon.energyPrimitivePoint ((budget.sample coefficients).primitiveValue (surface.mesh.triangulation.faces
      face).first))
    (Energy.Polygon.energyPrimitivePoint ((budget.sample coefficients).primitiveValue (surface.mesh.triangulation.faces
      face).second))
    (Energy.Polygon.energyPrimitivePoint ((budget.sample coefficients).primitiveValue (surface.mesh.triangulation.faces
      face).third)) = _
  rw [budget.sample_value, budget.sample_value, budget.sample_value,
    ← readings.atPoint_coordinate, ← readings.atPoint_coordinate, ← readings.atPoint_coordinate,
    coordinates.1, coordinates.2.1, coordinates.2.2]
  rfl

/-- The retained energy boundary equals the sum of the complete original rectangle boundaries. -/
theorem energy_boundary_eq_boxes {box : Rational.Box} {mesh :
  Meshes.RectangularObservationMesh.ObservationMesh domain.cuts box}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy.BasisReadings cached mesh.surface) (budget :
      Readings.AffineBasisEnergy.AffineBasis.SurfaceBudget readings.affine)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    (budget.sample coefficients).boundaryArea = Rectangle.Partition.PreparedBoxBoundary.sumBoxBoundaries
      (fun point => Energy.Polygon.energyPrimitivePoint (readings.atPoint coefficients point)) mesh.boxes := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyBoundary.energy_boundary_eq_wedges readings budget coefficients,
    mesh.coordinates, Rectangle.Partition.PreparedBoxBoundary.sumCoordinateWedges_boxTriangles]

/-- Summing all original refined rectangle boundaries equals the sum of the retained dyadic boundary traces. -/
private theorem refined_boundaries (primitive : Gaussian.Basic.Canonical →
  Purelib.Topology.Polygon.Stokes.PrimitivePoint) (depth : Nat) (boxes : List Rational.Box) :
    Rectangle.Partition.PreparedBoxBoundary.sumBoxBoundaries primitive
      (boxes.flatMap (Rectangle.Partition.PreparedBoxPartitions.cells depth)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (boxes.map
        (Rectangle.Partition.PreparedBoxBoundary.rectangleBoundary primitive depth)) := by
  induction boxes with
  | nil => rfl
  | cons box boxes ih =>
      rw [List.Flatten.flatMap_cons, Rectangle.Partition.PreparedBoxBoundary.sumBoxBoundaries_append,
        Rectangle.Partition.PreparedBoxBoundary.sumBoxBoundaries_cells, ih]
      rfl

/-- The original energy-sample boundary equals the complete retained exterior partition trace at its actual depth. -/
theorem energy_boundary_eq_exterior {box : Rational.Box} {mesh :
  Meshes.RectangularObservationMesh.ObservationMesh domain.cuts box}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy.BasisReadings cached mesh.surface) (budget :
      Readings.AffineBasisEnergy.AffineBasis.SurfaceBudget readings.affine)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    (budget.sample coefficients).boundaryArea = mesh.partition.boundary
      (fun point => Energy.Polygon.energyPrimitivePoint (readings.atPoint coefficients point)) mesh.depth := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyBoundary.energy_boundary_eq_boxes readings budget coefficients,
    mesh.boxes_eq, Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyBoundary.refined_boundaries,
    mesh.partition.boundary_eq_sum]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyBoundary
