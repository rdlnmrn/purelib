module
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.BilinearCombination
import Purelib.Topology.Polygon.Stokes
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Riemann.Readings.RectangularObservationAssembly

import Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly
public import Purelib.Integration.Polynomial.Rectangle.ClippedCornerCombination
import Purelib.Integration.Polynomial.Rectangle.ClippedBoundaryCombination
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Readings.RectangularObservationOwners
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rational.Box.Basic

public section

/-! Exact coefficient expansion of the stitched exterior, including all
joining edges between the retained primitive owners. -/
section

open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian)
open Purelib.Riemann.Periods.BilinearCombination (edgeArea_combination sumFin_combination)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

variable {columns rows leftCount rightCount : Nat} {geometry : Geometry columns rows}
  {cuts : GridCuts geometry} {box : Box}

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

open Purelib.Algebra in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.Meshes in
/-- The exact mesh's exterior side sum distributes over the original left and right coefficient families.

Each retained side sum keeps its model-owner indices and subdivision depth. Finite sum interchange retains every ordered
weighted coefficient pair. -/
theorem exteriorSides_combination (mesh :
  ObservationMesh cuts box)
    (left : Fin leftCount → Gaussian) (right : Fin rightCount → Gaussian)
    (first : Fin leftCount → Fin (columns + 1) → Fin (rows + 1) → Gaussian → Gaussian)
    (second : Fin rightCount → Fin (columns + 1) → Fin (rows + 1) → Gaussian → Gaussian) :
    Boundary.Assembly.exteriorSides (mesh.sideGrid (fun column row point =>
      ⟨sumFin (fun i => left i * first i column row point),
        FiniteSum.Fin.sumFin (fun j => right j * second j column row point)⟩)) =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => left i * right j *
        Boundary.Assembly.exteriorSides (mesh.sideGrid
          (fun column row point => ⟨first i column row point, second j column row point⟩)))) := by
  simp only [Boundary.Assembly.exteriorSides, RectangularObservationMesh.ObservationMesh.sideGrid,
    RectangularObservationMesh.ObservationMesh.cellSides,
    PreparedBoxBoundary.horizontalBoundary_combination, PreparedBoxBoundary.verticalBoundary_combination,
    mul_add, mul_sub, FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_sub]
  simp only [sumFin_combination, -eq_self, -iff_self]
  rfl

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Riemann.Meshes in
open Purelib.Riemann.Periods in
/-- The exact mesh's exterior corner-joining areas distribute over the original coefficient pairs.

The corner readbacks retain both endpoint owners of each joining chord. Bilinearity expands that same ordered endpoint
pair. -/
theorem exteriorJoins_combination (mesh :
  ObservationMesh cuts box)
    (left : Fin leftCount → Gaussian) (right : Fin rightCount → Gaussian)
    (first : Fin leftCount → Fin (columns + 1) → Fin (rows + 1) → Gaussian → Gaussian)
    (second : Fin rightCount → Fin (columns + 1) → Fin (rows + 1) → Gaussian → Gaussian) :
    BilinearGridBoundary.exteriorJoins (mesh.cornerValues (fun column row point =>
      ⟨sumFin (fun i => left i * first i column row point),
        FiniteSum.Fin.sumFin (fun j => right j * second j column row point)⟩)) =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => left i * right j *
        BilinearGridBoundary.exteriorJoins (mesh.cornerValues
          (fun column row point => ⟨first i column row point, second j column row point⟩)))) := by
  simp only [BilinearGridBoundary.exteriorJoins, RectangularObservationMesh.ObservationMesh.cornerValues,
    Vector.Basic.vectorOfFn_apply, RectangularObservationMesh.ObservationMesh.cornerGrid,
    edgeArea_combination, mul_add, mul_sub, FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_sub]
  simp only [sumFin_combination, -eq_self, -iff_self]
  rfl

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

section ClippedAssembly

variable {mesh : ObservationMesh cuts box}

namespace Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly

open Purelib.Data in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.Meshes in
open Purelib.Riemann.Periods in
/-- The retained assembly exterior equals the original mesh's exterior sides plus exterior corner joins.

The side and corner cache equations specialize at each original finite position. Their scalar contributions recover the
retained exterior reading. -/
theorem
  exterior_eq_values
    {values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint}
    (assembly : ClippedAssembly mesh values) :
    assembly.exterior = Boundary.Assembly.exteriorSides (mesh.sideGrid values) +
      BilinearGridBoundary.exteriorJoins (mesh.cornerValues values) := by
  rw [assembly.exterior_eq]
  conv_lhs => simp only [Boundary.Assembly.exteriorSides, BilinearGridBoundary.exteriorJoins,
    assembly.sides_eq, assembly.corners_eq, RectangularObservationMesh.ObservationMesh.cornerValues,
      Vector.Basic.vectorOfFn_apply]
  conv_rhs => simp only [Boundary.Assembly.exteriorSides, BilinearGridBoundary.exteriorJoins,
    assembly.sides_eq, assembly.corners_eq, RectangularObservationMesh.ObservationMesh.cornerValues,
      Vector.Basic.vectorOfFn_apply]

open Purelib.Algebra in
/-- The retained local-minus-exterior residual is the double weighted sum of the corresponding pair-assembly residuals.

Every pair assembly is indexed by the same original mesh and its own original paired values. -/
theorem
  local_sub_exterior_combination
    (left : Fin leftCount → Gaussian) (right : Fin rightCount → Gaussian)
    (first : Fin leftCount → Fin (columns + 1) → Fin (rows + 1) → Gaussian → Gaussian)
    (second : Fin rightCount → Fin (columns + 1) → Fin (rows + 1) → Gaussian → Gaussian)
    (assembly : ClippedAssembly mesh (fun column row point =>
      ⟨sumFin (fun i => left i * first i column row point),
        FiniteSum.Fin.sumFin (fun j => right j * second j column row point)⟩))
    (pairs : (i : Fin leftCount) → (j : Fin rightCount) → ClippedAssembly mesh
      (fun column row point => ⟨first i column row point, second j column row point⟩)) :
    assembly.localTotal - assembly.exterior =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => left i * right j * ((pairs i j).localTotal - (pairs
        i j).exterior))) := by
  rw [assembly.localTotal_eq, assembly.exterior_eq_values, mesh.pieces.localBoundary_combination,
    mesh.exteriorSides_combination, mesh.exteriorJoins_combination]
  conv_lhs => simp only [(pairs _ _).localTotal_eq, (pairs _ _).exterior_eq_values, mul_sub, mul_add,
    FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_add, -eq_self, -iff_self]
  conv_rhs => simp only [(pairs _ _).localTotal_eq, (pairs _ _).exterior_eq_values, mul_sub, mul_add,
    FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_add, -eq_self, -iff_self]

end Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly

end ClippedAssembly
end

end
