module
import Purelib.Algebra.FiniteSum.Fin

import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.BilinearCombination
import Purelib.Riemann.Readings.RectangularObservationAssembly
public import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Integration.Polynomial.Rectangle.ClippedBoundaryCombination
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Topology.Polygon.Stokes
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Riemann.Readings.RectangularObservationOwners
import Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid

@[expose] public section

/-! Coefficient expansion of each retained perimeter side, including its
owner-junction chords. This keeps the physical component selection intact. -/

namespace Purelib.Integration.Polynomial.Rectangle.ClippedPerimeterCombination

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add)
attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr
variable {columns rows leftCount rightCount : Nat} {geometry :
  Purelib.Riemann.Normalization.RectangularInverseModels.Geometry columns rows}
  {cuts : Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts geometry} {box :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Box} {mesh :
    Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh cuts box}
  (left : Fin leftCount → Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian) (right : Fin rightCount →
    Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian)
  (first : Fin leftCount → Fin (columns + 1) → Fin (rows + 1) →
    Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian →
    Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian)
  (second : Fin rightCount → Fin (columns + 1) → Fin (rows + 1) →
    Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian →
    Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian)
  {assembly : Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly mesh (fun column
    row point =>
    ⟨sumFin (fun i => left i * first i column row point),
      Purelib.Algebra.FiniteSum.Fin.sumFin (fun j => right j * second j column row point)⟩)}
  (perimeter : assembly.Perimeter)
  {pairs : (i : Fin leftCount) → (j : Fin rightCount) →
    Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly mesh
    (fun column row point => ⟨first i column row point, second j column row point⟩)}
  (perimeters : (i : Fin leftCount) → (j : Fin rightCount) → (pairs i j).Perimeter)

section
open Purelib.Algebra
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Meshes
open Purelib.Riemann.Periods
/-- The retained stitched bottom perimeter area is the double weighted sum of the original pair perimeters' bottom
areas. -/
theorem bottom_combination :
    perimeter.bottom = FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => left i * right j * (perimeters i
      j).bottom)) := by
  rw [perimeter.bottom_eq]
  simp only [(perimeters _ _).bottom_eq, assembly.sides_eq, assembly.corners_eq,
    (pairs _ _).sides_eq, (pairs _ _).corners_eq, RectangularObservationMesh.ObservationMesh.sideGrid,
      RectangularObservationMesh.ObservationMesh.cellSides, RectangularObservationMesh.ObservationMesh.cornerGrid,
    PreparedBoxBoundary.horizontalBoundary_combination,
    BilinearCombination.edgeArea_combination, mul_add, FiniteSum.Fin.sumFin_add]
  rw [BilinearCombination.sumFin_combination, BilinearCombination.sumFin_combination]

/-- The retained stitched right perimeter area is the double weighted sum of the original pair perimeters' right areas.
-/
theorem right_combination :
    perimeter.right = FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => left i * right j * (perimeters i
      j).right)) := by
  rw [perimeter.right_eq]
  simp only [(perimeters _ _).right_eq, assembly.sides_eq, assembly.corners_eq,
    (pairs _ _).sides_eq, (pairs _ _).corners_eq, RectangularObservationMesh.ObservationMesh.sideGrid,
      RectangularObservationMesh.ObservationMesh.cellSides, RectangularObservationMesh.ObservationMesh.cornerGrid,
    PreparedBoxBoundary.verticalBoundary_combination,
    BilinearCombination.edgeArea_combination, mul_add, FiniteSum.Fin.sumFin_add]
  rw [BilinearCombination.sumFin_combination, BilinearCombination.sumFin_combination]

/-- The retained stitched top perimeter area is the double weighted sum of the original pair perimeters' top areas. -/
theorem top_combination :
    perimeter.top = FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => left i * right j * (perimeters i
      j).top)) := by
  rw [perimeter.top_eq]
  simp only [(perimeters _ _).top_eq, assembly.sides_eq, assembly.corners_eq,
    (pairs _ _).sides_eq, (pairs _ _).corners_eq, RectangularObservationMesh.ObservationMesh.sideGrid,
      RectangularObservationMesh.ObservationMesh.cellSides, RectangularObservationMesh.ObservationMesh.cornerGrid,
    PreparedBoxBoundary.horizontalBoundary_combination,
    BilinearCombination.edgeArea_combination, mul_add, FiniteSum.Fin.sumFin_add]
  rw [BilinearCombination.sumFin_combination, BilinearCombination.sumFin_combination]

/-- The retained stitched left perimeter area is the double weighted sum of the original pair perimeters' left areas. -/
theorem left_combination :
    perimeter.left = FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => left i * right j * (perimeters i
      j).left)) := by
  rw [perimeter.left_eq]
  simp only [(perimeters _ _).left_eq, assembly.sides_eq, assembly.corners_eq,
    (pairs _ _).sides_eq, (pairs _ _).corners_eq, RectangularObservationMesh.ObservationMesh.sideGrid,
      RectangularObservationMesh.ObservationMesh.cellSides, RectangularObservationMesh.ObservationMesh.cornerGrid,
    PreparedBoxBoundary.verticalBoundary_combination,
    BilinearCombination.edgeArea_combination, mul_add, FiniteSum.Fin.sumFin_add]
  rw [BilinearCombination.sumFin_combination, BilinearCombination.sumFin_combination]

end

end Purelib.Integration.Polynomial.Rectangle.ClippedPerimeterCombination
