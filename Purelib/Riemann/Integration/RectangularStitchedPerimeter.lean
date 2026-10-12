module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Riemann.Periods.BilinearGridBoundary

import Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly
public import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Tactic.Ring

public section

/-! Four forward perimeter traces, assembled from the existing side and corner
caches. Top and left are reversed in the oriented exterior. -/
namespace Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly

open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)

variable {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry} {box : Box}
  {mesh : ObservationMesh cuts box}
  {values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint}

open Purelib.Algebra in
set_option genInjectivity false in
/-- The four cached stitched perimeter sides of an exact clipped observation assembly.

Each side retains its original side sums and adjacent-corner join contributions, with the common
bottom-plus-right-minus-top-minus-left orientation. -/
structure Perimeter
  (assembly : ClippedAssembly mesh values) where
  /-- The cached stitched bottom boundary value. -/ bottom : Gaussian
  /-- The bottom cache equals its original side sum and exact horizontal corner joins. -/ bottom_eq : bottom =
    FiniteSum.Fin.sumFin (fun column => (assembly.sides column 0).bottom) +
    FiniteSum.Fin.sumFin (fun column : Fin mesh.boundaryColumns =>
      edgeArea (assembly.corners column.castSucc 0).lowerRight (assembly.corners column.succ 0).lowerLeft)
  /-- The cached stitched right boundary value. -/ right : Gaussian
  /-- The right cache equals its original side sum and exact vertical corner joins. -/ right_eq : right =
    FiniteSum.Fin.sumFin (fun row => (assembly.sides (Fin.last mesh.boundaryColumns) row).right) +
    FiniteSum.Fin.sumFin (fun row : Fin mesh.boundaryRows =>
      edgeArea (assembly.corners (Fin.last mesh.boundaryColumns) row.castSucc).upperRight
        (assembly.corners (Fin.last mesh.boundaryColumns) row.succ).lowerRight)
  /-- The cached stitched top boundary value. -/ top : Gaussian
  /-- The top cache equals its original side sum and exact horizontal corner joins. -/ top_eq : top =
    FiniteSum.Fin.sumFin (fun column => (assembly.sides column (Fin.last mesh.boundaryRows)).top) +
    FiniteSum.Fin.sumFin (fun column : Fin mesh.boundaryColumns =>
      edgeArea (assembly.corners column.castSucc (Fin.last mesh.boundaryRows)).upperRight
        (assembly.corners column.succ (Fin.last mesh.boundaryRows)).upperLeft)
  /-- The cached stitched left boundary value. -/ left : Gaussian
  /-- The left cache equals its original side sum and exact vertical corner joins. -/ left_eq : left =
    FiniteSum.Fin.sumFin (fun row => (assembly.sides 0 row).left) +
    FiniteSum.Fin.sumFin (fun row : Fin mesh.boundaryRows =>
      edgeArea (assembly.corners 0 row.castSucc).upperLeft (assembly.corners 0 row.succ).lowerLeft)

constructive_injectivity
  Perimeter

open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly (Perimeter)

namespace Perimeter

variable {assembly : ClippedAssembly mesh values}

open Purelib.Algebra in
/-- Cache all four stitched perimeter sides from the exact retained assembly grids.

Each side combines its original side sums and neighboring corner chords. The four cached equalities preserve their mesh
indices and oriented endpoints. -/
@[expose] def
  build
  (assembly : ClippedAssembly mesh values) : Perimeter assembly :=
  ⟨sumFin (fun column => (assembly.sides column 0).bottom) +
      FiniteSum.Fin.sumFin (fun column : Fin mesh.boundaryColumns =>
        edgeArea (assembly.corners column.castSucc 0).lowerRight (assembly.corners column.succ 0).lowerLeft), rfl,
    FiniteSum.Fin.sumFin (fun row => (assembly.sides (Fin.last mesh.boundaryColumns) row).right) +
      FiniteSum.Fin.sumFin (fun row : Fin mesh.boundaryRows =>
        edgeArea (assembly.corners (Fin.last mesh.boundaryColumns) row.castSucc).upperRight
          (assembly.corners (Fin.last mesh.boundaryColumns) row.succ).lowerRight), rfl,
    FiniteSum.Fin.sumFin (fun column => (assembly.sides column (Fin.last mesh.boundaryRows)).top) +
      FiniteSum.Fin.sumFin (fun column : Fin mesh.boundaryColumns =>
        edgeArea (assembly.corners column.castSucc (Fin.last mesh.boundaryRows)).upperRight
          (assembly.corners column.succ (Fin.last mesh.boundaryRows)).upperLeft), rfl,
    FiniteSum.Fin.sumFin (fun row => (assembly.sides 0 row).left) +
      FiniteSum.Fin.sumFin (fun row : Fin mesh.boundaryRows =>
        edgeArea (assembly.corners 0 row.castSucc).upperLeft (assembly.corners 0 row.succ).lowerLeft), rfl⟩

open Purelib.Algebra in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.Periods in
/-- The original assembly exterior equals the signed sum of its four retained stitched perimeter sides.

The side words retain their exact starts, finishes and joining chords. Their signed readings recover the assembly
exterior without changing its mesh owners. -/
theorem
  exterior_eq
  (perimeter : Perimeter assembly) :
    assembly.exterior = perimeter.bottom + perimeter.right - perimeter.top - perimeter.left := by
  rw [assembly.exterior_eq, perimeter.bottom_eq, perimeter.right_eq, perimeter.top_eq, perimeter.left_eq]
  unfold Boundary.Assembly.exteriorSides BilinearGridBoundary.exteriorJoins
  have horizontal := FiniteSum.Fin.sumFin_congr (fun column : Fin mesh.boundaryColumns => show
    edgeArea (assembly.corners column.succ (Fin.last mesh.boundaryRows)).upperLeft
        (assembly.corners column.castSucc (Fin.last mesh.boundaryRows)).upperRight -
      edgeArea (assembly.corners column.succ 0).lowerLeft (assembly.corners column.castSucc 0).lowerRight =
      edgeArea (assembly.corners column.castSucc 0).lowerRight (assembly.corners column.succ 0).lowerLeft -
        edgeArea (assembly.corners column.castSucc (Fin.last mesh.boundaryRows)).upperRight
          (assembly.corners column.succ (Fin.last mesh.boundaryRows)).upperLeft by
    simp only [edgeArea]
    ring1)
  rw [horizontal]
  simp only [FiniteSum.Fin.sumFin_sub]
  ring1

end Perimeter
end Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly

end
