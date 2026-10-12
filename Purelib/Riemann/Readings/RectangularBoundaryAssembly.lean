module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Integration.Energy.Polygon
import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Polynomial.Rectangle.Boundary.Corners
import Purelib.LinearAlgebra.Grid.Offsets
public import Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly
public import Purelib.Riemann.Integration.RectangularPrimitiveCorners
public import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Normalization.InverseRootPolynomial

@[expose] public section

/-!
# Actual local primitive mesh boundaries assembled across a regular grid

Each coarse cell uses its own primitive on all its fine triangles.  Fine
diagonals cancel inside that cell before the coarse seam errors are paid.
The stitched exterior, corrected seams, and corner terms are cached and
connected by an exact identity.  This avoids charging a fixed ownership
mismatch separately to every fine triangle.
-/

namespace Purelib.Riemann.Readings.RectangularBoundaryAssembly

open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier of the boundary assembly. -/
private abbrev Gaussian := Basic.Canonical
open Purelib.Polynomial.Dense.Gaussian in
/-- The original dense Gaussian numerator polynomial carrier. -/
private abbrev Polynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveCorners (AlignedCorners)
/-- The finite vector carrier of the cached rectangular grid data. -/
private abbrev Vector := Data.Vector

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary (horizontalBoundary verticalBoundary rectangleBoundary)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (line_zero line_one)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions (cells)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

open Purelib in
open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Energy in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- Cached local and exterior primitive boundaries with their exact seam corrections.

The original aligned corners, grid owners and dyadic depth index the cached side traces, horizontal and vertical
corrections, and total decomposition readbacks. -/
structure BoundaryAssembly {polynomial numerator :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {columns rows : Nat} {geometry : Geometry
  columns rows}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator}
    (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges) (depth : Nat)
      where
  /-- The original aligned corner values and their exact joins. -/ corners : AlignedCorners anchors offsets
  /-- The cached four-side primitive traces at each original grid position. -/ sides : Data.Vector
    (Data.Vector Boundary.Assembly.Sides (rows + 1)) (columns + 1)
  /-- The cached bottom side reads the original horizontal primitive boundary. -/ bottom_eq : ∀ column row, (sides
    column row).bottom = PreparedBoxBoundary.horizontalBoundary
    (fun point => Polygon.energyPrimitivePoint (anchors.alignedValue offsets column row point)) depth
      (geometry.x.coordinates column.castSucc) (geometry.x.coordinates column.succ) (geometry.y.coordinates
        row.castSucc)
  /-- The cached right side reads the original vertical primitive boundary. -/ right_eq : ∀ column row, (sides column
    row).right = PreparedBoxBoundary.verticalBoundary
    (fun point => Polygon.energyPrimitivePoint (anchors.alignedValue offsets column row point)) depth
      (geometry.y.coordinates row.castSucc) (geometry.y.coordinates row.succ) (geometry.x.coordinates column.succ)
  /-- The cached top side reads the original horizontal primitive boundary. -/ top_eq : ∀ column row, (sides column
    row).top = PreparedBoxBoundary.horizontalBoundary
    (fun point => Polygon.energyPrimitivePoint (anchors.alignedValue offsets column row point)) depth
      (geometry.x.coordinates column.castSucc) (geometry.x.coordinates column.succ) (geometry.y.coordinates row.succ)
  /-- The cached left side reads the original vertical primitive boundary. -/ left_eq : ∀ column row, (sides column
    row).left = PreparedBoxBoundary.verticalBoundary
    (fun point => Polygon.energyPrimitivePoint (anchors.alignedValue offsets column row point)) depth
      (geometry.y.coordinates row.castSucc) (geometry.y.coordinates row.succ) (geometry.x.coordinates column.castSucc)
  /-- The cached sum of the original local side boundaries. -/ localTotal : Basic.Canonical
  /-- The local total reads back the exact side-assembly sum. -/ localTotal_eq : localTotal =
    Boundary.Assembly.localBoundary (fun column row => sides column row)
  /-- The cached original exterior sides and corner joins. -/ exterior : Basic.Canonical
  /-- The exterior reads back the exact exterior-side sum plus original corner joins. -/ exterior_eq : exterior =
    Boundary.Assembly.exteriorSides (fun column row => sides column row) + corners.exteriorJoins
  /-- The cached corrections along the original horizontal adjacency indices. -/ horizontalCorrections :
    Data.Vector (Data.Vector Basic.Canonical (rows + 1)) columns
  /-- Each cached correction equals the original horizontal seam minus its endpoint term. -/ horizontalCorrections_eq :
    ∀ column row, horizontalCorrections column row =
    Boundary.Assembly.horizontalSeam (fun column row => sides column row) column row -
      Boundary.Corners.horizontalEndpoint corners.values column row
  /-- The cached corrections along the original vertical adjacency indices. -/ verticalCorrections : Data.Vector
    (Data.Vector Basic.Canonical rows) (columns + 1)
  /-- Each cached correction equals the original vertical seam minus its endpoint term. -/ verticalCorrections_eq : ∀
    column row, verticalCorrections column row =
    Boundary.Assembly.verticalSeam (fun column row => sides column row) column row - Boundary.Corners.verticalEndpoint
      corners.values column row
  /-- The cached sum of all retained seam corrections. -/ seamTotal : Basic.Canonical
  /-- The seam total is exactly the corrected seam sum of the original side assembly. -/ seamTotal_eq : seamTotal =
    Boundary.Assembly.correctedSeamSum (fun column row => sides column row) corners.values

constructive_injectivity BoundaryAssembly

namespace BoundaryAssembly

variable {polynomial numerator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {columns
  rows : Nat} {geometry
  : Geometry columns rows}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator}
    {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges} {depth
      : Nat}

open Purelib in
open Purelib.Algebra in
open Purelib.Data in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Energy in
open Purelib.Integration.Polynomial.Rectangle in
/-- Cache the original rectangular side traces and their seam corrections.

The assembly retains the original aligned corners and depth, computes each correction once, and records exact finite-sum
readbacks for the resulting local, exterior and seam totals. -/
def build (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges) (depth :
  Nat) :
    BoundaryAssembly anchors offsets depth :=
  let corners := AlignedCorners.build anchors offsets
  let sides := Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row =>
    let values := fun point => Polygon.energyPrimitivePoint (anchors.alignedValue offsets column row point)
    (⟨horizontalBoundary values depth (geometry.x.coordinates column.castSucc) (geometry.x.coordinates column.succ)
      (geometry.y.coordinates row.castSucc),
      PreparedBoxBoundary.verticalBoundary values depth (geometry.y.coordinates row.castSucc) (geometry.y.coordinates
        row.succ) (geometry.x.coordinates column.succ),
      PreparedBoxBoundary.horizontalBoundary values depth (geometry.x.coordinates column.castSucc)
        (geometry.x.coordinates column.succ) (geometry.y.coordinates row.succ),
      PreparedBoxBoundary.verticalBoundary values depth (geometry.y.coordinates row.castSucc) (geometry.y.coordinates
        row.succ) (geometry.x.coordinates column.castSucc)⟩ : Boundary.Assembly.Sides)
  let horizontal := Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row =>
    Boundary.Assembly.horizontalSeam (fun column row => sides column row) column row -
      Boundary.Corners.horizontalEndpoint corners.values column row
  let vertical := Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row =>
    Boundary.Assembly.verticalSeam (fun column row => sides column row) column row - Boundary.Corners.verticalEndpoint
      corners.values column row
  { corners := corners
    sides := sides
    bottom_eq := fun column row => by dsimp only [sides]; rw [Vector.Basic.vectorOfFn_apply,
      Vector.Basic.vectorOfFn_apply]
    right_eq := fun column row => by dsimp only [sides]; rw [Vector.Basic.vectorOfFn_apply,
      Vector.Basic.vectorOfFn_apply]
    top_eq := fun column row => by dsimp only [sides]; rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
    left_eq := fun column row => by dsimp only [sides]; rw [Vector.Basic.vectorOfFn_apply,
      Vector.Basic.vectorOfFn_apply]
    localTotal := Boundary.Assembly.localBoundary (fun column row => sides column row)
    localTotal_eq := rfl
    exterior := Boundary.Assembly.exteriorSides (fun column row => sides column row) + corners.exteriorJoins
    exterior_eq := rfl
    horizontalCorrections := horizontal
    horizontalCorrections_eq := fun column row => by dsimp only [horizontal]; rw [Vector.Basic.vectorOfFn_apply,
      Vector.Basic.vectorOfFn_apply]
    verticalCorrections := vertical
    verticalCorrections_eq := fun column row => by dsimp only [vertical]; rw [Vector.Basic.vectorOfFn_apply,
      Vector.Basic.vectorOfFn_apply]
    seamTotal := FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row => horizontal column row)) +
      FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row => vertical column row))
    seamTotal_eq := by
      apply congrArg₂ (· + ·)
      · apply FiniteSum.Fin.sumFin_congr
        intro column
        apply FiniteSum.Fin.sumFin_congr
        intro row
        dsimp only [horizontal]
        rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
      · apply FiniteSum.Fin.sumFin_congr
        intro column
        apply FiniteSum.Fin.sumFin_congr
        intro row
        dsimp only [vertical]
        rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply] }

open Purelib.Algebra in
/-- The retained seam total is the sum of its actual cached horizontal and vertical corrections. -/
theorem seamTotal_eq_sum (assembly : BoundaryAssembly anchors offsets depth) :
    assembly.seamTotal = FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row =>
      assembly.horizontalCorrections column row)) +
      FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row => assembly.verticalCorrections column row)) :=
        by
  rw [assembly.seamTotal_eq]
  apply congrArg₂ (· + ·)
  · apply FiniteSum.Fin.sumFin_congr
    intro column
    apply FiniteSum.Fin.sumFin_congr
    intro row
    exact (assembly.horizontalCorrections_eq column row).symm
  · apply FiniteSum.Fin.sumFin_congr
    intro column
    apply FiniteSum.Fin.sumFin_congr
    intro row
    exact (assembly.verticalCorrections_eq column row).symm

section
open Purelib.Geometry.Rational
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Integration.Polynomial.Rectangle
/-- The cached horizontal correction reads back the original left/right primitive dyadic difference. -/
theorem horizontalCorrection_eq_dyadic (assembly : BoundaryAssembly anchors offsets depth) (column : Fin columns) (row :
  Fin (rows + 1)) :
    let start := geometry.vertex column.castSucc.succ row.castSucc
    let finish := geometry.vertex column.castSucc.succ row.succ
    let point := fun parameter => Affine.line start (finish - start) parameter
    assembly.horizontalCorrections column row = DyadicBoundaryRibbon.dyadicDifference
      (fun parameter => anchors.alignedValue offsets column.castSucc row (point parameter))
      (fun parameter => anchors.alignedValue offsets column.succ row (point parameter)) depth 0 1 := by
  dsimp only
  rw [assembly.horizontalCorrections_eq, Boundary.Assembly.horizontalSeam, assembly.right_eq, assembly.left_eq,
    Boundary.Corners.horizontalEndpoint, assembly.corners.upperLeft_eq, assembly.corners.upperRight_eq,
    assembly.corners.lowerLeft_eq, assembly.corners.lowerRight_eq, Fin.castSucc_succ]
  rw [DyadicBoundaryRibbon.verticalBoundary_eq_lineArea, DyadicBoundaryRibbon.verticalBoundary_eq_lineArea]
  rw [DyadicBoundaryRibbon.dyadicDifference, line_one,
    line_zero, BoundaryRibbon.area_sub_self_right, BoundaryRibbon.area_sub_self_right]
  rfl

/-- The cached vertical correction reads back the original upper/lower primitive dyadic difference. -/
theorem verticalCorrection_eq_dyadic (assembly : BoundaryAssembly anchors offsets depth) (column : Fin (columns + 1))
  (row : Fin rows) :
    let start := geometry.vertex column.castSucc row.castSucc.succ
    let finish := geometry.vertex column.succ row.castSucc.succ
    let point := fun parameter => Affine.line start (finish - start) parameter
    assembly.verticalCorrections column row = DyadicBoundaryRibbon.dyadicDifference
      (fun parameter => anchors.alignedValue offsets column row.succ (point parameter))
      (fun parameter => anchors.alignedValue offsets column row.castSucc (point parameter)) depth 0 1 := by
  dsimp only
  rw [assembly.verticalCorrections_eq, Boundary.Assembly.verticalSeam, assembly.bottom_eq, assembly.top_eq,
    Boundary.Corners.verticalEndpoint, assembly.corners.upperRight_eq, assembly.corners.lowerRight_eq,
    assembly.corners.upperLeft_eq, assembly.corners.lowerLeft_eq, Fin.castSucc_succ]
  rw [DyadicBoundaryRibbon.horizontalBoundary_eq_lineArea, DyadicBoundaryRibbon.horizontalBoundary_eq_lineArea]
  rw [DyadicBoundaryRibbon.dyadicDifference, line_one,
    line_zero, BoundaryRibbon.area_sub_self_right, BoundaryRibbon.area_sub_self_right]
  rfl

end

open Purelib.Integration.Polynomial.Rectangle in
/-- The original local-minus-exterior boundary equals its retained seam and corner totals. -/
theorem decomposition (assembly : BoundaryAssembly anchors offsets depth) :
    assembly.localTotal - assembly.exterior = assembly.seamTotal + assembly.corners.cornerTotal := by
  rw [assembly.localTotal_eq, assembly.exterior_eq, assembly.seamTotal_eq,
    assembly.corners.exteriorJoins_eq, assembly.corners.cornerTotal_eq]
  exact Boundary.Assembly.localBoundary_sub_stitchedExterior _ _

open Purelib.Algebra
open Purelib.Geometry.Rectangle.Partition
open Purelib.Integration.Energy
/-- The retained local total equals the sum of the original individual rectangle boundaries. -/
theorem localTotal_eq_rectangles (assembly : BoundaryAssembly anchors offsets depth) :
    assembly.localTotal = FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row =>
      PreparedBoxBoundary.rectangleBoundary (fun point => Polygon.energyPrimitivePoint (anchors.alignedValue offsets
        column row point)) depth (geometry.box column row))) := by
  rw [assembly.localTotal_eq]
  apply FiniteSum.Fin.sumFin_congr
  intro column
  apply FiniteSum.Fin.sumFin_congr
  intro row
  rw [assembly.bottom_eq, assembly.right_eq, assembly.top_eq, assembly.left_eq]
  rfl

/-- The retained local total equals the triangulated coordinate-wedge sum at the original depth. -/
theorem localTotal_eq_wedges (assembly : BoundaryAssembly anchors offsets depth) :
    assembly.localTotal = FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row =>
      PreparedBoxBoundary.sumCoordinateWedges
        (fun point => Polygon.energyPrimitivePoint (anchors.alignedValue offsets column row point))
        (PreparedBoxTriangulation.boxTriangles (PreparedBoxPartitions.cells depth (geometry.box column row))))) := by
  rw [assembly.localTotal_eq_rectangles]
  apply FiniteSum.Fin.sumFin_congr
  intro column
  apply FiniteSum.Fin.sumFin_congr
  intro row
  rw [PreparedBoxBoundary.sumCoordinateWedges_boxTriangles, PreparedBoxBoundary.sumBoxBoundaries_cells]

end BoundaryAssembly

end Purelib.Riemann.Readings.RectangularBoundaryAssembly
