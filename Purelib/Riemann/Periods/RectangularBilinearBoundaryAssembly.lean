module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Riemann.Integration.RectangularPrimitiveCorners
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps

import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly
import Purelib.Integration.Polynomial.Rectangle.Boundary.Corners
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Riemann.Periods.RectangularBilinearCorners
public import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Tactic.Ring
public import Purelib.Riemann.Readings.RectangularPointReadings

open Purelib.Riemann.Normalization.InverseRootPolynomial

@[expose] public section

/-!
# Actual local primitive mesh boundaries assembled across a regular grid

Each coarse cell uses its own primitive on all its fine triangles.  Fine
diagonals cancel inside that cell before the coarse seam errors are paid.
The stitched exterior, corrected seams, and corner terms are cached and
connected by an exact identity.  This avoids charging a fixed ownership
mismatch separately to every fine triangle.
-/

namespace Purelib.Riemann.Periods.RectangularBilinearBoundaryAssembly

open Purelib.Data in
/-- The exact Gaussian rational carrier of the boundary readings. -/
private abbrev Gaussian := Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Gaussian.Basic in
/-- The dense Gaussian polynomial carrier of the retained primitive models. -/
private abbrev Polynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
open Purelib.Data in
/-- The retained finite vector representation used for side and correction caches. -/
private abbrev Vector := Data.Vector
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveCorners (AlignedCorners)

open Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary (horizontalBoundary verticalBoundary rectangleBoundary)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (line_zero line_one)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions (cells)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

open Purelib.Data in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Polynomial.Rectangle.Boundary in
open Purelib.LinearAlgebra in
open Purelib.Polynomial.Dense.Gaussian.Basic in
open Purelib.Riemann in
open Purelib.Topology in
set_option genInjectivity false in
/-- Cached local boundaries, stitched exterior and corrected seams of two primitive banks.

Each coarse rectangle uses its own aligned primitive pair on all fine triangles. Exact side and corner readbacks
preserve the original owners and relate their local total to the stitched exterior, corrected seams and corner polygons.
-/
structure BilinearBoundaryAssembly {polynomial firstNumerator secondNumerator :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {columns rows : Nat}
  {geometry : Geometry columns rows}
    {firstModels secondModels : Bank polynomial geometry} {firstPrimitives : Primitives firstModels firstNumerator}
      {secondPrimitives : Primitives secondModels secondNumerator}
    (firstAnchors : PrimitiveAnchors firstPrimitives) (firstOffsets : LinearAlgebra.Grid.Offsets firstAnchors.edges)
    (secondAnchors : PrimitiveAnchors secondPrimitives) (secondOffsets : LinearAlgebra.Grid.Offsets secondAnchors.edges)
      (depth : Nat) where
  /-- The retained aligned corners of the first primitive bank. -/ firstCorners : AlignedCorners firstAnchors
    firstOffsets
  /-- The retained aligned corners of the second primitive bank. -/ secondCorners : AlignedCorners secondAnchors
    secondOffsets
  /-- The cached paired primitive values at every coarse-cell corner. -/ corners : Periods.BilinearGridBoundary.Values
    columns rows
  /-- The paired corners use the two retained aligned-corner banks. -/ corners_eq : corners =
    Periods.BilinearGridBoundary.pairValues firstCorners.values secondCorners.values
  /-- The cached sum of the coarse junction corner polygons. -/ cornerTotal : Gaussian.Basic.Canonical
  /-- The cached corner total is the exact corner sum of the retained paired values. -/ cornerTotal_eq : cornerTotal =
    Periods.BilinearGridBoundary.cornerSum corners
  /-- The four cached fine boundary readings for every coarse cell. -/ sides : Data.Vector (Data.Vector
    Assembly.Sides (rows + 1)) (columns + 1)
  /-- The bottom reading is the actual horizontal dyadic boundary of that cell's aligned primitive pair. -/ bottom_eq :
    ∀ column row, (sides column row).bottom = PreparedBoxBoundary.horizontalBoundary
    (fun point => (⟨firstAnchors.alignedValue firstOffsets column row point, secondAnchors.alignedValue secondOffsets
      column row point⟩ : Polygon.Stokes.PrimitivePoint)) depth
      (geometry.x.coordinates column.castSucc) (geometry.x.coordinates column.succ) (geometry.y.coordinates
        row.castSucc)
  /-- The right reading is the actual vertical dyadic boundary of that cell's aligned primitive pair. -/ right_eq : ∀
    column row, (sides column row).right = PreparedBoxBoundary.verticalBoundary
    (fun point => (⟨firstAnchors.alignedValue firstOffsets column row point, secondAnchors.alignedValue secondOffsets
      column row point⟩ : Polygon.Stokes.PrimitivePoint)) depth
      (geometry.y.coordinates row.castSucc) (geometry.y.coordinates row.succ) (geometry.x.coordinates column.succ)
  /-- The top reading is the actual horizontal dyadic boundary of that cell's aligned primitive pair. -/ top_eq : ∀
    column row, (sides column row).top = PreparedBoxBoundary.horizontalBoundary
    (fun point => (⟨firstAnchors.alignedValue firstOffsets column row point, secondAnchors.alignedValue secondOffsets
      column row point⟩ : Polygon.Stokes.PrimitivePoint)) depth
      (geometry.x.coordinates column.castSucc) (geometry.x.coordinates column.succ) (geometry.y.coordinates row.succ)
  /-- The left reading is the actual vertical dyadic boundary of that cell's aligned primitive pair. -/ left_eq : ∀
    column row, (sides column row).left = PreparedBoxBoundary.verticalBoundary
    (fun point => (⟨firstAnchors.alignedValue firstOffsets column row point, secondAnchors.alignedValue secondOffsets
      column row point⟩ : Polygon.Stokes.PrimitivePoint)) depth
      (geometry.y.coordinates row.castSucc) (geometry.y.coordinates row.succ) (geometry.x.coordinates column.castSucc)
  /-- The cached sum of all original coarse-cell boundary readings. -/ localTotal : Gaussian.Basic.Canonical
  /-- The local total sums the four retained oriented sides of every cell. -/ localTotal_eq : localTotal =
    Assembly.localBoundary (fun column row => sides column row)
  /-- The cached exterior with the original endpoint joins included. -/ exterior : Gaussian.Basic.Canonical
  /-- The exterior is the sum of its retained outer sides and paired corner joins. -/ exterior_eq : exterior =
    Assembly.exteriorSides (fun column row => sides column row) + Periods.BilinearGridBoundary.exteriorJoins corners
  /-- The cached seam corrections between horizontally adjacent coarse cells. -/ horizontalCorrections :
    Data.Vector (Data.Vector Gaussian.Basic.Canonical (rows + 1)) columns
  /-- Each horizontal correction subtracts its original endpoint term from the actual seam. -/ horizontalCorrections_eq
    : ∀ column row, horizontalCorrections column row =
    Assembly.horizontalSeam (fun column row => sides column row) column row -
      Periods.BilinearGridBoundary.horizontalEndpoint corners column row
  /-- The cached seam corrections between vertically adjacent coarse cells. -/ verticalCorrections : Data.Vector
    (Data.Vector Gaussian.Basic.Canonical rows) (columns + 1)
  /-- Each vertical correction subtracts its original endpoint term from the actual seam. -/ verticalCorrections_eq : ∀
    column row, verticalCorrections column row =
    Assembly.verticalSeam (fun column row => sides column row) column row -
      Periods.BilinearGridBoundary.verticalEndpoint corners column row
  /-- The cached sum of both families of corrected seams. -/ seamTotal : Gaussian.Basic.Canonical
  /-- The seam total is the corrected seam sum of the retained sides and corners. -/ seamTotal_eq : seamTotal =
    Periods.BilinearGridBoundary.correctedSeamSum (fun column row => sides column row) corners

constructive_injectivity BilinearBoundaryAssembly

namespace BilinearBoundaryAssembly

open Purelib.Data in
open Purelib.Integration.Polynomial.Rectangle.Boundary in
open Purelib.Riemann in
open Purelib.Riemann.Periods.BilinearGridBoundary in
/-- Read one paired corner entry from its two original finite corner vectors. -/
private theorem pairValues_apply {columns rows : Nat}
    (first second : Corners.Values columns rows)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    Periods.BilinearGridBoundary.pairValues first second column row =
      CornerValues.pair (first column row) (second column row) := by
  rw [Periods.BilinearGridBoundary.pairValues, Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]

variable {polynomial firstNumerator secondNumerator :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {columns
  rows : Nat} {geometry : Geometry columns rows}
    {firstModels secondModels : Bank polynomial geometry} {firstPrimitives : Primitives firstModels firstNumerator}
      {secondPrimitives : Primitives secondModels secondNumerator}
    {firstAnchors : PrimitiveAnchors firstPrimitives} {firstOffsets : LinearAlgebra.Grid.Offsets
      firstAnchors.edges}
    {secondAnchors : PrimitiveAnchors secondPrimitives} {secondOffsets : LinearAlgebra.Grid.Offsets
      secondAnchors.edges} {depth : Nat}

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Polynomial.Rectangle.Boundary in
open Purelib.LinearAlgebra in
open Purelib.Riemann in
open Purelib.Topology in
/-- Materialize the actual side sums, paired corners and corrected-seam caches.

The constructor stores exact readback equations for the original aligned primitive banks at the given depth, permitting
clients to consume the cached boundaries and corrections directly. -/
def build (firstAnchors : PrimitiveAnchors firstPrimitives) (firstOffsets : LinearAlgebra.Grid.Offsets
  firstAnchors.edges)
    (secondAnchors : PrimitiveAnchors secondPrimitives) (secondOffsets : LinearAlgebra.Grid.Offsets secondAnchors.edges)
      (depth : Nat) :
    BilinearBoundaryAssembly firstAnchors firstOffsets secondAnchors secondOffsets depth :=
  let firstCorners := AlignedCorners.build firstAnchors firstOffsets
  let secondCorners := AlignedCorners.build secondAnchors secondOffsets
  let corners := Periods.BilinearGridBoundary.pairValues firstCorners.values secondCorners.values
  let sides := Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row =>
    let values := fun point => (⟨firstAnchors.alignedValue firstOffsets column row point, secondAnchors.alignedValue
      secondOffsets column row point⟩ : Polygon.Stokes.PrimitivePoint)
    (⟨horizontalBoundary values depth (geometry.x.coordinates column.castSucc) (geometry.x.coordinates column.succ)
      (geometry.y.coordinates row.castSucc),
      PreparedBoxBoundary.verticalBoundary values depth (geometry.y.coordinates row.castSucc) (geometry.y.coordinates
        row.succ) (geometry.x.coordinates column.succ),
      PreparedBoxBoundary.horizontalBoundary values depth (geometry.x.coordinates column.castSucc)
        (geometry.x.coordinates column.succ) (geometry.y.coordinates row.succ),
      PreparedBoxBoundary.verticalBoundary values depth (geometry.y.coordinates row.castSucc) (geometry.y.coordinates
        row.succ) (geometry.x.coordinates column.castSucc)⟩ : Assembly.Sides)
  let horizontal := Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row =>
    Assembly.horizontalSeam (fun column row => sides column row) column row -
      Periods.BilinearGridBoundary.horizontalEndpoint corners column row
  let vertical := Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row =>
    Assembly.verticalSeam (fun column row => sides column row) column row -
      Periods.BilinearGridBoundary.verticalEndpoint corners column row
  { firstCorners := firstCorners
    secondCorners := secondCorners
    corners := corners
    corners_eq := rfl
    cornerTotal := Periods.BilinearGridBoundary.cornerSum corners
    cornerTotal_eq := rfl
    sides := sides
    bottom_eq := fun column row => by dsimp only [sides]; rw [Vector.Basic.vectorOfFn_apply,
      Vector.Basic.vectorOfFn_apply]
    right_eq := fun column row => by dsimp only [sides]; rw [Vector.Basic.vectorOfFn_apply,
      Vector.Basic.vectorOfFn_apply]
    top_eq := fun column row => by dsimp only [sides]; rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
    left_eq := fun column row => by dsimp only [sides]; rw [Vector.Basic.vectorOfFn_apply,
      Vector.Basic.vectorOfFn_apply]
    localTotal := Assembly.localBoundary (fun column row => sides column row)
    localTotal_eq := rfl
    exterior := Assembly.exteriorSides (fun column row => sides column row) + Periods.BilinearGridBoundary.exteriorJoins
      corners
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
/-- The cached seam total equals the finite sums of its two retained correction vectors. -/
theorem seamTotal_eq_sum (assembly : BilinearBoundaryAssembly firstAnchors firstOffsets secondAnchors secondOffsets
  depth) :
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
open Purelib.Geometry
open Purelib.Integration.Polynomial.Rectangle.Boundary
open Purelib.Riemann
open Purelib.Riemann.Periods.BilinearGridBoundary
open Purelib.Topology
open Purelib.Topology.Polygon.Stokes
/-- A horizontal adjacency correction is the exact dyadic ribbon difference on its vertical seam.

The two retained coarse-cell owners use the same geometric segment, and the original endpoint correction is included in
the ribbon identity. -/
theorem horizontalCorrection_eq_dyadic
    (assembly : BilinearBoundaryAssembly firstAnchors firstOffsets secondAnchors secondOffsets depth)
    (column : Fin columns) (row : Fin (rows + 1)) :
    let start := geometry.vertex column.castSucc.succ row.castSucc
    let finish := geometry.vertex column.castSucc.succ row.succ
    let point := fun parameter => Rational.Affine.line start (finish - start) parameter
    assembly.horizontalCorrections column row = Periods.DyadicBilinearBoundaryRibbon.dyadicDifference
      (fun parameter => ⟨firstAnchors.alignedValue firstOffsets column.castSucc row (point parameter),
        secondAnchors.alignedValue secondOffsets column.castSucc row (point parameter)⟩)
      (fun parameter => ⟨firstAnchors.alignedValue firstOffsets column.succ row (point parameter),
        secondAnchors.alignedValue secondOffsets column.succ row (point parameter)⟩) depth 0 1 := by
  dsimp only
  rw [assembly.horizontalCorrections_eq, Assembly.horizontalSeam,
    assembly.right_eq, assembly.left_eq, assembly.corners_eq]
  simp only [Periods.BilinearGridBoundary.horizontalEndpoint,
    pairValues_apply, CornerValues.pair,
    assembly.firstCorners.upperLeft_eq, assembly.firstCorners.upperRight_eq,
    assembly.firstCorners.lowerLeft_eq, assembly.firstCorners.lowerRight_eq,
    assembly.secondCorners.upperLeft_eq, assembly.secondCorners.upperRight_eq,
    assembly.secondCorners.lowerLeft_eq, assembly.secondCorners.lowerRight_eq, Fin.castSucc_succ]
  rw [Periods.DyadicBilinearBoundaryRibbon.verticalBoundary_eq_lineArea,
    Periods.DyadicBilinearBoundaryRibbon.verticalBoundary_eq_lineArea,
    Periods.DyadicBilinearBoundaryRibbon.dyadicDifference, line_one, line_zero]
  simp only [Polygon.Stokes.edgeArea, PrimitivePoint.sub, Geometry.vertex]
  ring1

/-- A vertical adjacency correction is the exact dyadic ribbon difference on its horizontal seam.

The two retained coarse-cell owners use the same geometric segment, and the original endpoint correction is included in
the ribbon identity. -/
theorem verticalCorrection_eq_dyadic
    (assembly : BilinearBoundaryAssembly firstAnchors firstOffsets secondAnchors secondOffsets depth)
    (column : Fin (columns + 1)) (row : Fin rows) :
    let start := geometry.vertex column.castSucc row.castSucc.succ
    let finish := geometry.vertex column.succ row.castSucc.succ
    let point := fun parameter => Rational.Affine.line start (finish - start) parameter
    assembly.verticalCorrections column row = Periods.DyadicBilinearBoundaryRibbon.dyadicDifference
      (fun parameter => ⟨firstAnchors.alignedValue firstOffsets column row.succ (point parameter),
        secondAnchors.alignedValue secondOffsets column row.succ (point parameter)⟩)
      (fun parameter => ⟨firstAnchors.alignedValue firstOffsets column row.castSucc (point parameter),
        secondAnchors.alignedValue secondOffsets column row.castSucc (point parameter)⟩) depth 0 1 := by
  dsimp only
  rw [assembly.verticalCorrections_eq, Assembly.verticalSeam,
    assembly.bottom_eq, assembly.top_eq, assembly.corners_eq]
  simp only [Periods.BilinearGridBoundary.verticalEndpoint,
    pairValues_apply, CornerValues.pair,
    assembly.firstCorners.upperLeft_eq, assembly.firstCorners.upperRight_eq,
    assembly.firstCorners.lowerLeft_eq, assembly.firstCorners.lowerRight_eq,
    assembly.secondCorners.upperLeft_eq, assembly.secondCorners.upperRight_eq,
    assembly.secondCorners.lowerLeft_eq, assembly.secondCorners.lowerRight_eq, Fin.castSucc_succ]
  rw [Periods.DyadicBilinearBoundaryRibbon.horizontalBoundary_eq_lineArea,
    Periods.DyadicBilinearBoundaryRibbon.horizontalBoundary_eq_lineArea,
    Periods.DyadicBilinearBoundaryRibbon.dyadicDifference, line_one, line_zero]
  simp only [Polygon.Stokes.edgeArea, PrimitivePoint.sub, Geometry.vertex]
  ring1

end

open Purelib.Riemann in
/-- The local boundary total minus the stitched exterior equals corrected seams plus corner polygons. -/
theorem decomposition (assembly : BilinearBoundaryAssembly firstAnchors firstOffsets secondAnchors secondOffsets depth)
  :
    assembly.localTotal - assembly.exterior = assembly.seamTotal + assembly.cornerTotal := by
  rw [assembly.localTotal_eq, assembly.exterior_eq, assembly.seamTotal_eq, assembly.cornerTotal_eq]
  exact Periods.BilinearGridBoundary.localBoundary_sub_stitchedExterior _ _

open Purelib.Algebra
open Purelib.Geometry.Rectangle.Partition
open Purelib.Topology
/-- Read the cached local total as the sum of the actual fine rectangle boundaries. -/
theorem localTotal_eq_rectangles (assembly : BilinearBoundaryAssembly firstAnchors firstOffsets secondAnchors
  secondOffsets depth) :
    assembly.localTotal = FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row =>
      PreparedBoxBoundary.rectangleBoundary (fun point => (⟨firstAnchors.alignedValue firstOffsets column row point,
        secondAnchors.alignedValue secondOffsets column row point⟩ : Polygon.Stokes.PrimitivePoint)) depth (geometry.box
        column row))) := by
  rw [assembly.localTotal_eq]
  apply FiniteSum.Fin.sumFin_congr
  intro column
  apply FiniteSum.Fin.sumFin_congr
  intro row
  rw [assembly.bottom_eq, assembly.right_eq, assembly.top_eq, assembly.left_eq]
  rfl

/-- Read the local total as the wedge sum of the actual refined cell triangles.

Every triangle uses its coarse cell's own aligned primitive pair, so internal fine diagonals cancel before coarse owner
discrepancies are charged. -/
theorem localTotal_eq_wedges (assembly : BilinearBoundaryAssembly firstAnchors firstOffsets secondAnchors secondOffsets
  depth) :
    assembly.localTotal = FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row =>
      PreparedBoxBoundary.sumCoordinateWedges
        (fun point => (⟨firstAnchors.alignedValue firstOffsets column row point, secondAnchors.alignedValue
          secondOffsets column row point⟩ : Polygon.Stokes.PrimitivePoint))
        (PreparedBoxTriangulation.boxTriangles (PreparedBoxPartitions.cells depth (geometry.box column row))))) := by
  rw [assembly.localTotal_eq_rectangles]
  apply FiniteSum.Fin.sumFin_congr
  intro column
  apply FiniteSum.Fin.sumFin_congr
  intro row
  rw [PreparedBoxBoundary.sumCoordinateWedges_boxTriangles, PreparedBoxBoundary.sumBoxBoundaries_cells]

end BilinearBoundaryAssembly

end Purelib.Riemann.Periods.RectangularBilinearBoundaryAssembly
