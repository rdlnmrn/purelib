module
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Topology.Polygon.Stokes
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Energy.Polygon
import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Mesh.CoordinateTriangulation
public import Purelib.Riemann.Integration.RectangularSharedPrimitives
public import Purelib.Geometry.Rectangle.Partition.RectangularMeshRefinement
public import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

@[expose] public section

/-!
# Geometric boundary of shared primitive meshes

The indexed mesh's cached boundary is exactly the sum on the subdivided
coarse-cell sides.  Fine diagonals and internal refinement edges disappear
before any analytic error is estimated.  This identity holds for generated
meshes satisfying the same coordinate and incidence certificates, not just
for the default indexing algorithm.  The A/B period-word identification is
still a separate cut-surface obligation.
-/

namespace Purelib.Riemann.Readings.RectangularPrimitiveBoundary

open Purelib.Data.Gaussian in
/-- The exact rational Gaussian carrier. -/
private abbrev Gaussian := Basic.Canonical
open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Polynomial.Dense.Gaussian in
/-- The original dense Gaussian polynomial carrier. -/
private abbrev Polynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial

open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeListArea triangleWedgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary (coordinateWedge sumCoordinateWedges rectangleBoundary)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

namespace SharedPrimitiveValues

variable {polynomial numerator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {columns
  rows : Nat} {geometry
  : Geometry columns rows}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator}
    {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
    {triangles : List (ModelTriangle geometry)} {surface : OwnedTriangulation triangles}

open Purelib in
open Purelib.Data.Gaussian in
/-- Read the retained shared primitive at a present original mesh coordinate, returning zero outside the vertex list. -/
def atPoint (readings : SharedPrimitiveValues anchors offsets surface) (point : Basic.Canonical) : Basic.Canonical :=
  if member : point ∈ surface.mesh.vertices then
    readings.values (Topology.Mesh.CoordinateTriangulation.lookupVertex point surface.mesh.vertices member).index
  else 0

open Purelib in
open Purelib.Riemann.Readings in
/-- Coordinate lookup returns the exact retained reading at every original mesh vertex. -/
theorem atPoint_coordinate (readings : SharedPrimitiveValues anchors offsets surface)
    (vertex : Fin surface.mesh.vertices.length) : RectangularPrimitiveBoundary.SharedPrimitiveValues.atPoint readings
      (surface.mesh.coordinate vertex) = readings.values vertex := by
  have member : surface.mesh.coordinate vertex ∈ surface.mesh.vertices := List.getElem_mem _
  rw [atPoint, dif_pos member]
  exact readings.coordinate_consistent _ vertex (Topology.Mesh.CoordinateTriangulation.lookupVertex _ _ _).coordinate_eq

open Purelib.Algebra in
open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Energy in
open Purelib.Riemann.Readings in
/-- The original affine sample boundary area equals the sum of its coordinate triangle wedges.

Lookup consistency identifies each retained vertex value with its original coordinate, preserving the exact triangle
list and finite face indices. -/
theorem sample_boundary_eq_wedges (readings : SharedPrimitiveValues anchors offsets surface)
    (radius : Fraction.Rational) (positive : 0 < radius) :
    (readings.sample radius positive).boundaryArea =
      PreparedBoxBoundary.sumCoordinateWedges (fun point => Polygon.energyPrimitivePoint
        (RectangularPrimitiveBoundary.SharedPrimitiveValues.atPoint readings point))
        (triangles.map ModelTriangle.triangle) := by
  change edgeListArea (fun vertex => Polygon.energyPrimitivePoint (readings.values vertex))
    surface.mesh.triangulation.boundary = _
  rw [← surface.mesh.wedgeSum_eq_boundaryArea, PreparedBoxBoundary.sumCoordinateWedges_eq_sumFin]
  apply FiniteSum.Fin.sumFin_congr
  intro face
  have coordinates := surface.mesh.face_coordinates face
  change triangleWedgeArea
    (Polygon.energyPrimitivePoint (readings.values (surface.mesh.triangulation.faces face).first))
    (Polygon.energyPrimitivePoint (readings.values (surface.mesh.triangulation.faces face).second))
    (Polygon.energyPrimitivePoint (readings.values (surface.mesh.triangulation.faces face).third)) = _
  rw [← RectangularPrimitiveBoundary.SharedPrimitiveValues.atPoint_coordinate readings, ←
    RectangularPrimitiveBoundary.SharedPrimitiveValues.atPoint_coordinate readings, ←
    RectangularPrimitiveBoundary.SharedPrimitiveValues.atPoint_coordinate readings,
    coordinates.1, coordinates.2.1, coordinates.2.2]
  rfl

end SharedPrimitiveValues

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rectangle.Partition in
/-- Coordinate wedge sums add over concatenated original triangle lists.

Structural recursion retains the same coordinate triangle at each head. The
unchanged tail supplies its own wedge sum, so concatenation groups exactly the
original ordered contributions. -/
private theorem wedges_append (primitive : Basic.Canonical → PrimitivePoint)
    (first last : List Topology.Mesh.CoordinateTriangulation.CoordinateTriangle) :
    PreparedBoxBoundary.sumCoordinateWedges primitive (first ++ last) =
      PreparedBoxBoundary.sumCoordinateWedges primitive first + PreparedBoxBoundary.sumCoordinateWedges primitive last
        := by
  induction first with
  | nil =>
      simp only [List.nil_append, PreparedBoxBoundary.sumCoordinateWedges, zero_add, -eq_self, -iff_self]
      rfl
  | cons triangle rest ih =>
      simp only [List.cons_append, PreparedBoxBoundary.sumCoordinateWedges, ih, add_assoc, -eq_self, -iff_self]
      rfl

namespace Geometry

variable {columns rows : Nat}

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rectangle.Partition in
/-- Sum the retained depth's rectangle-boundary areas over the original ordered cell selection. -/
def selectionBoundary (geometry : Geometry columns rows) (primitive : Basic.Canonical → PrimitivePoint) (depth : Nat) :
    List (Fin (columns + 1) × Fin (rows + 1)) → Basic.Canonical
  | [] => 0
  | cell :: rest => PreparedBoxBoundary.rectangleBoundary primitive depth (geometry.box cell.1 cell.2) +
      Purelib.Riemann.Readings.RectangularPrimitiveBoundary.Geometry.selectionBoundary geometry primitive depth rest

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Riemann.Readings in
open Purelib.Data.List in
/-- The refined original selection's triangle wedges equal its ordered rectangle-boundary sum.

The original refinement concatenates each selected cell's retained triangles.
Their coordinate wedges read back that same cell boundary, and structural
induction adds those boundaries in the original selection order. -/
theorem refineSelection_wedges (geometry : Geometry columns rows) (primitive : Basic.Canonical → PrimitivePoint)
    (depth : Nat) (selection : List (Fin (columns + 1) × Fin (rows + 1))) :
    PreparedBoxBoundary.sumCoordinateWedges primitive
        ((Geometry.Rectangle.Partition.RectangularMeshRefinement.refineSelection geometry
      selection depth).map ModelTriangle.triangle) =
      RectangularPrimitiveBoundary.Geometry.selectionBoundary geometry primitive depth selection := by
  induction selection with
  | nil => rfl
  | cons cell rest ih =>
      simp only [Geometry.Rectangle.Partition.RectangularMeshRefinement.refineSelection, Flatten.flatMap_cons,
          Map.map_append,
        wedges_append,
        RectangularMeshRefinement.ModelTriangle.refineCell_coordinates,
          PreparedBoxBoundary.sumCoordinateWedges_boxTriangles,
        PreparedBoxBoundary.sumBoxBoundaries_cells, selectionBoundary, -eq_self, -iff_self]
      dsimp only [Geometry.Rectangle.Partition.RectangularMeshRefinement.refineSelection] at ih
      exact congrArg (PreparedBoxBoundary.rectangleBoundary primitive depth (geometry.box cell.1 cell.2) + ·) ih

end Geometry

namespace SharedPrimitiveValues

variable {polynomial numerator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {columns
  rows : Nat} {geometry
  : Geometry columns rows}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator}
    {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
    {selection : List (Fin (columns + 1) × Fin (rows + 1))} {depth : Nat}
    {surface : OwnedTriangulation
      (Geometry.Rectangle.Partition.RectangularMeshRefinement.refineSelection geometry selection
      depth)}

open Purelib.Data.Rat
open Purelib.Integration.Energy
open Purelib.Riemann.Readings
/-- The original shared primitive sample boundary equals the retained selected-cell boundary sum. -/
theorem sample_boundary_eq_selection (readings : SharedPrimitiveValues anchors offsets surface)
    (radius : Fraction.Rational) (positive : 0 < radius) :
    (readings.sample radius positive).boundaryArea =
      RectangularPrimitiveBoundary.Geometry.selectionBoundary geometry (fun point => Polygon.energyPrimitivePoint
        (RectangularPrimitiveBoundary.SharedPrimitiveValues.atPoint readings point)) depth selection := by
  rw [RectangularPrimitiveBoundary.SharedPrimitiveValues.sample_boundary_eq_wedges readings,
    RectangularPrimitiveBoundary.Geometry.refineSelection_wedges geometry]

/-- The original affine energy minus its retained error budget is bounded by the selected boundary energy.

The same shared primitive readings determine both the affine sample and the exact imaginary boundary-area readback. -/
theorem sample_energy_le_selectionBoundary (readings : SharedPrimitiveValues anchors offsets surface)
    (radius : Fraction.Rational) (positive : 0 < radius) :
    let sample := readings.sample radius positive
    sample.affineEnergy - sample.errorBudget ≤
      (RectangularPrimitiveBoundary.Geometry.selectionBoundary geometry (fun point => Polygon.energyPrimitivePoint
        (RectangularPrimitiveBoundary.SharedPrimitiveValues.atPoint readings point)) depth selection).im / 4 := by
  have estimate := (readings.sample radius positive).affineEnergy_sub_errorBudget_le_boundaryEnergy
  rw [RectangularPrimitiveBoundary.SharedPrimitiveValues.sample_boundary_eq_selection readings] at estimate
  exact estimate

end SharedPrimitiveValues

end Purelib.Riemann.Readings.RectangularPrimitiveBoundary
