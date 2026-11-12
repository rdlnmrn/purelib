module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Branches.RectangularSheetGauge

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
public import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularPrimitiveOverlap
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Mesh-independent cached readings of a finite point bank

Each point has one retained containing-cell owner and one evaluated value.
Any fine mesh using the same primitive data compares to this fixed bank,
paying both ownership discrepancies on each increment.
-/

namespace Purelib.Riemann.Readings.RectangularPointReadings

variable {pairs : Nat}

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex ModelTriangle OwnedTriangulation)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)

open Purelib in
open Purelib.Data in
set_option genInjectivity false in
/-- Cached primitive readings and containing cell owners for an original finite point family.

The retained owner vector has the exact point count, and each original coordinate and aligned-value readback is stored
explicitly. -/
structure PointReadings {polynomial numerator : Polynomial} {columns rows count : Nat}
    {geometry : Geometry columns rows} {models : Bank polynomial geometry}
    {primitives : Primitives models numerator pairs}
    (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges) (points : Fin
      count → Gaussian) where
  /-- The retained cell owners indexed by the original finite point family. -/ owners : Data.Vector (OwnedVertex
    geometry) count
  /-- Each retained owner's coordinate equals the exact original indexed point. -/ point_eq : ∀ index, (owners
    index).point = points index
  /-- The cached original point-family primitive readings. -/ values : Data.Vector Gaussian count
  /-- Each cached reading equals the aligned primitive at its exact retained owner coordinate. -/ value_eq : ∀ index,
    values index = anchors.alignedValue offsets
    (owners index).column (owners index).row (owners index).point

constructive_injectivity PointReadings

namespace PointReadings

variable {polynomial numerator : Polynomial} {columns rows count : Nat} {geometry : Geometry columns rows}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator pairs}

open Purelib in
open Purelib.Data in
/-- Cache the original finite point family's aligned readings using the supplied exact cell owners. -/
def build (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (points : Fin count → Gaussian) (owners : Data.Vector (OwnedVertex geometry) count)
    (pointEq : ∀ index, (owners index).point = points index) : PointReadings anchors offsets points :=
  ⟨owners, pointEq, Vector.Basic.vectorOfFn fun index => anchors.alignedValue offsets
    (owners index).column (owners index).row (owners index).point, Vector.Basic.vectorOfFn_apply _⟩

/-- Read every literal point in one original cell, preserving the whole primitive, anchor and offset caches. -/
def inCell (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (points : Fin count → Gaussian)
    (inside : ∀ position, (geometry.box column row).Contains (points position)) :
    PointReadings anchors offsets points :=
  PointReadings.build anchors offsets points
    (vectorOfFn fun position => (⟨column, row, points position, inside position⟩ : OwnedVertex geometry))
    (fun position => by rewrite [vectorOfFn_apply]; rfl)

/-- The same-cell reader retains the complete original cell and point owner at each repeated or stationary slot. -/
theorem inCell_owner (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (points : Fin count → Gaussian)
    (inside : ∀ position, (geometry.box column row).Contains (points position)) (position : Fin count) :
    (inCell anchors offsets column row points inside).owners position =
      (⟨column, row, points position, inside position⟩ : OwnedVertex geometry) := by
  change (vectorOfFn fun position =>
    (⟨column, row, points position, inside position⟩ : OwnedVertex geometry)) position = _
  exact vectorOfFn_apply _ position

/-- Each same-cell value is the original primitive plus that SAME cell's retained additive offset. -/
theorem inCell_value (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (points : Fin count → Gaussian)
    (inside : ∀ position, (geometry.box column row).Contains (points position)) (position : Fin count) :
    (inCell anchors offsets column row points inside).values position =
      offsets.values column row + primitives.value column row (points position) :=
  ((inCell anchors offsets column row points inside).value_eq position).trans
    (congrArg (fun owner : OwnedVertex geometry =>
      anchors.alignedValue offsets owner.column owner.row owner.point)
      (inCell_owner anchors offsets column row points inside position))

/-- Two endpoints in the SAME original cell recover that exact raw primitive increment without normalizing constants. -/
theorem inCell_increment (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (points : Fin count → Gaussian)
    (inside : ∀ position, (geometry.box column row).Contains (points position)) (first last : Fin count) :
    (inCell anchors offsets column row points inside).values last -
        (inCell anchors offsets column row points inside).values first =
      (primitives.dense column row).value.eval (points last) -
        (primitives.dense column row).value.eval (points first) :=
  (congrArg₂ (fun last first : Gaussian => last - first)
    (inCell_value anchors offsets column row points inside last)
    (inCell_value anchors offsets column row points inside first)).trans (by
      change (offsets.values column row + primitives.value column row (points last)) -
          (offsets.values column row + primitives.value column row (points first)) =
        primitives.value column row (points last) - primitives.value column row (points first)
      ring1)

end PointReadings

namespace GridPrimitiveAccuracy

variable {polynomial numerator : Polynomial} {ambient : Box} {clearance : RegionClearance polynomial ambient}
    {bounds : PrimitiveOverlapBounds clearance numerator} {columns rows count : Nat} {target : Coordinate}
    {geometry : Geometry columns rows} {bank : Bank polynomial geometry}

section Comparisons

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration

/-- Two retained readings at the same point pay their actual containing-cell discrepancy.

Both banks retain the same primitive polynomials, anchors and offsets.
Their original point indices and complete cell owners remain distinct;
the coordinate equality supplies the numerical incidence.
-/
theorem point_comparison_bound (request : GridPrimitiveAccuracy bounds columns target pairs)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator pairs}
    {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
    {points : Fin count → Gaussian} (fixed : PointReadings anchors offsets points)
    {otherCount : Nat} {otherPoints : Fin otherCount → Gaussian}
    (other : PointReadings anchors offsets otherPoints)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (position : Fin count) (otherPosition : Fin otherCount) (same : points position = otherPoints otherPosition) :
    Norm.Basic.normSq (fixed.values position - other.values otherPosition) ≤ 4 * request.globalBound := by
  have firstInside : (geometry.box (fixed.owners position).column (fixed.owners position).row).Contains
      (points position) :=
    Eq.mp (congrArg (fun point =>
      (geometry.box (fixed.owners position).column (fixed.owners position).row).Contains point)
      (fixed.point_eq position)) (fixed.owners position).contains
  have lastInside : (geometry.box (other.owners otherPosition).column (other.owners otherPosition).row).Contains
      (points position) :=
    Eq.mpr (congrArg (fun point =>
      (geometry.box (other.owners otherPosition).column (other.owners otherPosition).row).Contains point) same)
      (Eq.mp (congrArg (fun point =>
        (geometry.box (other.owners otherPosition).column (other.owners otherPosition).row).Contains point)
        (other.point_eq otherPosition)) (other.owners otherPosition).contains)
  rewrite [Norm.Basic.normSq_eq_canonical, fixed.value_eq position, other.value_eq otherPosition,
    fixed.point_eq position, other.point_eq otherPosition, ← same]
  exact request.overlap_bound anchors offsets refines
    (fixed.owners position).column (other.owners otherPosition).column
    (fixed.owners position).row (other.owners otherPosition).row firstInside lastInside

/-- Matching endpoint pairs pay the increment change on their same original numerator primitive bank.

The finite bound combines both actual same-point discrepancies. Every
endpoint index, cell owner and primitive constant remains retained.
-/
theorem increment_comparison_bound (request : GridPrimitiveAccuracy bounds columns target pairs)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator pairs}
    {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
    {points : Fin count → Gaussian} (fixed : PointReadings anchors offsets points)
    {otherCount : Nat} {otherPoints : Fin otherCount → Gaussian}
    (other : PointReadings anchors offsets otherPoints)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (first last : Fin count) (otherFirst otherLast : Fin otherCount)
    (firstEq : points first = otherPoints otherFirst) (lastEq : points last = otherPoints otherLast) :
    Norm.Basic.normSq ((fixed.values last - fixed.values first) -
      (other.values otherLast - other.values otherFirst)) ≤ 16 * request.globalBound := by
  have firstBound := point_comparison_bound request fixed other refines first otherFirst firstEq
  have lastBound := point_comparison_bound request fixed other refines last otherLast lastEq
  have decomposition : (fixed.values last - fixed.values first) -
      (other.values otherLast - other.values otherFirst) =
      (fixed.values last - other.values otherLast) - (fixed.values first - other.values otherFirst) := by ring1
  rewrite [decomposition]
  have estimate := Norm.Bounds.normSq_sub_le_two
    (fixed.values last - other.values otherLast) (fixed.values first - other.values otherFirst)
  have total := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct lastBound firstBound)
    (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 2)
  exact estimate.trans (total.trans_eq (by ring1))

end Comparisons

open Purelib in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
/-- Matching original point and mesh coordinates have readings within four retained global bounds. -/
theorem point_reading_bound (request : GridPrimitiveAccuracy bounds columns target pairs)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator pairs} {anchors :
      PrimitiveAnchors primitives}
    {offsets : LinearAlgebra.Grid.Offsets anchors.edges} {points : Fin count → Gaussian}
    (fixed : PointReadings anchors offsets points) {triangles : List (ModelTriangle geometry)}
    {surface : OwnedTriangulation triangles} (readings : SharedPrimitiveValues anchors offsets surface)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (point : Fin count) (vertex : Fin surface.mesh.vertices.length) (equal : surface.mesh.coordinate vertex = points
      point) :
    normSq (readings.values vertex - fixed.values point) ≤ 4 * request.globalBound := by
  have inside : (geometry.box (fixed.owners point).column (fixed.owners point).row).Contains (surface.mesh.coordinate
    vertex) :=
    ((fixed.point_eq point).trans equal.symm) ▸ (fixed.owners point).contains
  rw [fixed.value_eq, fixed.point_eq, ← equal]
  exact RectangularSharedPrimitives.GridPrimitiveAccuracy.shared_value_bound request readings refines _ _ vertex inside

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Branches in
/-- Matching original endpoint pairs have reading increments within sixteen retained global bounds.

Both point indices and mesh vertex indices remain original, and their two exact coordinate equalities determine the
comparison. -/
theorem point_increment_bound (request : GridPrimitiveAccuracy bounds columns target pairs)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator pairs} {anchors :
      PrimitiveAnchors primitives}
    {offsets : LinearAlgebra.Grid.Offsets anchors.edges} {points : Fin count → Gaussian}
    (fixed : PointReadings anchors offsets points) {triangles : List (ModelTriangle geometry)}
    {surface : OwnedTriangulation triangles} (readings : SharedPrimitiveValues anchors offsets surface)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (first last : Fin count) (firstVertex lastVertex : Fin surface.mesh.vertices.length)
    (firstEq : surface.mesh.coordinate firstVertex = points first) (lastEq : surface.mesh.coordinate lastVertex = points
      last) :
    normSq ((fixed.values last - fixed.values first) - (readings.values lastVertex - readings.values firstVertex)) ≤
      16 * request.globalBound := by
  have identity : (fixed.values last - fixed.values first) - (readings.values lastVertex - readings.values firstVertex)
    =
      (readings.values firstVertex - fixed.values first) - (readings.values lastVertex - fixed.values last) := by ring1
  rw [identity]
  have scalarEstimate := Norm.Bounds.normSq_sub_le_two
    (readings.values firstVertex - fixed.values first) (readings.values lastVertex - fixed.values last)
  simp only [Norm.Basic.normSq_eq_canonical] at scalarEstimate
  exact scalarEstimate.trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (point_reading_bound request fixed readings refines first firstVertex firstEq)
        (point_reading_bound request fixed readings refines last lastVertex lastEq)) (by decide)).trans_eq (by ring1))

end GridPrimitiveAccuracy
end Purelib.Riemann.Readings.RectangularPointReadings

end

public section

namespace Purelib.Riemann.Readings.RectangularPointReadings.PointReadings

variable {pairs : Nat}

open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)

variable {polynomial numerator : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator pairs}

/-- Forward the actual mesh owners and cached values as its point-reading bank.

The original vertex coordinate family and primitive bank remain the indices.
Every owner and numerical value is the supplied retained vector; no primitive
is evaluated and no cell owner is selected again.
-/
def ofMesh {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
    {triangles : List (ModelTriangle geometry)} {surface : OwnedTriangulation triangles}
    (readings : SharedPrimitiveValues anchors offsets surface) :
    PointReadings anchors offsets surface.mesh.coordinate :=
  ⟨surface.owners, surface.point_eq, readings.values, readings.value_eq⟩

/-- The mesh view forwards its complete original owner vector. -/
theorem owners_ofMesh {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
    {triangles : List (ModelTriangle geometry)} {surface : OwnedTriangulation triangles}
    (readings : SharedPrimitiveValues anchors offsets surface) :
    (ofMesh readings).owners = surface.owners := (rfl)

/-- The mesh view forwards its complete original primitive-reading vector. -/
theorem values_ofMesh {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
    {triangles : List (ModelTriangle geometry)} {surface : OwnedTriangulation triangles}
    (readings : SharedPrimitiveValues anchors offsets surface) :
    (ofMesh readings).values = readings.values := (rfl)

end Purelib.Riemann.Readings.RectangularPointReadings.PointReadings

end
