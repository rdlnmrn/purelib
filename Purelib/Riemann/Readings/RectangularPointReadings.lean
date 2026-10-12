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
    {geometry : Geometry columns rows} {models : Bank polynomial geometry} {primitives : Primitives models numerator}
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
    {models : Bank polynomial geometry} {primitives : Primitives models numerator}

open Purelib in
open Purelib.Data in
/-- Cache the original finite point family's aligned readings using the supplied exact cell owners. -/
def build (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (points : Fin count → Gaussian) (owners : Data.Vector (OwnedVertex geometry) count)
    (pointEq : ∀ index, (owners index).point = points index) : PointReadings anchors offsets points :=
  ⟨owners, pointEq, Vector.Basic.vectorOfFn fun index => anchors.alignedValue offsets
    (owners index).column (owners index).row (owners index).point, Vector.Basic.vectorOfFn_apply _⟩

end PointReadings

namespace GridPrimitiveAccuracy

variable {polynomial numerator : Polynomial} {ambient : Box} {clearance : RegionClearance polynomial ambient}
    {bounds : PrimitiveOverlapBounds clearance numerator} {columns rows count : Nat} {target : Coordinate}
    {geometry : Geometry columns rows} {bank : Bank polynomial geometry}

open Purelib in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
/-- Matching original point and mesh coordinates have readings within four retained global bounds. -/
theorem point_reading_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} {anchors :
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
theorem point_increment_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} {anchors :
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
