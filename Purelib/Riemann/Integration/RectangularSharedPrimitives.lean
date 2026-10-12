module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
public import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Branches.RectangularSheetGauge

import Purelib.Geometry.Rectangle.Partition.RectangularOverlapGeometry
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
public import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveOverlap
public import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Shared finite primitive readings across independently modeled cells

The vertex owner selects one cached aligned primitive reading.  Every face
uses those same indexed readings, so internal edges cancel exactly even
when adjacent local polynomials only agree approximately.  The local Taylor
estimate pays both endpoint ownership errors explicitly.  This is a regular
patch construction; identification with the global A/B boundary remains a
separate geometric obligation.
-/

namespace Purelib.Riemann.Integration.RectangularSharedPrimitives

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Normalization.RectangularInverseModels (Transitions)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Riemann.Topology.PreparedSurfaceCoercivity (AffineSurfaceSample)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

open Purelib in
open Purelib.Data in
set_option genInjectivity false in
/-- Cached primitive readings at the exact retained mesh vertex owners.

Each value is evaluated through its original cell anchor and offset; the vector length and readback equations retain the
original owned triangulation. -/
structure SharedPrimitiveValues {polynomial numerator : Polynomial} {columns rows : Nat}
    {geometry : Geometry columns rows} {models : Bank polynomial geometry}
    {primitives : Primitives models numerator} (anchors : PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges) {triangles : List (ModelTriangle geometry)}
    (surface : OwnedTriangulation triangles) where
  /-- The retained primitive-reading vector indexed by original mesh vertices. -/ values : Data.Vector Gaussian
    surface.mesh.vertices.length
  /-- Each cached reading equals the aligned primitive at its exact retained original owner and coordinate. -/ value_eq
    : ∀ vertex, values vertex = anchors.alignedValue offsets
    (surface.owners vertex).column (surface.owners vertex).row (surface.owners vertex).point

constructive_injectivity SharedPrimitiveValues

namespace SharedPrimitiveValues

variable {polynomial numerator : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator}
    {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
    {triangles : List (ModelTriangle geometry)} {surface : OwnedTriangulation triangles}

open Purelib in
open Purelib.Data in
/-- Cache each original mesh vertex's aligned primitive value using its retained cell owner. -/
def build (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (surface : OwnedTriangulation triangles) : SharedPrimitiveValues anchors offsets surface where
  values := Vector.Basic.vectorOfFn fun vertex => anchors.alignedValue offsets
    (surface.owners vertex).column (surface.owners vertex).row (surface.owners vertex).point
  value_eq := fun vertex => Vector.Basic.vectorOfFn_apply _ vertex

/-- Equal original mesh coordinates give equal retained shared primitive readings. -/
theorem coordinate_consistent (readings : SharedPrimitiveValues anchors offsets surface)
    (first last : Fin surface.mesh.vertices.length) (equal : surface.mesh.coordinate first = surface.mesh.coordinate
      last) :
    readings.values first = readings.values last := by
  have owners := surface.owner_consistent first last equal
  rw [readings.value_eq, readings.value_eq, surface.point_eq, surface.point_eq, owners.1, owners.2, equal]

open Purelib.Geometry.Rectangle.Partition in
/-- A strictly interior original cell reads the shared value through that exact unique owner. -/
theorem value_eq_of_strictInside (readings : SharedPrimitiveValues anchors offsets surface)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (vertex : Fin surface.mesh.vertices.length)
    (inside : (geometry.box column row).StrictContains (surface.mesh.coordinate vertex)) :
    readings.values vertex = anchors.alignedValue offsets column row (surface.mesh.coordinate vertex) := by
  have owners := Geometry.Rectangle.Partition.RectangularOverlapGeometry.unique_owner geometry column (surface.owners
      vertex).column row
    (surface.owners vertex).row
    inside (surface.owner_inside vertex)
  rw [readings.value_eq, surface.point_eq, ← owners.1, ← owners.2]

open Purelib.Data in
/-- Read each original face's coefficient at its first vertex using the retained source-cell owner. -/
def faceCoefficients (_readings : SharedPrimitiveValues anchors offsets surface) :
    Data.Vector Gaussian (triangles.map ModelTriangle.triangle).length :=
  Vector.Basic.vectorOfFn fun face =>
    let source := surface.faceSource face
    (primitives.cells source.column source.row).coefficient.eval
      (surface.mesh.coordinate (surface.mesh.triangulation.faces face).first)

open Purelib.Riemann.Topology in
/-- Construct an affine surface sample from the retained vertex readings and exact face coefficients.

The original triangulation and coordinates remain the source geometry, while the positive radius is retained by the
affine sample constructor. -/
def sample (readings : SharedPrimitiveValues anchors offsets surface) (radius : Coordinate)
    (positive : 0 < radius) :
    PreparedSurfaceCoercivity.AffineSurfaceSample surface.mesh.vertices.length (triangles.map
      ModelTriangle.triangle).length :=
  let coefficients := readings.faceCoefficients
  PreparedSurfaceCoercivity.AffineSurfaceSample.ofVertices surface.mesh.triangulation surface.mesh.coordinate
    (fun vertex => readings.values vertex) (fun face => coefficients face) radius positive

end SharedPrimitiveValues

namespace GridPrimitiveAccuracy

variable {polynomial numerator : Polynomial} {ambient : Box} {clearance : RegionClearance polynomial ambient}
    {bounds : PrimitiveOverlapBounds clearance numerator} {columns rows : Nat} {target : Coordinate}
    {geometry : Geometry columns rows} {bank : Bank polynomial geometry}

open Purelib in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
/-- A shared vertex reading differs from any containing original cell reading by at most four global bounds. -/
theorem shared_value_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} {anchors :
      PrimitiveAnchors primitives}
    {offsets : LinearAlgebra.Grid.Offsets anchors.edges} {triangles : List (ModelTriangle geometry)}
    {surface : OwnedTriangulation triangles} (readings : SharedPrimitiveValues anchors offsets surface)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (vertex : Fin surface.mesh.vertices.length)
    (inside : (geometry.box column row).Contains (surface.mesh.coordinate vertex)) :
    normSq (readings.values vertex - anchors.alignedValue offsets column row (surface.mesh.coordinate vertex)) ≤ 4 *
      request.globalBound := by
  rw [readings.value_eq, surface.point_eq]
  exact RectangularPrimitiveAccuracy.GridPrimitiveAccuracy.overlap_bound request anchors offsets refines _ _ _ _
    (surface.owner_inside vertex) inside

section
open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Riemann.Branches
/-- A retained shared increment differs from the original containing-cell primitive increment by at most sixteen global
bounds. -/
theorem shared_local_increment_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} {anchors :
      PrimitiveAnchors primitives}
    {offsets : LinearAlgebra.Grid.Offsets anchors.edges} {triangles : List (ModelTriangle geometry)}
    {surface : OwnedTriangulation triangles} (readings : SharedPrimitiveValues anchors offsets surface)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (first last : Fin surface.mesh.vertices.length)
    (firstInside : (geometry.box column row).Contains (surface.mesh.coordinate first))
    (lastInside : (geometry.box column row).Contains (surface.mesh.coordinate last)) :
    normSq ((readings.values last - readings.values first) -
      (primitives.value column row (surface.mesh.coordinate last) - primitives.value column row (surface.mesh.coordinate
        first))) ≤
      16 * request.globalBound := by
  let firstError := readings.values first - anchors.alignedValue offsets column row (surface.mesh.coordinate first)
  let lastError := readings.values last - anchors.alignedValue offsets column row (surface.mesh.coordinate last)
  have firstBound := shared_value_bound request readings refines column row first firstInside
  have lastBound := shared_value_bound request readings refines column row last lastInside
  have identity : (readings.values last - readings.values first) -
      (primitives.value column row (surface.mesh.coordinate last) - primitives.value column row (surface.mesh.coordinate
        first)) =
      lastError - firstError := by
    dsimp only [lastError, firstError, PrimitiveAnchors.alignedValue]
    ring1
  rw [identity]
  have scalarEstimate := Norm.Bounds.normSq_sub_le_two lastError firstError
  simp only [Norm.Basic.normSq_eq_canonical] at scalarEstimate
  exact scalarEstimate.trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add lastBound firstBound) (by decide)).trans_eq
      (by ring1))

/-- A retained shared increment satisfies the original cell coefficient estimate with paid gluing and remainder terms.

The same cell contains both original endpoints, and its exact primitive remainder is combined with their shared-reading
error. -/
theorem shared_increment_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} {anchors :
      PrimitiveAnchors primitives}
    {offsets : LinearAlgebra.Grid.Offsets anchors.edges} {triangles : List (ModelTriangle geometry)}
    {surface : OwnedTriangulation triangles} (readings : SharedPrimitiveValues anchors offsets surface)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (first last : Fin surface.mesh.vertices.length)
    (firstInside : (geometry.box column row).Contains (surface.mesh.coordinate first))
    (lastInside : (geometry.box column row).Contains (surface.mesh.coordinate last)) :
    normSq (readings.values last - readings.values first -
      (primitives.cells column row).coefficient.eval (surface.mesh.coordinate first) *
        (surface.mesh.coordinate last - surface.mesh.coordinate first)) ≤
      32 * request.globalBound + 2 * (primitives.cells column row).remainderBound *
        normSq (surface.mesh.coordinate last - surface.mesh.coordinate first) ^ 2 := by
  let start := surface.mesh.coordinate first
  let finish := surface.mesh.coordinate last
  let endpointError := (readings.values last - readings.values first) -
    (primitives.value column row finish - primitives.value column row start)
  let taylor := primitives.value column row finish - primitives.value column row start -
    (primitives.cells column row).coefficient.eval start * (finish - start)
  have endpoints := shared_local_increment_bound request readings refines column row first last firstInside lastInside
  have taylorBound := (primitives.dense column row).increment_bound firstInside lastInside
  dsimp only [Primitives.dense] at taylorBound
  simp only [Norm.Basic.normSq_eq_canonical] at taylorBound
  have identity : readings.values last - readings.values first -
      (primitives.cells column row).coefficient.eval start * (finish - start) =
        endpointError + taylor := by
    dsimp only [endpointError, taylor]
    ring1
  rw [identity]
  have scalarEstimate := Norm.Bounds.normSq_add_le_two endpointError taylor
  simp only [Norm.Basic.normSq_eq_canonical] at scalarEstimate
  exact scalarEstimate.trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add endpoints taylorBound) (by
      decide)).trans_eq (by ring1))

end

open Purelib in
open Purelib.Data in
open Purelib.Riemann.Branches in
/-- Both original first-vertex face increments satisfy the retained shared coefficient and remainder bounds. -/
theorem shared_face_increment_bounds (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} {anchors :
      PrimitiveAnchors primitives}
    {offsets : LinearAlgebra.Grid.Offsets anchors.edges} {triangles : List (ModelTriangle geometry)}
    {surface : OwnedTriangulation triangles} (readings : SharedPrimitiveValues anchors offsets surface)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (face : Fin (triangles.map ModelTriangle.triangle).length) :
    let source := surface.faceSource face
    let indexed := surface.mesh.triangulation.faces face
    let start := surface.mesh.coordinate indexed.first
    let second := surface.mesh.coordinate indexed.second
    let third := surface.mesh.coordinate indexed.third
    let remainder := (primitives.cells source.column source.row).remainderBound
    normSq (readings.values indexed.second - readings.values indexed.first -
      readings.faceCoefficients face * (second - start)) ≤
        32 * request.globalBound + 2 * remainder * normSq (second - start) ^ 2 ∧
    normSq (readings.values indexed.third - readings.values indexed.first -
      readings.faceCoefficients face * (third - start)) ≤
        32 * request.globalBound + 2 * remainder * normSq (third - start) ^ 2 := by
  have inside := surface.face_inside face
  dsimp only [SharedPrimitiveValues.faceCoefficients]
  rw [Vector.Basic.vectorOfFn_apply]
  exact ⟨shared_increment_bound request readings refines _ _ _ _ inside.1 inside.2.1,
    shared_increment_bound request readings refines _ _ _ _ inside.1 inside.2.2⟩

end GridPrimitiveAccuracy

end Purelib.Riemann.Integration.RectangularSharedPrimitives
