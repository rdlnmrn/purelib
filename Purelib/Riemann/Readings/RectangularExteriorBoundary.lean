module
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Topology.Polygon.Stokes
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Energy.Polygon
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Normalization.RectangularInverseModels

import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Geometry.Rectangle.Partition.RectangularMeshRefinement
import Purelib.LinearAlgebra.Grid.Offsets
public import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Cancellation from a full refined grid to its four exterior sides

The axes may be nonuniform.  Every exterior side retains the original coarse
cuts, with the same dyadic depth inside each interval.  The proof telescopes
finite indexed sums; it does not assert that this boundary is an A/B word.
-/

namespace Purelib.Riemann.Readings.RectangularExteriorBoundary

open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The exact rational Gaussian carrier. -/
private abbrev Gaussian := Basic.Canonical
open Purelib.Polynomial.Dense.Gaussian in
/-- The original dense Gaussian polynomial carrier. -/
private abbrev Polynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
open Purelib.Riemann.Normalization.RectangularInverseModels (Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedTriangulation)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Readings.RectangularPrimitiveBoundary.Geometry (selectionBoundary)

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary (horizontalBoundary verticalBoundary rectangleBoundary)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ sumFin_congr sumFin_add sumFin_sub sumFin_swap)
open Purelib.Integration.Path.BoundaryRibbon (sum_decreasing sum_increasing)

namespace Geometry

variable {columns rows : Nat}

/-- List every original rectangular cell in column-major order with its exact finite indices. -/
def allCells (_geometry : Geometry columns rows) : List (Fin (columns + 1) × Fin (rows + 1)) :=
  (List.ofFn fun column => List.ofFn fun row => (column, row)).flatten

open Purelib.Data.Gaussian in
open Purelib.Riemann.Readings in
/-- The original selected-cell boundary sum adds over concatenated ordered selections.

Each retained cell contributes its original depth-dependent rectangle boundary.
Structural recursion groups the same ordered contributions from the first
selection before the unchanged second selection. -/
private theorem selectionBoundary_append (geometry : Geometry columns rows) (primitive : Basic.Canonical →
  PrimitivePoint)
    (depth : Nat) (first last : List (Fin (columns + 1) × Fin (rows + 1))) :
    RectangularPrimitiveBoundary.Geometry.selectionBoundary geometry primitive depth (first ++ last) =
      RectangularPrimitiveBoundary.Geometry.selectionBoundary geometry primitive depth first +
        RectangularPrimitiveBoundary.Geometry.selectionBoundary geometry primitive depth last := by
  induction first with
  | nil =>
      simp only [List.nil_append, selectionBoundary, zero_add, -eq_self, -iff_self]
      rfl
  | cons cell rest ih =>
      simp only [List.cons_append, selectionBoundary, ih, add_assoc, -eq_self, -iff_self]
      rfl

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Riemann.Readings in
/-- A finite original cell vector's boundary sum equals its indexed finite sum. -/
private theorem selectionBoundary_ofFn (geometry : Geometry columns rows) (primitive : Basic.Canonical → PrimitivePoint)
    (depth : Nat) {count : Nat} (cells : Fin count → Fin (columns + 1) × Fin (rows + 1)) :
    RectangularPrimitiveBoundary.Geometry.selectionBoundary geometry primitive depth (List.ofFn cells) =
      FiniteSum.Fin.sumFin (fun index => PreparedBoxBoundary.rectangleBoundary primitive depth (geometry.box (cells
        index).1 (cells index).2)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [OfFn.Basic.ofFn_succ, selectionBoundary, FiniteSum.Fin.sumFin_succ, ih]

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Riemann.Readings in
/-- The flattened original selection's boundary sum equals the finite sum of its retained rows. -/
private theorem selectionBoundary_flatten (geometry : Geometry columns rows) (primitive : Basic.Canonical →
  PrimitivePoint)
    (depth : Nat) {count : Nat} (cells : Fin count → List (Fin (columns + 1) × Fin (rows + 1))) :
    RectangularPrimitiveBoundary.Geometry.selectionBoundary geometry primitive depth (List.ofFn cells).flatten =
      FiniteSum.Fin.sumFin (fun index => RectangularPrimitiveBoundary.Geometry.selectionBoundary geometry primitive
        depth (cells index)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [OfFn.Basic.ofFn_succ, List.flatten_cons, selectionBoundary_append, FiniteSum.Fin.sumFin_succ, ih]

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rectangle.Partition
/-- The retained-depth boundary contribution of one original horizontal grid interval at the selected height. -/
def horizontalSide (geometry : Geometry columns rows) (primitive : Basic.Canonical → PrimitivePoint) (depth : Nat)
    (column : Fin (columns + 1)) (height : Fin (rows + 2)) : Basic.Canonical :=
  PreparedBoxBoundary.horizontalBoundary primitive depth (geometry.x.coordinates column.castSucc)
    (geometry.x.coordinates column.succ)
    (geometry.y.coordinates height)

/-- The retained-depth boundary contribution of one original vertical grid interval at the selected horizontal
coordinate. -/
def verticalSide (geometry : Geometry columns rows) (primitive : Basic.Canonical → PrimitivePoint) (depth : Nat)
    (horizontal : Fin (columns + 2)) (row : Fin (rows + 1)) : Basic.Canonical :=
  PreparedBoxBoundary.verticalBoundary primitive depth (geometry.y.coordinates row.castSucc) (geometry.y.coordinates
    row.succ)
    (geometry.x.coordinates horizontal)

end

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Readings in
/-- The original oriented outer boundary sum: bottom plus right minus top minus left.

Every side retains its original axis intervals and the same subdivision depth and primitive readings. -/
def exteriorBoundary (geometry : Geometry columns rows) (primitive : Basic.Canonical → PrimitivePoint) (depth : Nat) :
  Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun column => RectangularExteriorBoundary.Geometry.horizontalSide geometry primitive depth
    column 0) +
    FiniteSum.Fin.sumFin (fun row => RectangularExteriorBoundary.Geometry.verticalSide geometry primitive depth
      (Fin.last (columns + 1)) row) -
    FiniteSum.Fin.sumFin (fun column => RectangularExteriorBoundary.Geometry.horizontalSide geometry primitive depth
      column (Fin.last (rows + 1))) -
    FiniteSum.Fin.sumFin (fun row => RectangularExteriorBoundary.Geometry.verticalSide geometry primitive depth 0 row)

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path in
open Purelib.Riemann.Normalization in
open Purelib.Riemann.Readings in
/-- Summing all original cell boundaries cancels internal sides and gives the exact exterior boundary.

The original column-major selection and finite axis sums preserve every signed side occurrence through the telescoping
calculation. -/
theorem selectionBoundary_allCells (geometry : Geometry columns rows) (primitive : Basic.Canonical → PrimitivePoint)
    (depth : Nat) : RectangularPrimitiveBoundary.Geometry.selectionBoundary geometry primitive depth
      (RectangularExteriorBoundary.Geometry.allCells geometry) =
      RectangularExteriorBoundary.Geometry.exteriorBoundary geometry primitive depth := by
  rw [allCells, selectionBoundary_flatten]
  have cells : FiniteSum.Fin.sumFin (fun column => RectangularPrimitiveBoundary.Geometry.selectionBoundary geometry
    primitive depth (List.ofFn fun row => (column, row))) =
      FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row =>
        (RectangularExteriorBoundary.Geometry.horizontalSide geometry primitive depth column row.castSucc -
          RectangularExteriorBoundary.Geometry.horizontalSide geometry primitive depth column row.succ) +
        (RectangularExteriorBoundary.Geometry.verticalSide geometry primitive depth column.succ row -
          RectangularExteriorBoundary.Geometry.verticalSide geometry primitive depth column.castSucc row))) := by
    apply FiniteSum.Fin.sumFin_congr
    intro column
    rw [selectionBoundary_ofFn]
    apply FiniteSum.Fin.sumFin_congr
    intro row
    dsimp only [PreparedBoxBoundary.rectangleBoundary, RectangularInverseModels.Geometry.box, horizontalSide,
      verticalSide]
    ring1
  rw [cells]
  have split := FiniteSum.Fin.sumFin_congr (fun column : Fin (columns + 1) => FiniteSum.Fin.sumFin_add
    (fun row : Fin (rows + 1) => RectangularExteriorBoundary.Geometry.horizontalSide geometry primitive depth column
      row.castSucc - RectangularExteriorBoundary.Geometry.horizontalSide geometry primitive depth column row.succ)
    (fun row : Fin (rows + 1) => RectangularExteriorBoundary.Geometry.verticalSide geometry primitive depth column.succ
      row - RectangularExteriorBoundary.Geometry.verticalSide geometry primitive depth column.castSucc row))
  rw [split, FiniteSum.Fin.sumFin_add]
  have horizontal : FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row =>
      RectangularExteriorBoundary.Geometry.horizontalSide geometry primitive depth column row.castSucc -
        RectangularExteriorBoundary.Geometry.horizontalSide geometry primitive depth column row.succ)) =
      FiniteSum.Fin.sumFin (fun column => RectangularExteriorBoundary.Geometry.horizontalSide geometry primitive depth
        column 0 -
        RectangularExteriorBoundary.Geometry.horizontalSide geometry primitive depth column (Fin.last (rows + 1))) :=
    FiniteSum.Fin.sumFin_congr (fun column => BoundaryRibbon.sum_decreasing
      (RectangularExteriorBoundary.Geometry.horizontalSide geometry primitive depth column))
  have vertical : FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row =>
      RectangularExteriorBoundary.Geometry.verticalSide geometry primitive depth column.succ row -
        RectangularExteriorBoundary.Geometry.verticalSide geometry primitive depth column.castSucc row)) =
      FiniteSum.Fin.sumFin (fun row => RectangularExteriorBoundary.Geometry.verticalSide geometry primitive depth
        (Fin.last (columns + 1)) row - RectangularExteriorBoundary.Geometry.verticalSide geometry primitive depth 0 row)
        := by
    rw [FiniteSum.Fin.sumFin_swap]
    exact FiniteSum.Fin.sumFin_congr (fun row => BoundaryRibbon.sum_increasing (fun column =>
      RectangularExteriorBoundary.Geometry.verticalSide geometry primitive depth column row))
  rw [horizontal, vertical, FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_sub]
  unfold exteriorBoundary
  ring1

end Geometry

namespace SharedPrimitiveValues

variable {polynomial numerator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {columns
  rows : Nat} {geometry
  : Geometry columns rows}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator}
    {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges} {depth
      : Nat}
    {surface : OwnedTriangulation
      (Geometry.Rectangle.Partition.RectangularMeshRefinement.refineSelection geometry
      (Purelib.Riemann.Readings.RectangularExteriorBoundary.Geometry.allCells geometry) depth)}

open Purelib.Data.Rat in
open Purelib.Integration.Energy in
open Purelib.Riemann.Readings in
/-- The full-grid shared primitive sample boundary equals the exact original exterior boundary sum. -/
theorem sample_boundary_eq_exterior (readings : SharedPrimitiveValues anchors offsets surface)
    (radius : Fraction.Rational) (positive : 0 < radius) :
    (readings.sample radius positive).boundaryArea =
      RectangularExteriorBoundary.Geometry.exteriorBoundary geometry (fun point => Polygon.energyPrimitivePoint
        (RectangularPrimitiveBoundary.SharedPrimitiveValues.atPoint readings point)) depth := by
  rw [RectangularPrimitiveBoundary.SharedPrimitiveValues.sample_boundary_eq_selection readings,
    RectangularExteriorBoundary.Geometry.selectionBoundary_allCells geometry]

end SharedPrimitiveValues

end Purelib.Riemann.Readings.RectangularExteriorBoundary
