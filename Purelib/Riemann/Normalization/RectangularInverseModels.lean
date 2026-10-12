module

import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Normalization.InverseModelOverlap
public import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Affine

public import Purelib.Topology.Grid.Signs
public import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Mathlib.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-!
# Computed sheet gauges for rectangular inverse-model banks

The cells are actual adjacent rational rectangles, with independently
acquired, cached inverse-root polynomials.  Four models meet at every inner
grid vertex.  Their proved triple cocycles make each transition square flat,
so the finite spanning-tree scan produces signs consistent on every shared
edge.  No global sheet-consistency certificate is an input.
-/

namespace Purelib.Riemann.Normalization.RectangularInverseModels

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseModelOverlap (OverlapSample)
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial (OverlapReady)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

/-- The executable finite vector carrier. -/
abbrev Vector := Data.Vector

set_option genInjectivity false in
/-- An ordered finite coordinate axis with strictly increasing consecutive entries.

The coordinates retain their original finite indices. Each adjacent pair
has a stored strict inequality, which supplies the cell-width certificate. -/
structure Axis (steps : Nat) where
  /-- The retained finite coordinate vector of the original axis. -/ coordinates : Vector Coordinate (steps + 2)
  /-- Consecutive original axis coordinates are strictly increasing. -/ ordered : ∀ index : Fin (steps + 1), coordinates
    index.castSucc < coordinates index.succ

constructive_injectivity Axis

set_option genInjectivity false in
/-- A rectangular grid retaining its original horizontal and vertical ordered axes.

The two axes retain their ordered coordinates and original step counts.
Consecutive entries determine every indexed cell and grid vertex. -/
structure Geometry (columns rows : Nat) where
  /-- The original ordered horizontal coordinate axis. -/ x : Axis columns
  /-- The original ordered vertical coordinate axis. -/ y : Axis rows

constructive_injectivity Geometry

namespace Geometry

variable {columns rows : Nat}

/-- The original grid vertex at the retained column and row coordinate indices. -/
@[expose] def vertex (geometry : Geometry columns rows) (column : Fin (columns + 2)) (row : Fin (rows + 2)) : Gaussian
  :=
  ⟨geometry.x.coordinates column, geometry.y.coordinates row⟩

/-- The original cell box between consecutive entries of the retained coordinate axes. -/
@[expose] def box (geometry : Geometry columns rows) (column : Fin (columns + 1)) (row : Fin (rows + 1)) : Box :=
  ⟨geometry.x.coordinates column.castSucc, geometry.x.coordinates column.succ,
    geometry.y.coordinates row.castSucc, geometry.y.coordinates row.succ,
    (geometry.x.ordered column).le, (geometry.y.ordered row).le⟩

/-- Every original rectangular cell has positive width and height. -/
theorem box_proper (geometry : Geometry columns rows) (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    (geometry.box column row).Proper := ⟨geometry.x.ordered column, geometry.y.ordered row⟩

/-- The original lower-left cell vertex belongs to its cell box. -/
theorem lowerLeft_mem (geometry : Geometry columns rows) (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    (geometry.box column row).Contains (geometry.vertex column.castSucc row.castSucc) :=
  ⟨le_rfl, (geometry.x.ordered column).le, le_rfl, (geometry.y.ordered row).le⟩

/-- The original lower-right cell vertex belongs to its cell box. -/
theorem lowerRight_mem (geometry : Geometry columns rows) (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    (geometry.box column row).Contains (geometry.vertex column.succ row.castSucc) :=
  ⟨(geometry.x.ordered column).le, le_rfl, le_rfl, (geometry.y.ordered row).le⟩

/-- The original upper-left cell vertex belongs to its cell box. -/
theorem upperLeft_mem (geometry : Geometry columns rows) (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    (geometry.box column row).Contains (geometry.vertex column.castSucc row.succ) :=
  ⟨le_rfl, (geometry.x.ordered column).le, (geometry.y.ordered row).le, le_rfl⟩

/-- The original upper-right cell vertex belongs to its cell box. -/
theorem upperRight_mem (geometry : Geometry columns rows) (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    (geometry.box column row).Contains (geometry.vertex column.succ row.succ) :=
  ⟨(geometry.x.ordered column).le, le_rfl, (geometry.y.ordered row).le, le_rfl⟩

end Geometry

set_option genInjectivity false in
/-- A retained box and overlap-ready inverse-root model for the original polynomial.

The retained model belongs to the supplied polynomial on that exact box.
Its overlap-ready evidence remains attached to the same cached model. -/
structure CachedCell (polynomial : Polynomial) where
  /-- The retained original cell box. -/ box : Box
  /-- The overlap-ready inverse-root model on the exact retained box. -/ ready : OverlapReady polynomial box

constructive_injectivity CachedCell

set_option genInjectivity false in
/-- A rectangular bank of retained inverse-root cells with exact original geometric box identities.

Each cached cell remains indexed by its original column and row, and its box equals the corresponding original geometry
cell. -/
structure Bank (polynomial : Polynomial) {columns rows : Nat} (geometry : Geometry columns rows) where
  /-- The cached inverse-root cells indexed by original column and row. -/ cells : Vector (Vector (CachedCell
    polynomial) (rows + 1)) (columns + 1)
  /-- Each cached cell box equals its exact original geometric cell box. -/ box_eq : ∀ column row, (cells column
    row).box = geometry.box column row

constructive_injectivity Bank

namespace Bank

variable {polynomial : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}

/-- Transport the retained cell model along its exact original geometric box identity. -/
@[expose] def ready (bank : Bank polynomial geometry) (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    OverlapReady polynomial (geometry.box column row) :=
  (bank.box_eq column row) ▸ (bank.cells column row).ready

section
open Purelib.Data
/-- Cache the original indexed inverse-root models with their exact geometric cell boxes. -/
@[expose] def ofFn (models : ∀ column row, OverlapReady polynomial (geometry.box column row)) : Bank polynomial geometry
  where
  cells := Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row => ⟨geometry.box column row, models
    column row⟩
  box_eq := fun column row => by rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]

/-- Reading a freshly cached bank returns the exact original indexed model. -/
theorem ready_ofFn (models : ∀ column row, OverlapReady polynomial (geometry.box column row))
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) : (ofFn models).ready column row = models column row := by
  have cast_eq (cell : CachedCell polynomial) (boxEq : cell.box = geometry.box column row)
      (equal : cell = ⟨geometry.box column row, models column row⟩) : boxEq ▸ cell.ready = models column row := by
    cases equal
    rfl
  apply cast_eq
  change Vector.Basic.vectorOfFn (fun column => Vector.Basic.vectorOfFn fun row =>
    (⟨geometry.box column row, models column row⟩ : CachedCell polynomial)) column row = _
  rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]

end

open Purelib.Approximation.Rational in
/-- Refine an original overlap-ready model while retaining its polynomial, box and smallness bound. -/
@[expose] def refineReady {box : Box} (ready : OverlapReady polynomial box) (index : Nat) : OverlapReady polynomial box
  :=
  ⟨ready.model.refine index,
    ((ready.model.refine_bound index).trans_le
      (Geometric.Basic.quarterRadius_le_scale ready.model.bound_nonnegative index)).trans ready.small⟩

/-- Refine each original indexed cell model at the same geometric depth. -/
@[expose] def refine (bank : Bank polynomial geometry) (index : Nat) : Bank polynomial geometry :=
  .ofFn fun column row => refineReady (bank.ready column row) index

open Purelib.Approximation.Rational in
/-- The refined cell's bound is the exact quarter-radius refinement of its original bound. -/
theorem refine_bound (bank : Bank polynomial geometry) (index : Nat)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    ((bank.refine index).ready column row).model.bound =
      Geometric.Basic.quarterRadius (bank.ready column row).model.bound index := by
  rw [refine, ready_ofFn]
  exact (bank.ready column row).model.refine_bound index

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- Each refined original cell satisfies the common quarter-radius bound from one over 256. -/
theorem refine_uniform_bound (bank : Bank polynomial geometry) (index : Nat)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    ((bank.refine index).ready column row).model.bound ≤ Geometric.Basic.quarterRadius (1 / 256) index := by
  rw [bank.refine_bound, Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (bank.ready column row).small
    (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) index)

/-- The retained inverse-root transition across the common vertical edge of adjacent columns. -/
@[expose] def horizontalEdge (bank : Bank polynomial geometry) (column : Fin columns) (row : Fin (rows + 1)) :
    EdgeTransition (bank.ready column.castSucc row).model (bank.ready column.succ row).model
      (geometry.vertex column.castSucc.succ row.castSucc) (geometry.vertex column.castSucc.succ row.succ) :=
  .build _ _ _ _ (geometry.lowerRight_mem column.castSucc row) (geometry.upperRight_mem column.castSucc row)
    (geometry.lowerLeft_mem column.succ row) (geometry.upperLeft_mem column.succ row)

/-- The retained inverse-root transition across the common horizontal edge of adjacent rows. -/
@[expose] def verticalEdge (bank : Bank polynomial geometry) (column : Fin (columns + 1)) (row : Fin rows) :
    EdgeTransition (bank.ready column row.castSucc).model (bank.ready column row.succ).model
      (geometry.vertex column.castSucc row.castSucc.succ) (geometry.vertex column.succ row.castSucc.succ) :=
  .build _ _ _ _ (geometry.upperLeft_mem column row.castSucc) (geometry.upperRight_mem column row.castSucc)
    (geometry.lowerLeft_mem column row.succ) (geometry.lowerRight_mem column row.succ)

end Bank

set_option genInjectivity false in
/-- Cached adjacent-cell alignment signs for the same original rectangular inverse-model bank.

Both sign vectors retain exact equations to the original edge-transition samples, preserving their column and row
indices. -/
structure Transitions {polynomial : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
    (bank : Bank polynomial geometry) where
  /-- The cached signs across adjacent original columns. -/ horizontal : Vector (Vector Bool (rows + 1)) columns
  /-- The cached signs across adjacent original rows. -/ vertical : Vector (Vector Bool rows) (columns + 1)
  /-- Each horizontal adjacency cache equals its original edge sample's alignment sign. -/ horizontal_eq : ∀ column row,
    horizontal column row = (bank.horizontalEdge column row).sample.alignment.flip
  /-- Each vertical adjacency cache equals its original edge sample's alignment sign. -/ vertical_eq : ∀ column row,
    vertical column row = (bank.verticalEdge column row).sample.alignment.flip

constructive_injectivity Transitions

namespace Transitions

variable {polynomial : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
    {bank : Bank polynomial geometry}

open Purelib.Data in
/-- Cache the original bank's horizontal and vertical edge-alignment signs. -/
@[expose] def build (bank : Bank polynomial geometry) : Transitions bank where
  horizontal := Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row => (bank.horizontalEdge column
    row).sample.alignment.flip
  vertical := Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row => (bank.verticalEdge column
    row).sample.alignment.flip
  horizontal_eq := fun column row => by rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
  vertical_eq := fun column row => by rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]

section
open Purelib.Geometry.Rational
/-- The cached horizontal adjacency sign equals alignment at every point on its original common edge. -/
theorem horizontal_at (transitions : Transitions bank) (column : Fin columns) (row : Fin (rows + 1))
    {parameter : Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    transitions.horizontal column row =
      (OverlapSample.build (bank.ready column.castSucc row).model (bank.ready column.succ row).model
        (Affine.line (geometry.vertex column.castSucc.succ row.castSucc)
          (geometry.vertex column.castSucc.succ row.succ - geometry.vertex column.castSucc.succ row.castSucc)
            parameter)).alignment.flip :=
  (transitions.horizontal_eq column row).trans ((bank.horizontalEdge column row).flip_eq_at inside)

/-- The cached vertical adjacency sign equals alignment at every point on its original common edge. -/
theorem vertical_at (transitions : Transitions bank) (column : Fin (columns + 1)) (row : Fin rows)
    {parameter : Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    transitions.vertical column row =
      (OverlapSample.build (bank.ready column row.castSucc).model (bank.ready column row.succ).model
        (Affine.line (geometry.vertex column.castSucc row.castSucc.succ)
          (geometry.vertex column.succ row.castSucc.succ - geometry.vertex column.castSucc row.castSucc.succ)
            parameter)).alignment.flip :=
  (transitions.vertical_eq column row).trans ((bank.verticalEdge column row).flip_eq_at inside)

end

/-- The retained transition signs satisfy the XOR square identity at every original grid junction.

Two overlap cocycle identities at the shared original vertex equate the two adjacent-cell routes. -/
theorem square (transitions : Transitions bank) (column : Fin columns) (row : Fin rows) :
    (transitions.horizontal column row.castSucc ^^ transitions.vertical column.succ row) =
      (transitions.vertical column.castSucc row ^^ transitions.horizontal column row.succ) := by
  let point := geometry.vertex column.castSucc.succ row.castSucc.succ
  let bottomLeft := bank.ready column.castSucc row.castSucc
  let bottomRight := bank.ready column.succ row.castSucc
  let topLeft := bank.ready column.castSucc row.succ
  let topRight := bank.ready column.succ row.succ
  have first := OverlapReady.cocycle bottomLeft bottomRight topRight
    (geometry.upperRight_mem column.castSucc row.castSucc)
    (geometry.upperLeft_mem column.succ row.castSucc)
    (geometry.lowerLeft_mem column.succ row.succ)
    (OverlapSample.build bottomLeft.model bottomRight.model point)
    (OverlapSample.build bottomRight.model topRight.model point)
    (OverlapSample.build bottomLeft.model topRight.model point)
  have second := OverlapReady.cocycle bottomLeft topLeft topRight
    (geometry.upperRight_mem column.castSucc row.castSucc)
    (geometry.lowerRight_mem column.castSucc row.succ)
    (geometry.lowerLeft_mem column.succ row.succ)
    (OverlapSample.build bottomLeft.model topLeft.model point)
    (OverlapSample.build topLeft.model topRight.model point)
    (OverlapSample.build bottomLeft.model topRight.model point)
  have xor_eq (left right : Bool) : (if left then !right else right) = (left ^^ right) := by
    cases left <;> cases right <;> rfl
  rw [xor_eq] at first second
  rw [transitions.horizontal_eq, transitions.vertical_eq, transitions.vertical_eq, transitions.horizontal_eq,
    (bank.horizontalEdge column row.castSucc).flip_eq_finish,
    (bank.verticalEdge column.castSucc row).flip_eq_finish]
  exact first.symm.trans second

open Purelib
/-- The flat sign grid carried by the exact retained transition vectors and square identities. -/
@[expose] def flatGrid (transitions : Transitions bank) : Topology.Grid.Signs.FlatGrid columns rows :=
  ⟨transitions.horizontal, transitions.vertical, transitions.square⟩

/-- Construct the sign gauge of the original retained transition grid with the selected initial sign. -/
@[expose] def gauge (transitions : Transitions bank) (initial : Bool := false) : Topology.Grid.Signs.Gauge
  transitions.flatGrid :=
  .build transitions.flatGrid initial

end Transitions

end Purelib.Riemann.Normalization.RectangularInverseModels
