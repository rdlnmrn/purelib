module
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.Nat.Multiplication
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Segment

import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
public import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

/-!
# Whole-edge fragments contained in two retained rectangular grids

Split by the first cached grid, then split each retained piece by the second.
Both preparations survive in the result. The flattened fragments cache their
two cell owners and endpoints; their exact telescope and finite count include
all pieces, including stationary, reversed and boundary-aligned edges.
-/

namespace Purelib.Riemann.Paths.RectangularPairedSegments

public section

open Purelib.Data.List
open Purelib.Data.Nat

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts SegmentPiece SegmentSplit)
open Purelib.Riemann.Branches
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {leftColumns leftRows rightColumns rightRows : Nat}
  {leftGeometry : Geometry leftColumns leftRows} {rightGeometry : Geometry rightColumns rightRows}

set_option genInjectivity false in
/-- A directed segment retaining containing cell owners in both original rectangular geometries.

The same two endpoint values carry separate containment certificates for the retained left and right cell indices. -/
structure PairedSegmentPiece (leftGeometry : Geometry leftColumns leftRows)
    (rightGeometry : Geometry rightColumns rightRows) where
  /-- The retained original left-grid cell-column index. -/ leftColumn : Fin (leftColumns + 1)
  /-- The retained original left-grid cell-row index. -/ leftRow : Fin (leftRows + 1)
  /-- The retained original right-grid cell-column index. -/ rightColumn : Fin (rightColumns + 1)
  /-- The retained original right-grid cell-row index. -/ rightRow : Fin (rightRows + 1)
  /-- The original directed piece's first point. -/ first : Gaussian
  /-- The original directed piece's last point. -/ last : Gaussian
  /-- The retained first point belongs to the original left cell. -/ leftFirst : (leftGeometry.box leftColumn
    leftRow).Contains first
  /-- The retained last point belongs to the original left cell. -/ leftLast : (leftGeometry.box leftColumn
    leftRow).Contains last
  /-- The retained first point belongs to the original right cell. -/ rightFirst : (rightGeometry.box rightColumn
    rightRow).Contains first
  /-- The retained last point belongs to the original right cell. -/ rightLast : (rightGeometry.box rightColumn
    rightRow).Contains last

constructive_injectivity PairedSegmentPiece

open Purelib.Geometry.Rational in
open Purelib.Geometry.Rectangle.Partition in
/-- Retain both original cell owners for a right-grid subdivision of an original left-grid piece.

The right subdivision supplies its exact endpoints and containing cell. Original interval bounds prove that these same
points remain in the retained left cell, preserving both owners. -/
@[expose] def pairedPiece {first last : Gaussian} (left : SegmentPiece leftGeometry first last)
    (right : SegmentPiece rightGeometry left.firstPoint left.lastPoint) : PairedSegmentPiece leftGeometry rightGeometry
      := by
  have inside (parameter : Coordinate) (within : 0 ≤ parameter ∧ parameter ≤ 1) :
      (leftGeometry.box left.column left.row).Contains (PreparedSegmentCuts.point left.firstPoint left.lastPoint
        parameter) := by
    rw [PreparedSegmentCuts.point_eq_line]
    exact Box.contains_line left.first_inside left.last_inside within
  exact ⟨left.column, left.row, right.column, right.row, right.firstPoint, right.lastPoint,
    right.first_eq.symm ▸ inside right.interval.lower
      ⟨right.within.1, right.interval.ordered.le.trans right.within.2⟩,
    right.last_eq.symm ▸ inside right.interval.upper
      ⟨right.within.1.trans right.interval.ordered.le, right.within.2⟩,
    right.first_inside, right.last_inside⟩

set_option genInjectivity false in
/-- Ordered right-grid splits indexed by the exact original left-grid piece list.

Each row retains the original left piece endpoints as the right split's endpoints, preserving the complete original list
dependency. -/
inductive PairedSegmentRows (rightCuts : GridCuts rightGeometry) {first last : Gaussian} :
    List (SegmentPiece leftGeometry first last) → Type
  /-- The empty original left-piece list has no retained subdivision rows. -/ | nil : PairedSegmentRows rightCuts []
  /-- Retain the exact right-grid split of the original head piece and the dependent tail rows. -/ | cons {piece rest}
    (split : SegmentSplit rightCuts piece.firstPoint piece.lastPoint)
      (tail : PairedSegmentRows rightCuts rest) : PairedSegmentRows rightCuts (piece :: rest)

constructive_injectivity PairedSegmentRows

namespace PairedSegmentRows

variable {rightCuts : GridCuts rightGeometry} {first last : Gaussian}

open Purelib.Riemann.Paths in
/-- Split each original left-grid piece by the retained right-grid cuts in list order.

Each right split uses the original left piece endpoints and their retained coverage witnesses. Structural recursion
stores the resulting row before the unchanged dependent tail. -/
@[expose] def build (rightCuts : GridCuts rightGeometry) (firstInside : RectangularSegmentSplitting.Geometry.Covers
  rightGeometry first)
    (lastInside : RectangularSegmentSplitting.Geometry.Covers rightGeometry last) :
    (pieces : List (SegmentPiece leftGeometry first last)) → PairedSegmentRows rightCuts pieces
  | [] => .nil
  | piece :: rest =>
      let split := SegmentSplit.build rightCuts piece.firstPoint piece.lastPoint
        (piece.first_eq.symm ▸ RectangularSegmentSplitting.Geometry.covers_point rightGeometry firstInside lastInside
          ⟨piece.within.1, piece.interval.ordered.le.trans piece.within.2⟩)
        (piece.last_eq.symm ▸ RectangularSegmentSplitting.Geometry.covers_point rightGeometry firstInside lastInside
          ⟨piece.within.1.trans piece.interval.ordered.le, piece.within.2⟩)
      .cons split (build rightCuts firstInside lastInside rest)

/-- Flatten the retained right-grid rows into their exact doubly owned original pieces.

Each row maps its original right split through the same two-owner construction. Concatenation retains the original row
order and every occurrence in the tail. -/
@[expose] def pieces : {source : List (SegmentPiece leftGeometry first last)} → PairedSegmentRows rightCuts source →
    List (PairedSegmentPiece leftGeometry rightGeometry)
  | _, .nil => []
  | _, .cons (piece := piece) split tail => split.pieces.map (pairedPiece piece) ++ pieces tail

open Purelib.Data.Gaussian in
/-- The finite Gaussian sum of concatenated lists is the sum of their original finite sums. -/
private theorem sum_append (first last : List Gaussian) : Data.Gaussian.Norm.Sum.Basic.gaussianSum (first ++ last) =
  Data.Gaussian.Norm.Sum.Basic.gaussianSum first + Data.Gaussian.Norm.Sum.Basic.gaussianSum last := by
  induction first with
  | nil =>
      change Data.Gaussian.Norm.Sum.Basic.gaussianSum last = 0 + Data.Gaussian.Norm.Sum.Basic.gaussianSum last;
      ring1
  | cons head rest ih =>
      change head + Data.Gaussian.Norm.Sum.Basic.gaussianSum (rest ++ last) = (head +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum rest) +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum last
      rw [ih]
      ring1

/-- Doubly owned piece increments equal the exact original right-piece endpoint increments.

The same reading function is applied to the two original endpoints in each right-grid piece. Structural list congruence
preserves the remaining entries and their original order. -/
private theorem mapped_pieces (value : Gaussian → Gaussian) (piece : SegmentPiece leftGeometry first last)
    (parts : List (SegmentPiece rightGeometry piece.firstPoint piece.lastPoint)) :
    (parts.map (pairedPiece piece)).map (fun pair => value pair.last - value pair.first) =
      parts.map (fun part => value part.lastPoint - value part.firstPoint) := by
  induction parts with
  | nil => rfl
  | cons part rest ih => exact congrArg (List.cons _) ih

open Purelib.Data.Gaussian in
/-- Each retained row's increments telescope to the original left-piece increment sum.

The arbitrary endpoint reading is evaluated on the original directed pieces. Row telescoping and ordered concatenation
recover the same left-piece increments. -/
theorem telescope (value : Gaussian → Gaussian) {source : List (SegmentPiece leftGeometry first last)}
    (rows : PairedSegmentRows rightCuts source) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (rows.pieces.map fun piece => value piece.last - value piece.first) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (source.map fun piece => value piece.lastPoint - value piece.firstPoint)
        := by
  induction rows with
  | nil => rfl
  | cons split tail ih =>
      rewrite [pieces, Map.map_append, sum_append, mapped_pieces, split.telescope, ih]
      exact Eq.refl _

/-- The retained paired rows have at most the original left-piece count times the right-grid piece bound.

Each original row satisfies the right grid's retained piece bound. Adding those inequalities along the dependent list
gives the displayed product without dropping repeated or stationary pieces. -/
theorem length_le {source : List (SegmentPiece leftGeometry first last)} (rows : PairedSegmentRows rightCuts source) :
    rows.pieces.length ≤ source.length * (rightColumns + rightRows + 5) := by
  induction rows with
  | nil => exact Nat.zero_le _
  | cons split tail ih =>
      have bounded := split.count_le
      rw [split.count_eq] at bounded
      simp only [pieces, Append.length_append, Map.length_map, List.length_cons]
      exact (Nat.add_le_add bounded ih).trans_eq (by
          rewrite [Multiplication.right_distrib, Nat.one_mul, Nat.add_comm];
          exact Eq.refl _)

end PairedSegmentRows

set_option genInjectivity false in
/-- A common segment split retaining both original grids, dependent rows, flattened pieces and exact count.

The left split is retained first; every right-grid row remains indexed by its exact left piece, and the cached flattened
list preserves that order. -/
structure PairedSegmentSplit (leftCuts : GridCuts leftGeometry) (rightCuts : GridCuts rightGeometry)
    (first last : Gaussian) where
  /-- The retained original left-grid segment split. -/ left : SegmentSplit leftCuts first last
  /-- The right-grid subdivisions indexed by that exact original left-piece list. -/ rows : PairedSegmentRows rightCuts
    left.pieces
  /-- The cached flattened list of original doubly owned pieces. -/ pieces : List (PairedSegmentPiece leftGeometry
    rightGeometry)
  /-- The cached pieces equal the exact retained row flattening. -/ pieces_eq : pieces = rows.pieces
  /-- The cached original common piece count. -/ count : Nat
  /-- The count cache equals the exact retained flattened piece length. -/ count_eq : count = pieces.length

constructive_injectivity PairedSegmentSplit

namespace PairedSegmentSplit

variable {leftCuts : GridCuts leftGeometry} {rightCuts : GridCuts rightGeometry} {first last : Gaussian}

open Purelib.Riemann.Paths in
/-- Construct the original left split, split its exact pieces by the original right grid, and cache the resulting doubly
owned word.

Both original endpoint coverage certificates drive the retained constructions, and the cached count is the exact
flattened piece length. -/
@[expose] def build (leftCuts : GridCuts leftGeometry) (rightCuts : GridCuts rightGeometry) (first last : Gaussian)
    (leftFirst : RectangularSegmentSplitting.Geometry.Covers leftGeometry first) (leftLast :
      RectangularSegmentSplitting.Geometry.Covers leftGeometry last)
    (rightFirst : RectangularSegmentSplitting.Geometry.Covers rightGeometry first) (rightLast :
      RectangularSegmentSplitting.Geometry.Covers rightGeometry last) :
    PairedSegmentSplit leftCuts rightCuts first last :=
  let left := SegmentSplit.build leftCuts first last leftFirst leftLast
  let rows := PairedSegmentRows.build rightCuts rightFirst rightLast left.pieces
  let pieces := rows.pieces
  ⟨left, rows, pieces, rfl, pieces.length, rfl⟩

open Purelib.Data.Gaussian in
/-- The retained doubly owned piece increments telescope to the exact original segment endpoint difference.

The cached piece equation identifies the original paired rows. Their telescope and the retained left split recover the
same directed endpoint difference for any supplied reading. -/
theorem telescope (split : PairedSegmentSplit leftCuts rightCuts first last) (value : Gaussian → Gaussian) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (split.pieces.map fun piece => value piece.last - value piece.first) =
      value last -
      value first := by
  rw [split.pieces_eq, split.rows.telescope]
  exact split.left.telescope value

/-- The retained common split count is bounded by the product of the two original grid piece bounds.

The cache equations preserve the full flattened count. The retained row bound and original left split bound multiply to
the displayed two-grid estimate. -/
theorem count_le (split : PairedSegmentSplit leftCuts rightCuts first last) :
    split.count ≤ (leftColumns + leftRows + 5) * (rightColumns + rightRows + 5) := by
  rw [split.count_eq, split.pieces_eq]
  exact split.rows.length_le.trans
    (Nat.mul_le_mul_right _ (split.left.count_eq ▸ split.left.count_le))

end PairedSegmentSplit

end
end Purelib.Riemann.Paths.RectangularPairedSegments
