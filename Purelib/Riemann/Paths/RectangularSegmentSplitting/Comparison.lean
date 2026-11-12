module

public import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic

/-! # Quantitative telescoping on the actual retained analytic split

Literal indexed piece errors bound the same whole endpoint error. Each
charge keeps its original occurrence, including stationary and repeated
pieces; no function or primitive constant is identified.
-/

public section

namespace Purelib.Riemann.Paths.RectangularSegmentSplitting.SegmentSplit

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Indexed (sumFin_map normSq_sumFin_sub_le_count_mul_sumFin)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)

variable {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry}
variable {first last : Gaussian}

/-- The actual indexed piece charges bound the original increment difference with its literal split count.

Each local estimate concerns that exact bounded occurrence. The original
split telescope and finite Cauchy derive the whole bound without an
integral, constant-normalization or closure premise.
-/
theorem increment_difference_le (split : SegmentSplit cuts first last)
    (left right : Gaussian → Gaussian) (charges : Fin split.pieces.length → Coordinate)
    (bounded : ∀ index : Fin split.pieces.length,
      normSq ((left (split.pieces[index.val]'index.isLt).lastPoint -
        left (split.pieces[index.val]'index.isLt).firstPoint) -
        (right (split.pieces[index.val]'index.isLt).lastPoint -
          right (split.pieces[index.val]'index.isLt).firstPoint)) ≤ charges index) :
    normSq ((left last - left first) - (right last - right first)) ≤ (split.count : Coordinate) * sumFin charges := by
  let leftValue := fun piece : SegmentPiece geometry first last => left piece.lastPoint - left piece.firstPoint
  let rightValue := fun piece : SegmentPiece geometry first last => right piece.lastPoint - right piece.firstPoint
  have original := normSq_sumFin_sub_le_count_mul_sumFin
    (fun index : Fin split.pieces.length => leftValue (split.pieces[index.val]'index.isLt))
    (fun index : Fin split.pieces.length => rightValue (split.pieces[index.val]'index.isLt)) charges bounded
  have leftEq := (sumFin_map split.pieces leftValue).trans (split.telescope left)
  have rightEq := (sumFin_map split.pieces rightValue).trans (split.telescope right)
  have values := congrArg₂ (fun a b : Gaussian => a - b) leftEq rightEq
  have counted := Eq.mp (congrArg (fun value : Gaussian => normSq value ≤
    (split.pieces.length : Coordinate) * sumFin charges) values) original
  exact counted.trans_eq
    (congrArg (fun count : Nat => (count : Coordinate) * sumFin charges) split.count_eq.symm)

/-- A charge depending only on each original piece uses the same finite indexed estimate and exact ordered map. -/
theorem increment_difference_map_le (split : SegmentSplit cuts first last)
    (left right : Gaussian → Gaussian) (charges : SegmentPiece geometry first last → Coordinate)
    (bounded : ∀ piece ∈ split.pieces,
      normSq ((left piece.lastPoint - left piece.firstPoint) -
        (right piece.lastPoint - right piece.firstPoint)) ≤ charges piece) :
    normSq ((left last - left first) - (right last - right first)) ≤
      (split.count : Coordinate) * Algebra.FiniteSum.Rational.Squares.coordinateSum (split.pieces.map charges) :=
  (split.increment_difference_le left right
    (fun index : Fin split.pieces.length => charges (split.pieces[index.val]'index.isLt))
    (fun index => bounded _ (List.getElem_mem index.isLt))).trans_eq
      (congrArg (fun value : Coordinate => (split.count : Coordinate) * value)
        (Algebra.FiniteSum.Rational.Squares.coordinateSum_map_eq_sumFin split.pieces charges).symm)

end Purelib.Riemann.Paths.RectangularSegmentSplitting.SegmentSplit
