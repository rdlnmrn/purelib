module

public import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Fraction
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Segment

/-! # Exact partial parameters of the same retained analytic split piece -/

public section

namespace Purelib.Riemann.Paths.RectangularSegmentSplitting.SegmentSplit.Located

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)

variable {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry}
variable {first last : Canonical} {split : SegmentSplit cuts first last} {parameter : Rational}
variable (located : Located split parameter)

/-- Normalize the original query using its SAME selected piece's proper parameter interval. -/
@[expose] def fraction : Rational := located.piece.interval.fraction parameter

/-- The exact selected-piece fraction is in the closed unit interval, including either endpoint. -/
theorem fraction_inside : 0 ≤ located.fraction ∧ located.fraction ≤ 1 :=
  located.piece.interval.fraction_inside located.inside

/-- The literal selected piece at its normalized fraction is the SAME original segment query point. -/
theorem point_eq :
    Affine.line located.piece.firstPoint (located.piece.lastPoint - located.piece.firstPoint)
      located.fraction = PreparedSegmentCuts.point first last parameter := by
  have endpoints := congrArg₂
    (fun a b => PreparedSegmentCuts.point a b located.fraction)
    located.piece.first_eq located.piece.last_eq
  have interpolation := PreparedSegmentCuts.point_affine first last
    located.piece.interval.lower located.piece.interval.upper located.fraction
  have original := congrArg (PreparedSegmentCuts.point first last)
    (located.piece.interval.fraction_eq parameter)
  exact (PreparedSegmentCuts.point_eq_line _ _ _).symm.trans
    (endpoints.trans (interpolation.symm.trans original))

/-- The exact same original query point lies in the selected piece's retained cell. -/
theorem contained : (geometry.box located.piece.column located.piece.row).Contains
    (PreparedSegmentCuts.point first last parameter) :=
  located.point_eq ▸ Box.contains_line located.piece.first_inside located.piece.last_inside located.fraction_inside

end Purelib.Riemann.Paths.RectangularSegmentSplitting.SegmentSplit.Located

end
