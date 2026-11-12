module

public import Purelib.Geometry.Rational.Box.Outside.Transport
public import Purelib.Geometry.Rational.Box.Interior
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Outside sides paid by retained box separation

The original separating box faces select a coordinate side of an interior
point of the other box. Its gap is at least that point's retained minimum
interior gap, even when another point-only side has a much smaller gap.
-/

public section

namespace Purelib.Geometry.Rational.Box

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Fraction.Order

/-- Compute an original outside side from separated boxes with a gap paid by the actual interior point.

The four original box-face comparisons select the side. Strict containment
in the other retained box gives the actual outside inequality and bounds
the same selected side gap below by the original minimum interior gap. -/
@[expose] def Separated.outsideSide {outer inner : Box} {point : Canonical}
    (separated : outer.Separated inner) (inside : inner.StrictContains point) :
    {side : OutsideSide outer point // Interior.strictCoordinateGap inner point ≤ side.gap} := by
  by_cases right : outer.xUpper < inner.xLower
  · refine ⟨.right (right.trans inside.1), ?_⟩
    change Interior.strictCoordinateGap inner point ≤ point.re - outer.xUpper
    exact (Basic.min_le_left _ _).trans (Arithmetic.sub_le_sub_left_direct right.le point.re)
  by_cases left : inner.xUpper < outer.xLower
  · refine ⟨.left (inside.2.1.trans left), ?_⟩
    change Interior.strictCoordinateGap inner point ≤ outer.xLower - point.re
    exact ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _)).trans
      (Arithmetic.sub_le_sub_right_direct left.le point.re)
  by_cases top : outer.yUpper < inner.yLower
  · refine ⟨.top (top.trans inside.2.2.1), ?_⟩
    change Interior.strictCoordinateGap inner point ≤ point.im - outer.yUpper
    exact ((Basic.min_le_right _ _).trans ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _))).trans
      (Arithmetic.sub_le_sub_left_direct top.le point.im)
  have bottom : inner.yUpper < outer.yLower := by
    rcases separated with isRight | isLeft | isTop | isBottom
    · exact (right isRight).elim
    · exact (left isLeft).elim
    · exact (top isTop).elim
    · exact isBottom
  refine ⟨.bottom (inside.2.2.2.trans bottom), ?_⟩
  change Interior.strictCoordinateGap inner point ≤ outer.yLower - point.im
  exact ((Basic.min_le_right _ _).trans ((Basic.min_le_right _ _).trans (Basic.min_le_right _ _))).trans
    (Arithmetic.sub_le_sub_right_direct bottom.le point.im)

end Purelib.Geometry.Rational.Box
