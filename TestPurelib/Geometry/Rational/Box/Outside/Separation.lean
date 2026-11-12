module

import Purelib.Geometry.Rational.Box.Outside.Separation
import Purelib.Geometry.Rational.Box.Outside.Transport
import Purelib.Geometry.Rational.Box.Outside
import Purelib.Geometry.Rational.Box.Square.Centered.Interior
import Purelib.Data.Gaussian.Basic

/-! # Retained owner separation pays a gap that a point-only side can miss -/

namespace TestPurelib.Geometry.Rational.Box.Outside.Separation

open Purelib.Geometry.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

/-- The original outer square is centered at zero with radius one eighth. -/
def outer : Box := Box.Square.Centered.Affine.centeredSquare ⟨0, 0⟩ (1 / 8) (by decide)

/-- The original point barely clears the outer square's right face and lies far above it. -/
def point : Canonical := ⟨9 / 64, 1⟩

/-- Its original inner owner square has the same radius and is separated along the imaginary coordinate. -/
def inner : Box := Box.Square.Centered.Affine.centeredSquare point (1 / 8) (by decide)

/-- The actual original owner boxes retain strict top separation. -/
theorem separated : outer.Separated inner := Or.inr (Or.inr (Or.inl (by decide +kernel)))

/-- The original point lies strictly inside its same retained inner owner. -/
theorem inside : inner.StrictContains point := by
  constructor <;> decide +kernel

/-- A point-only selector chooses the much smaller original right-face gap. -/
def pointSide := Box.outsideSide (box := outer) (point := point) (by decide +kernel)

/-- That original point-only gap is one sixty-fourth. -/
example : pointSide.gap = 1 / 64 := by decide +kernel

/-- Compute the paid original side from the same actual owner boxes and interior point. -/
def retained := separated.outsideSide inside

/-- Its same retained side has the original top gap seven eighths. -/
example : retained.val.gap = 7 / 8 := by decide +kernel

/-- The actual retained side gap pays the original inner owner's minimum interior gap. -/
example : Box.Interior.strictCoordinateGap inner point ≤ retained.val.gap := retained.property

/-- The original centered inner owner's minimum interior gap remains one eighth. -/
example : Box.Interior.strictCoordinateGap inner point = 1 / 8 :=
  Box.Square.Centered.Interior.centeredSquare_gap _ _ _

/-- The smaller point-only gap cannot pay this same actual inner-owner floor. -/
example : pointSide.gap < Box.Interior.strictCoordinateGap inner point := by decide +kernel

/-- The retained outside-side squared margin is the square of that exact same paid coordinate gap. -/
example : retained.val.margin = retained.val.gap ^ 2 := retained.val.margin_eq_gap_sq

end TestPurelib.Geometry.Rational.Box.Outside.Separation
