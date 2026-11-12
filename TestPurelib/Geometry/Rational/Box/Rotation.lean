module
import Purelib.Geometry.Rational.Box.Rotation
import Purelib.Geometry.Rational.Box.Square.Centered.Rotation
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Data.Gaussian.Basic

/-! # Exact rotated-box enclosure regressions -/

namespace TestPurelib.Geometry.Rational.Box.Rotation

open Purelib.Geometry.Rational

/-- A nonsymmetric rational rectangle with horizontal width two and vertical width one. -/
def source : Box := ⟨0, 2, 0, 1, by decide, by decide⟩

/-- A positive slope retains the extreme real sums and reversed imaginary contributions. -/
example :
    let box := Box.Rotation.enclosure 2 source
    (box.xLower, box.xUpper, box.yLower, box.yUpper) = (0, 4, -4, 1) := by rfl

/-- A negative slope reverses the vertical contribution to the real interval. -/
example :
    let box := Box.Rotation.enclosure (-2) source
    (box.xLower, box.xUpper, box.yLower, box.yUpper) = (-2, 2, 0, 5) := by rfl

/-- The zero-slope construction preserves every original rectangle endpoint. -/
example : Box.Rotation.enclosure 0 source = source := by rfl

/-- The rotated upper-right corner lies inside the computed positive-slope enclosure. -/
example : (Box.Rotation.enclosure 2 source).Contains ⟨4, -3⟩ := by decide

/-- A point beyond the maximum rotated real reading is excluded by the computed enclosure. -/
example : ¬ (Box.Rotation.enclosure 2 source).Contains ⟨5, -3⟩ := by decide

/-- A retained point box stays a point box under rotation. -/
example :
    let source : Box := ⟨1, 1, -1, -1, le_rfl, le_rfl⟩
    let box := Box.Rotation.enclosure 2 source
    (box.xLower, box.xUpper, box.yLower, box.yUpper) = (-1, -1, -3, -3) := by rfl

/-- A paid actual rotated height difference separates both original square enclosures in a negative-slope chart. -/
example :
    (Box.Rotation.enclosure (-2) (Box.Square.Centered.Affine.centeredSquare ⟨0, 0⟩ (1 / 8) (by decide))).yUpper <
      (Box.Rotation.enclosure (-2) (Box.Square.Centered.Affine.centeredSquare ⟨0, 1⟩ (1 / 8) (by decide))).yLower :=
  Box.Rotation.enclosure_centeredSquare_ySeparated _ _ _ _ _ (by decide)

end TestPurelib.Geometry.Rational.Box.Rotation
