module

import Purelib.Curves.Legendre.Paths.Preparation

/-! # Intrinsic branch-box preparation and signed square enclosure regressions -/

namespace TestPurelib.Curves.Legendre.Paths.Preparation

open Purelib.Curves.Legendre.Paths
open Purelib.Geometry.Rational
open Purelib.Data.Gaussian.Coordinates

/-- A negative real parameter retains the logical order parameter, zero, one. -/
example :
    [(branchOrder (gaussian (-1) 0) (projectionSlope (gaussian (-1) 0))).forward 0,
      (branchOrder (gaussian (-1) 0) (projectionSlope (gaussian (-1) 0))).forward 1,
      (branchOrder (gaussian (-1) 0) (projectionSlope (gaussian (-1) 0))).forward 2] = [1, 0, 2] := rfl

/-- A parameter between zero and one retains the logical label order. -/
example :
    [(branchOrder (gaussian (1 / 2) 0) (projectionSlope (gaussian (1 / 2) 0))).forward 0,
      (branchOrder (gaussian (1 / 2) 0) (projectionSlope (gaussian (1 / 2) 0))).forward 1,
      (branchOrder (gaussian (1 / 2) 0) (projectionSlope (gaussian (1 / 2) 0))).forward 2] = [0, 1, 2] := rfl

/-- A real parameter above one moves the one label before the parameter label. -/
example :
    [(branchOrder (gaussian 2 0) (projectionSlope (gaussian 2 0))).forward 0,
      (branchOrder (gaussian 2 0) (projectionSlope (gaussian 2 0))).forward 1,
      (branchOrder (gaussian 2 0) (projectionSlope (gaussian 2 0))).forward 2] = [0, 2, 1] := rfl

/-- The exceptional imaginary parameter uses its computed slope two and the correct order. -/
example :
    [(branchOrder (gaussian 0 1) (projectionSlope (gaussian 0 1))).forward 0,
      (branchOrder (gaussian 0 1) (projectionSlope (gaussian 0 1))).forward 1,
      (branchOrder (gaussian 0 1) (projectionSlope (gaussian 0 1))).forward 2] = [0, 2, 1] := rfl

/-- The opposite exceptional parameter orders its negative projected reading before zero. -/
example :
    [(branchOrder (gaussian 1 (-1)) (projectionSlope (gaussian 1 (-1)))).forward 0,
      (branchOrder (gaussian 1 (-1)) (projectionSlope (gaussian 1 (-1)))).forward 1,
      (branchOrder (gaussian 1 (-1)) (projectionSlope (gaussian 1 (-1)))).forward 2] = [1, 0, 2] := rfl

/-- The real midpoint computes radius one sixth from its actual half-unit gaps. -/
example : branchRadius (gaussian (1 / 2) 0) (projectionSlope (gaussian (1 / 2) 0)) = 1 / 6 := by decide

/-- The imaginary exception pays the full slope-two width with radius one seventh. -/
example : branchRadius (gaussian 0 1) (projectionSlope (gaussian 0 1)) = 1 / 7 := by decide

/-- The reflected exception has the same exact radius payment. -/
example : branchRadius (gaussian 1 (-1)) (projectionSlope (gaussian 1 (-1))) = 1 / 7 := by decide

/-- A binding cap narrows the same original radius below its default projection allocation. -/
example : branchRadius (gaussian (1 / 2) 0) 0 ⟨1 / 8, by decide⟩ = 1 / 8 := by decide

/-- The capped original selector uses that same narrower radius in the actual moving branch square. -/
example : (branchBoxes (gaussian (1 / 2) 0) 0 (by constructor <;> decide)
    (cap := ⟨1 / 8, by decide⟩) 1).xLower = 3 / 8 := by decide

/-- The public intrinsic preparation proves the retained imaginary-parameter boxes separated. -/
example :
    (branchBoxes (gaussian 0 1) (projectionSlope (gaussian 0 1))
      (projectionSlope_separates _ (by decide) (by decide)) (cap := ⟨1, by decide⟩) 0).Separated
      (branchBoxes (gaussian 0 1) (projectionSlope (gaussian 0 1))
      (projectionSlope_separates _ (by decide) (by decide)) (cap := ⟨1, by decide⟩) 1) :=
  branchBoxes_separated _ _ (projectionSlope_separates _ (by decide) (by decide)) _ _ (by decide)

/-- A negative slope computes the same half-width factor about the actual rotated center. -/
example :
    Box.Rotation.enclosure (-2)
      (Box.Square.Centered.Affine.centeredSquare (gaussian 3 5) 1 (by decide)) =
      Box.Square.Centered.Affine.centeredSquare (gaussian (-7) 11) 3 (by decide) :=
  Box.Rotation.enclosure_centeredSquare _ _ _ (by decide)

/-- A zero-radius square rotates to the exact point for either sign of slope. -/
example :
    Box.Rotation.enclosure (-2)
      (Box.Square.Centered.Affine.centeredSquare (gaussian 3 5) 0 (by decide)) =
      Box.Square.Centered.Affine.centeredSquare (Rotation.rotate (-2) (gaussian 3 5)) 0 (by decide) :=
  Box.Rotation.enclosure_centeredSquare _ _ _ (by decide)

end TestPurelib.Curves.Legendre.Paths.Preparation
