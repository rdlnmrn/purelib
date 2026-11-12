module

public import Purelib.Geometry.Rational.Box.Square.Centered.Separation
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Components.Maximum
import Purelib.Tactic.Ring

/-! # The actual retained signed-square radius below its original center quadrance

The retained radius reads half the original largest coordinate magnitude.
The existing maximum-coordinate norm bound therefore pays four times
that same radius square, without replacing the original signed square.
-/

public section

namespace Purelib.Geometry.Rational.Box.Square.Centered.Separation

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian

/-- Four times the original signed-square radius squared is bounded by its same center's quadrance.

The exact retained radius equation identifies twice that radius with the
original maximum coordinate magnitude. Its existing squared-norm bound
therefore applies to the unchanged square and center.
-/
theorem radius_sq_le_normSq {center : Canonical} (separation : Separation center) :
    4 * separation.radius ^ 2 ≤ Norm.Basic.normSq center := by
  have paid := Norm.Components.maximum_sq_le_normSq center
  change coordinateMaximum center ^ 2 ≤ Norm.Basic.normSq center at paid
  rewrite [← separation.radius_eq] at paid
  exact (show 4 * separation.radius ^ 2 = (2 * separation.radius) ^ 2 by ring1).trans_le paid

end Purelib.Geometry.Rational.Box.Square.Centered.Separation

end
