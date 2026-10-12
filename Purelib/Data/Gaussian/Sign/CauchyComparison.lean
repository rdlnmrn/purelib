module
public import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Rat.Sign.Jump
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

namespace Purelib.Data.Gaussian.Sign.CauchyComparison

/-! ## Rouché comparison of two synchronized finite walks -/

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Compute the sum of two signed jumps from the retained Gaussian endpoint coordinates.

Form the real and imaginary coordinates of the conjugate-product comparison, then use those products and the retained
imaginary endpoint factor in the two original signJump calls. The integer result preserves their ordered signed sum. -/
def vertexHomotopyCorrection2 (source target : Basic.Canonical) : Int
  :=
  let real := source.re * target.re + source.im * target.im
  let imaginary := source.re * target.im - source.im * target.re
  (Sign.Jump.signJump 1 (real * imaginary) : Int) +
    Sign.Jump.signJump 1 (imaginary * ((-source.im) * target.im))
end Purelib.Data.Gaussian.Sign.CauchyComparison

end
