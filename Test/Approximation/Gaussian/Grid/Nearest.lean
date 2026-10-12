module
public import Purelib.Approximation.Gaussian.Grid.Nearest.Basic

import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Approximation.Gaussian.Grid

section
@[expose] public section

namespace Test.Approximation.Gaussian.Grid.Nearest

/-- Nearest-grid rounding works on both sides of zero. -/
theorem signed_rounding :
    Nearest.Basic.rounded (1 / 4) ⟨1 / 3, -(1 / 3)⟩ = ⟨1 / 4, -(1 / 4)⟩ := by
  decide +kernel

/-- Proposal generation can discard a tiny imaginary component; the caller still has to check the resulting point before
using it. -/
theorem tiny_imaginary_component :
    Nearest.Basic.rounded (1 / 4) ⟨1, -(1 / 32)⟩ = ⟨1, 0⟩ := by
  decide +kernel
end Test.Approximation.Gaussian.Grid.Nearest

end

end
