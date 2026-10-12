module
public import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Gaussian.Basic

section
@[expose] public section

/-!
# Whole-cycle quartic sample certificates

This module retains the generated sample certificates for the explicit A
boundary banks and B connector banks. These are independent numerical
fixtures: the connector banks do not represent the root-closed standard B
tour. The Python generator owns the rational totals and error coefficients.
-/

namespace Purelib.Data.Gaussian.Additive

/-- Reassociate four Gaussian summands while preserving their displayed order. -/
theorem gaussianFourSum_assoc
    (a b c d : Canonical) :
    ((a + b) + c) + d = a + (b + (c + d)) := by
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re,
      Gaussian.Basic.add_im] <;> ring1
end Purelib.Data.Gaussian.Additive

end
