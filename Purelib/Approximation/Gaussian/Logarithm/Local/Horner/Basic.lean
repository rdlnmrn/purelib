module
public import Purelib.Approximation.Rat.Logarithm.Horner.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Gaussian.Basic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation.Rat.Logarithm.Horner.Basic

open Purelib.Data.Gaussian.RationalEmbedding

section
@[expose] public section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Basic

/-- Compute one canonical Gaussian logarithm Horner step using the displayed rational coefficient.

The supplied tail is multiplied by the reduced squared argument and coefficient, then added to one. -/
def step (w : Canonical) (index :
  Nat) (tail : Canonical) : Canonical :=
  Data.Gaussian.Basic.canonical (1 + ComplexLog.scalar (ComplexLog.coefficient index) * w * tail)

/-- The canonical Gaussian Horner step equals its defining scalar expression. -/
theorem step_eq (w : Canonical)
  (index : Nat) (tail : Canonical) :
    step w index tail = 1 + ComplexLog.scalar
      (ComplexLog.coefficient index) * w * tail :=
  Data.Gaussian.Basic.canonical_eq _

/-- Evaluate the finite Gaussian logarithm Horner recurrence.

The zero-depth value is one; each successor step advances the coefficient index and consumes the recursively evaluated
tail. -/
def horner (w :
  Canonical) : Nat → Nat → Canonical
  | _, 0 => 1
  | index, depth + 1 => step w index
    (horner w (index + 1) depth)

/-- The zero-depth Gaussian logarithm Horner value is one. -/
@[simp] theorem horner_zero (w :
  Canonical) (index : Nat) :
    horner w index 0 = 1 := rfl

/-- A successor-depth Gaussian Horner value applies one step to the next-index tail. -/
@[simp] theorem horner_succ (w :
  Canonical) (index depth : Nat) :
    horner w index (depth + 1) =
      step w index
        (horner w (index + 1) depth) := rfl
end Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Basic

end
