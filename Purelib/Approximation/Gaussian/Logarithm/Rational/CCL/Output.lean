module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Sequence.CCL.Output
public import Purelib.Approximation.Gaussian.Name.CCL.Output
public import Purelib.Approximation.Gaussian.Logarithm.Rational.Name
import Purelib.Approximation.Gaussian.Logarithm.Rational.Sequence
import Purelib.Data.CCL.Transducer.Machine.Advance

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Logarithm.Rational

open Purelib.Data.CCL.Transducer.Machine

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite logarithm Horner approximation

For a displayed positive rational input in `[1/2,2]`, this module computes only
finite truncations of `2z(1 + z²/3 + z⁴/5 + ⋯)`, where
`z = (x - 1)/(x + 1)`.  The ellipsis is descriptive only: every definition
below is structural recursion with a natural depth, and every semantic
predicate has an explicit later finite index witness.  No completed logarithm,
infinite series, or limit is introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Rational.CCL.Output

/-- The finite logarithm name for a rational input in the retained interval emits exactly the requested finite bit count
and preserves its initial prefix. -/
theorem productive (x : Fraction.Rational) (halfLe :
  1 / 2 ≤ x) (leTwo : x ≤ 2)
    (count : Nat) :
    (Name.named x halfLe leTwo).machine.emitted.IsPrefix
        (Advance.advance
          (Name.named x halfLe leTwo).machine count).emitted ∧
      (Advance.advance
          (Name.named x halfLe leTwo).machine count).emitted.length = count :=
  (Sequence.approximation x halfLe leTwo).output_productive count

end Purelib.Approximation.Gaussian.Logarithm.Rational.CCL.Output

end
