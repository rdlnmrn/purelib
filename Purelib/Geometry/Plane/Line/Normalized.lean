module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Basic
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Logic.Nontrivial.Defs

open Purelib.Geometry.Plane

section
@[expose] public section

/-!
# Divine Proportions, Chapter 14 examples

The prime-field exclusions are stated through the exact finite Frobenius law
used by Euler's square test.  This avoids enumerating a carrier or searching
globally for roots.  The positive examples retain the literal source lines.
-/

namespace Purelib.Geometry.Plane.Line.Normalized

section

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K] [Nontrivial K] [DecidableEq K]

/-- The origin line with displayed coefficients slope, one and zero.

Nontriviality certifies the nonzero second direction coefficient. -/
public def printedLine (slope : K) : Line K where
  a := slope
  b := 1
  c := 0
  direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0)

end

end

end Purelib.Geometry.Plane.Line.Normalized

end
