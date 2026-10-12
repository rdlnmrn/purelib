module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Squares
public import Purelib.Geometry.Trigonometry.Spread.Number.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Geometry.Trigonometry.Spread

section
@[expose] public section

/-!
# Divine Proportions, Chapter 14 examples

The prime-field exclusions are stated through the exact finite Frobenius law
used by Euler's square test.  This avoids enumerating a carrier or searching
globally for roots.  The positive examples retain the literal source lines.
-/

namespace Purelib.Geometry.Trigonometry.SpreadNumber.Obstruction

section

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K] [Nontrivial K] [DecidableEq K]
omit [Nontrivial K] [DecidableEq K] in
/-- A value is not a spread number when its nonzero radicand is not a square. -/
public theorem not_spread_of_radicand_nonsquare
    (value : K)
    (radicandNonzero : value * (1 - value) ≠ 0)
    (radicandNotSquare : ¬ Squares.IsNonzeroSquare (value * (1 - value))) :
    ¬ Number.Basic.IsSpreadNumber value := by
  rintro ⟨root, rootSquare⟩
  apply radicandNotSquare
  have rootNonzero : root ≠ 0 := by
    intro rootZero
    apply radicandNonzero
    calc
      value * (1 - value) = root ^ 2 := rootSquare
      _ = 0 := by rw [rootZero]; ring1
  exact ⟨root, rootNonzero, rootSquare⟩

end

end

end Purelib.Geometry.Trigonometry.SpreadNumber.Obstruction

end
