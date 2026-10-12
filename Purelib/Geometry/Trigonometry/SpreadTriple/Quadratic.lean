module
public import Purelib.Geometry.Trigonometry.Spread.Triple
import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry.Trigonometry.Spread.Triple

section
@[expose] public section

/-!
# Divine Proportions, Exercise 10.12

The source's complex calculation uses only exact Gaussian-rational arithmetic.
Each value here is therefore represented by a finite pair
`Rational × Rational`, equipped with the project-owned constructive field
operations; no completed complex object is introduced.
-/

namespace Purelib.Geometry.Trigonometry.SpreadTriple.Quadratic

section

/-- Factor the Triple-spread polynomial using two roots with the specified sum and product. -/
public theorem factorization_identity
    {K : Type*} [Algebra.Field.ExplicitField K]
    (firstSpread secondSpread firstRoot secondRoot thirdSpread : K)
    (rootSum :
      firstRoot + secondRoot =
        2 * (firstSpread + secondSpread) -
          4 * firstSpread * secondSpread)
    (rootProduct :
      (firstSpread + secondSpread) ^ 2 -
          2 * (firstSpread ^ 2 + secondSpread ^ 2) =
        -(firstRoot * secondRoot)) :
    TripleSpread.tripleSpreadFunction firstSpread secondSpread thirdSpread =
      -((thirdSpread - firstRoot) * (thirdSpread - secondRoot)) := by
  calc
    TripleSpread.tripleSpreadFunction firstSpread secondSpread thirdSpread =
        -thirdSpread ^ 2 +
          (2 * (firstSpread + secondSpread) -
            4 * firstSpread * secondSpread) * thirdSpread +
          ((firstSpread + secondSpread) ^ 2 -
            2 * (firstSpread ^ 2 + secondSpread ^ 2)) := by
      unfold TripleSpread.tripleSpreadFunction
      ring1
    _ = -thirdSpread ^ 2 +
        (firstRoot + secondRoot) * thirdSpread -
          firstRoot * secondRoot := by
      rw [rootSum, rootProduct]
      ring1
    _ = -((thirdSpread - firstRoot) *
        (thirdSpread - secondRoot)) := by ring1

end

end Purelib.Geometry.Trigonometry.SpreadTriple.Quadratic

end
