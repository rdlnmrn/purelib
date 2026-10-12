module
public import Purelib.Geometry.Trigonometry.Spread.Triple
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Trigonometry.Spread.Quadruple
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Geometry.Trigonometry.Spread

open Purelib.Geometry.Trigonometry.Spread.Triple

section
@[expose] public section

/-!
# Divine Proportions, §7.7: quadruple spread and cross formulas

The scalar elimination is kept separate from the geometric specialization.
Two displayed spread triples give two explicit quadratic equations with a
common root; the finite quadratic-compatibility calculation then yields the
four-variable polynomial.
-/

namespace Purelib.Geometry.Trigonometry.Cross.Quadruple

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The constructive diagonal-cross calculation. Unlike the diagonal-spread formula, complementation leaves an outer
`1-`; Exercise 7.14 omits it. -/
theorem two_cross_triples_common_value
    (a b c d x : K)
    (twoNonzero : (2 : K) ≠ 0)
    (firstTriple : TripleSpread.SpreadTriple (1 - a) (1 - b) (1 - x))
    (secondTriple : TripleSpread.SpreadTriple (1 - c) (1 - d) (1 - x))
    (centersDistinct :
      a + b - 2 * a * b ≠ c + d - 2 * c * d) :
    let denominator := 2 * (a + b - c - d - 2 * a * b + 2 * c * d)
    denominator ≠ 0 ∧
      x = 1 - ((a - b) ^ 2 - (c - d) ^ 2) / denominator := by
  dsimp only
  have complementedCentersDistinct :
      (1 - a) + (1 - b) - 2 * (1 - a) * (1 - b) ≠
        (1 - c) + (1 - d) - 2 * (1 - c) * (1 - d) := by
    intro centersEqual
    apply centersDistinct
    calc
      a + b - 2 * a * b =
          (1 - a) + (1 - b) - 2 * (1 - a) * (1 - b) := by ring1
      _ = (1 - c) + (1 - d) - 2 * (1 - c) * (1 - d) := centersEqual
      _ = c + d - 2 * c * d := by ring1
  have result := Quadruple.two_spread_triples_common_value
    (1 - a) (1 - b) (1 - c) (1 - d) (1 - x)
    twoNonzero firstTriple secondTriple complementedCentersDistinct
  dsimp only at result
  have denominatorEquality :
      2 * ((1 - a) + (1 - b) - (1 - c) - (1 - d) -
          2 * (1 - a) * (1 - b) + 2 * (1 - c) * (1 - d)) =
        2 * (a + b - c - d - 2 * a * b + 2 * c * d) := by ring1
  have numeratorEquality :
      ((1 - a) - (1 - b)) ^ 2 - ((1 - c) - (1 - d)) ^ 2 =
        (a - b) ^ 2 - (c - d) ^ 2 := by ring1
  constructor
  · rw [← denominatorEquality]
    exact result.1
  · calc
      x = 1 - (1 - x) := by ring1
      _ = 1 -
          (((1 - a) - (1 - b)) ^ 2 - ((1 - c) - (1 - d)) ^ 2) /
            (2 * ((1 - a) + (1 - b) - (1 - c) - (1 - d) -
              2 * (1 - a) * (1 - b) +
              2 * (1 - c) * (1 - d))) := by rw [result.2]
      _ = 1 - ((a - b) ^ 2 - (c - d) ^ 2) /
          (2 * (a + b - c - d - 2 * a * b + 2 * c * d)) := by
        rw [numeratorEquality, denominatorEquality]
end Purelib.Geometry.Trigonometry.Cross.Quadruple

end
