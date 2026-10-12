module
public import Purelib.Geometry.Trigonometry.Spread.Triple
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry.Trigonometry

open Purelib.Geometry.Trigonometry.Spread.Triple

section
@[expose] public section

/-!
# Divine Proportions, Chapter 10: isosceles triangles

The scalar forms isolate the finite cancellations used by the geometric
statements.  They apply uniformly to ratios obtained from rational triangles
or from triangles over explicit finite fields.
-/

namespace Purelib.Geometry.Triangles.Equilateral.Numeric

variable {K : Type*} [ExplicitField K]

/-- Theorem 69 (Equilateral triangle), in terms of the common spread and quadrance. The common cross is represented by
its complement `1 - s`. -/
theorem equilateral_triangle [DecidableEq K]
    (q s : K) (sNonzero : s ≠ 0) (fourNonzero : (4 : K) ≠ 0)
    (spreadTriple : TripleSpread.SpreadTriple s s s) :
    s = 3 / 4 ∧
      1 - s = 1 / 4 ∧
      QuadTriple.Basic.archimedesFunction q q q = 3 * q ^ 2 := by
  have squareNonzero : s ^ 2 ≠ 0 := by
    simpa [pow_two] using ExplicitField.mul_ne_zero sNonzero sNonzero
  have factorZero : s ^ 2 * (3 - 4 * s) = 0 := by
    unfold TripleSpread.SpreadTriple TripleSpread.tripleSpreadFunction at spreadTriple
    calc
      s ^ 2 * (3 - 4 * s) =
          (s + s + s) ^ 2 - 2 * (s ^ 2 + s ^ 2 + s ^ 2) -
            4 * s * s * s := by ring1
      _ = 0 := spreadTriple
  have linearZero : 3 - 4 * s = 0 := by
    by_cases zero : 3 - 4 * s = 0
    · exact zero
    · exact False.elim
        ((ExplicitField.mul_ne_zero squareNonzero zero) factorZero)
  have spreadValue : s = 3 / 4 := by
    apply ExplicitField.eq_of_mul_eq_mul_right fourNonzero
    calc
      s * 4 = 3 := by
        calc
          s * 4 = 3 - (3 - 4 * s) := by ring1
          _ = 3 := by rw [linearZero]; ring1
      _ = (3 / 4) * 4 :=
        (ExplicitField.div_mul_cancel 3 fourNonzero).symm
  have crossValue : 1 - s = 1 / 4 := by
    apply ExplicitField.eq_of_mul_eq_mul_right fourNonzero
    calc
      (1 - s) * 4 = (1 - 3 / 4) * 4 := by rw [spreadValue]
      _ = 4 - (3 / 4) * 4 := by ring1
      _ = 1 := by
        rw [ExplicitField.div_mul_cancel 3 fourNonzero]
        ring1
      _ = (1 / 4) * 4 :=
        (ExplicitField.div_mul_cancel 1 fourNonzero).symm
  exact ⟨spreadValue, crossValue, by
    unfold QuadTriple.Basic.archimedesFunction
    ring1⟩
end Purelib.Geometry.Triangles.Equilateral.Numeric

end
