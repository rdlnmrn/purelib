module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Exponential.Horner.Basic
import Purelib.Approximation.Gaussian.Exponential.Horner.Bounds
public import Purelib.Approximation.Rational.Geometric.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation.Gaussian.Exponential

open Purelib.Approximation.Rational

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the exponential

The relative exponential is not introduced by dividing by its argument.
Instead, `expRelSample z n` is the already finite inner Horner program, and
the factorization

`expSample z n - 1 = z * expRelSample z n`

is proved at every displayed depth, including `z = 0`.  A second shifted
Horner program gives a quadratic remainder.  All approximation objects below
contain only Gaussian-rational samples, rational squared-error allowances,
and terminating natural-number refinement programs.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Horner.Relative.Sample

/-! ## The first relative exponential -/

/-- The finite program for `(exp z - 1) / z`, defined without division by `z`. At zero it evaluates directly to one. -/
def expRelSample (z :
  Canonical) (index : Nat) : Canonical :=
  Horner.Basic.horner z 2 index

/-- Every finite relative-exponential sample at zero input is one. -/
theorem expRelSample_zero (index : Nat) :
  expRelSample 0 index = 1 :=
  Horner.Basic.horner_zero_input index 2

/-- Later relative-exponential samples on the unit disk stay within the earlier index's scale-ten quarter-radius
allowance. -/
theorem expRelSample_later_close {z :
  Canonical}
    (unitInput : Data.Gaussian.Norm.Basic.normSq z ≤ 1) {earlier later : Nat}
    (order : earlier ≤ later) :
    Data.Gaussian.Norm.Basic.normSq (expRelSample z
      later - expRelSample z earlier) ≤
      Geometric.Basic.quarterRadius 10 earlier := by
  obtain ⟨extra, rfl⟩ : ∃ extra, later = earlier + extra :=
    ⟨later - earlier, (Data.Nat.Subtraction.add_sub_of_le order).symm⟩
  simpa only [expRelSample,
    Geometric.Basic.quarterRadius_eq_mul_pow] using
      Horner.Bounds.horner_add_depth_close z unitInput
        earlier extra 2 (by decide)

/-- Every finite relative-exponential sample on the unit disk has squared norm at most four. -/
theorem expRelSample_bounded {z :
  Canonical}
    (unitInput : Data.Gaussian.Norm.Basic.normSq z ≤ 1) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (expRelSample z
      index) ≤ 4 :=
  Horner.Bounds.horner_bounded z unitInput index 2 (by decide)
end Purelib.Approximation.Gaussian.Exponential.Horner.Relative.Sample

end
