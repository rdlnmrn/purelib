module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
import Purelib.Algebra.FiniteSum.Prefix
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Sample
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Quarter
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.FiniteSum.Geometric
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Bounds.ReciprocalNatural
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.FiniteSum

open Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.Gaussian

open Purelib.Data.Rat

section
public section

/-!
# Executable, limit-free differential laws for the logarithm

This module works with the finite local coordinate `log(1+u)`, on the
displayed rational disk `normSq u ≤ 1/4`.  Its relative forms and derivative
are finite alternating sums.  The reciprocal derivative law is expressed by
an exact finite geometric remainder and then by finite-request operational
equivalence.  No infinitesimal, limit, infinite series, or global logarithm
branch is introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Bounds

open Purelib.Data.Rat.Bounds in
/-- The indexed second-relative logarithm term has squared norm bounded by the matching quarter-power on the
quarter-quadrance disk.

The disk bounds the original Gaussian power. The reciprocal natural
coefficient has square at most one, preserving the matching quarter-power bound. -/
theorem log1pSecondRelTerm_bound {u : Data.Gaussian.Basic.Canonical}
    (disk : Data.Gaussian.Norm.Basic.normSq u ≤ 1 / 4) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (Sample.log1pSecondRelTerm u index) ≤
      (1 / 4 : Fraction.Rational) ^ index := by
  rw [Sample.log1pSecondRelTerm, Scale.normSq_scale,
    Power.normSq_pow, Data.Gaussian.Norm.Basic.normSq_neg]
  have coefficientBound :
      (-(1 / ((index + 2 : Nat) : Fraction.Rational))) ^ 2 ≤ 1 := by
    calc
      (-(1 / ((index + 2 : Nat) : Fraction.Rational))) ^ 2 =
          (1 / ((index + 2 : Nat) : Fraction.Rational)) ^ 2 := by ring1
      _ = (1 / (((index + 1) + 1 : Nat) : Fraction.Rational)) ^ 2 := by
        rw [show index + 2 = (index + 1) + 1 by ring1]
      _ ≤ 1 := ReciprocalNatural.reciprocalNatSq_le_one (index + 1)
  have powerBound := Fraction.Order.Arithmetic.pow_le_pow_direct
    (Data.Gaussian.Norm.Basic.normSq_nonneg u) disk index
  calc
    (-(1 / ((index + 2 : Nat) : Fraction.Rational))) ^ 2 *
          Data.Gaussian.Norm.Basic.normSq u ^ index ≤
        1 * (1 / 4 : Fraction.Rational) ^ index :=
      Fraction.Order.Arithmetic.mul_le_mul_direct coefficientBound powerBound
        (Fraction.Order.Arithmetic.pow_nonneg_direct (Data.Gaussian.Norm.Basic.normSq_nonneg u) index)
        (by decide)
    _ = (1 / 4 : Fraction.Rational) ^ index :=
      Fraction.Field.one_mul _

/-- Every finite second-relative logarithm sample has squared norm at most four on the quarter-quadrance disk.

The sample sums exactly the retained finite prefix of indexed terms.
Its geometric norm bound uses the same quarter-power term estimates on the disk. -/
theorem log1pSecondRelSample_bounded {u : Data.Gaussian.Basic.Canonical}
    (disk : Data.Gaussian.Norm.Basic.normSq u ≤ 1 / 4) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (Sample.log1pSecondRelSample u index) ≤ 4 := by
  exact FiniteSum.Geometric.sum_geometric_normSq_le
    (Sample.log1pSecondRelTerm u) (index + 1) 1 (by decide)
      (fun termIndex => by
        simpa only [Fraction.Field.one_mul] using
          Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Bounds.log1pSecondRelTerm_bound disk termIndex)

open Purelib.Data.Nat in
/-- Later second-relative logarithm samples stay within the earlier index's scale-one quarter-radius allowance.

The retained index order identifies the later prefix as the earlier prefix
plus its exact natural-difference tail. The geometric term bound controls that
finite tail at the original earlier index. -/
theorem log1pSecondRelSample_later_close {u : Data.Gaussian.Basic.Canonical}
    (disk : Data.Gaussian.Norm.Basic.normSq u ≤ 1 / 4) {earlier later : Nat}
    (order : earlier ≤ later) :
    Data.Gaussian.Norm.Basic.normSq
        (Sample.log1pSecondRelSample u later -
          Sample.log1pSecondRelSample u earlier) ≤
      Geometric.Basic.quarterRadius 1 earlier := by
  obtain ⟨extra, rfl⟩ : ∃ extra : Nat, later = earlier + extra :=
    ⟨later - earlier, (Subtraction.add_sub_of_le order).symm⟩
  rw [Sample.log1pSecondRelSample, Sample.log1pSecondRelSample,
    show earlier + extra + 1 = earlier + 1 + extra by ring1,
    Prefix.sum_append]
  have tailBound :
      Data.Gaussian.Norm.Basic.normSq
          (Prefix.sum
            (fun index => Sample.log1pSecondRelTerm u (earlier + 1 + index))
              extra) ≤
        4 * (1 / 4 : Fraction.Rational) ^ (earlier + 1) := by
    exact FiniteSum.Geometric.sum_geometric_normSq_le
      (fun index => Sample.log1pSecondRelTerm u (earlier + 1 + index)) extra
      ((1 / 4 : Fraction.Rational) ^ (earlier + 1))
      (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) _)
      (fun index => by
        calc
          Data.Gaussian.Norm.Basic.normSq (Sample.log1pSecondRelTerm u (earlier + 1 + index)) ≤
              (1 / 4 : Fraction.Rational) ^ (earlier + 1 + index) :=
            Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Bounds.log1pSecondRelTerm_bound disk _
          _ = (1 / 4 : Fraction.Rational) ^ (earlier + 1) *
              (1 / 4 : Fraction.Rational) ^ index :=
            Quarter.quarterPower_shift earlier index)
  calc
    Data.Gaussian.Norm.Basic.normSq
        (Prefix.sum
              (Sample.log1pSecondRelTerm u) (earlier + 1) +
            Prefix.sum
              (fun index => Sample.log1pSecondRelTerm u (earlier + 1 + index))
                extra -
          Prefix.sum
            (Sample.log1pSecondRelTerm u) (earlier + 1)) =
      Data.Gaussian.Norm.Basic.normSq
        (Prefix.sum
          (fun index => Sample.log1pSecondRelTerm u (earlier + 1 + index))
            extra) := by
        congr 1
        apply Data.Gaussian.Basic.ext <;>
          simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im] <;> ring1
    _ ≤ 4 * (1 / 4 : Fraction.Rational) ^ (earlier + 1) := tailBound
    _ = Geometric.Basic.quarterRadius 1 earlier := by
      rw [Quarter.four_mul_quarterPower_succ,
        Geometric.Basic.quarterRadius_eq_mul_pow,
        Fraction.Field.one_mul]
end Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Bounds

end
