module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
import Purelib.Algebra.FiniteSum.Prefix
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Sample
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Quarter
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.FiniteSum.Geometric
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
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

open Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.Gaussian

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the logarithm

This module works with the finite local coordinate `log(1+u)`, on the
displayed rational disk `normSq u ≤ 1/4`.  Its relative forms and derivative
are finite alternating sums.  The reciprocal derivative law is expressed by
an exact finite geometric remainder and then by finite-request operational
equivalence.  No infinitesimal, limit, infinite series, or global logarithm
branch is introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Bounds

/-- Every finite one-plus logarithm derivative sample has squared norm at most four on the quarter-quadrance disk. -/
theorem log1pDerivativeSample_bounded {u :
  Data.Gaussian.Basic.Canonical}
    (disk : Data.Gaussian.Norm.Basic.normSq u ≤ 1 / 4) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (Sample.log1pDerivativeSample u index) ≤ 4 := by
  exact FiniteSum.Geometric.sum_geometric_normSq_le
    (fun termIndex => (-u) ^ termIndex) (index + 1) 1 (by decide)
      (fun termIndex => by
        rw [Power.normSq_pow, Data.Gaussian.Norm.Basic.normSq_neg]
        simpa only [Fraction.Field.one_mul] using
          Fraction.Order.Arithmetic.pow_le_pow_direct
            (Data.Gaussian.Norm.Basic.normSq_nonneg u) disk termIndex)

open Purelib.Data.Nat in
/-- Later finite one-plus logarithm derivative samples stay within the earlier index's scale-one quarter-radius
allowance. -/
theorem log1pDerivativeSample_later_close {u :
  Data.Gaussian.Basic.Canonical}
    (disk : Data.Gaussian.Norm.Basic.normSq u ≤ 1 / 4) {earlier later : Nat}
    (order : earlier ≤ later) :
    Data.Gaussian.Norm.Basic.normSq
        (Sample.log1pDerivativeSample u later -
          Sample.log1pDerivativeSample u earlier) ≤
      Geometric.Basic.quarterRadius 1 earlier := by
  obtain ⟨extra, rfl⟩ : ∃ extra, later = earlier + extra :=
    ⟨later - earlier, (Subtraction.add_sub_of_le order).symm⟩
  rw [Sample.log1pDerivativeSample, Sample.log1pDerivativeSample,
    show earlier + extra + 1 = earlier + 1 + extra by ring1,
    Prefix.sum_append]
  have tailBound :=
    FiniteSum.Geometric.sum_geometric_normSq_le
      (fun index => (-u) ^ (earlier + 1 + index)) extra
      ((1 / 4 : Fraction.Rational) ^ (earlier + 1))
      (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) _)
      (fun index => by
        rw [Power.normSq_pow, Data.Gaussian.Norm.Basic.normSq_neg]
        calc
          Data.Gaussian.Norm.Basic.normSq u ^ (earlier + 1 + index) ≤
              (1 / 4 : Fraction.Rational) ^ (earlier + 1 + index) :=
            Fraction.Order.Arithmetic.pow_le_pow_direct
              (Data.Gaussian.Norm.Basic.normSq_nonneg u) disk _
          _ = (1 / 4 : Fraction.Rational) ^ (earlier + 1) *
              (1 / 4 : Fraction.Rational) ^ index :=
            Quarter.quarterPower_shift earlier index)
  calc
    Data.Gaussian.Norm.Basic.normSq
        (Prefix.sum
              (fun termIndex => (-u) ^ termIndex) (earlier + 1) +
            Prefix.sum
              (fun index => (-u) ^ (earlier + 1 + index)) extra -
          Prefix.sum
            (fun termIndex => (-u) ^ termIndex) (earlier + 1)) =
      Data.Gaussian.Norm.Basic.normSq
        (Prefix.sum
          (fun index => (-u) ^ (earlier + 1 + index)) extra) := by
        congr 1
        apply Data.Gaussian.Basic.ext <;>
          simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im] <;> ring1
    _ ≤ 4 * (1 / 4 : Fraction.Rational) ^ (earlier + 1) := tailBound
    _ = Geometric.Basic.quarterRadius 1 earlier := by
      rw [Quarter.four_mul_quarterPower_succ,
        Geometric.Basic.quarterRadius_eq_mul_pow,
        Fraction.Field.one_mul]
end Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Bounds

end
