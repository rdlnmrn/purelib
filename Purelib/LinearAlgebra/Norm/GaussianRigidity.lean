module
import Purelib.Algebra.Group.Basic
import Purelib.Algebra.NatCast
import Purelib.Data.List.Membership
public import Purelib.Algebra.Group.Negation
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section

open Purelib

open Purelib.Data.Rat

/-!
# Equality forced by a finite displacement budget

If a displayed list sums to its length times a given vector, and every
squared norm is at most that vector's squared norm, every entry equals the
vector. The proof is the exact finite variance identity and nonnegativity.
-/

public section

namespace Purelib.LinearAlgebra.Norm

open Purelib.Data.Gaussian.Basic.Canonical

/-- The finite sum of Gaussian squared norms is nonnegative. -/
private theorem normSum_nonnegative (values : List Data.Gaussian.Basic.Canonical) : 0 ≤
  Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum values := by
  induction values with
  | nil => exact le_rfl
  | cons value values ih => exact add_nonneg (Data.Gaussian.Basic.Canonical.normSq_nonneg value) ih

/-- A uniform squared-norm bound controls the finite norm sum.

Each retained occurrence contributes at most the supplied bound. Structural
induction adds one bound per occurrence without changing the norm-sum recurrence. -/
private theorem normSum_bounded (values : List Data.Gaussian.Basic.Canonical) (bound : Fraction.Rational)
    (bounded : ∀ value ∈ values, Data.Gaussian.Norm.Basic.normSq value ≤ bound) :
    Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum values ≤ (values.length : Fraction.Rational) * bound := by
  induction values with
  | nil => change (0 : Fraction.Rational) ≤ 0 * bound; rw [Fraction.Field.zero_mul_direct]
  | cons value values ih =>
      exact (add_le_add (show Data.Gaussian.Basic.Canonical.normSq value ≤ bound from
        by simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using bounded value List.mem_cons_self)
        (ih (fun value member => bounded value (List.mem_cons_of_mem _ member)))).trans_eq (by
          simp only [List.length_cons, Algebra.NatCast.add, Nat.cast_one]
          ring1)

/-- A retained member squared norm is bounded by the complete finite norm sum.

The displayed membership locates either the current head or a retained tail
occurrence. All other squared norms are nonnegative. -/
private theorem member_norm_le_sum {values : List Data.Gaussian.Basic.Canonical} {value : Data.Gaussian.Basic.Canonical}
  (member : value ∈ values) :
    Data.Gaussian.Norm.Basic.normSq value ≤ Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum values := by
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  induction values with
  | nil => exact (List.not_mem_nil member).elim
  | cons head tail ih =>
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact le_add_of_nonneg_right (normSum_nonnegative tail)
      · exact (ih member).trans (le_add_of_nonneg_left (Data.Gaussian.Basic.Canonical.normSq_nonneg head))

/-- The Gaussian variance is expressed by the retained finite sums.

Subtracting the same mean from every entry separates the original squared-norm
sum, the length-scaled mean norm and the dot product of the original sum. -/
theorem gaussian_variance_identity (values : List Data.Gaussian.Basic.Canonical) (mean : Data.Gaussian.Basic.Canonical)
  :
    Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum (values.map (fun value => value - mean)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum values + (values.length : Fraction.Rational) *
        Data.Gaussian.Norm.Basic.normSq mean -
        2 * ((Data.Gaussian.Norm.Sum.Basic.gaussianSum values).re * mean.re +
          (Data.Gaussian.Norm.Sum.Basic.gaussianSum values).im * mean.im) := by
  induction values with
  | nil =>
      change (0 : Fraction.Rational) = 0 + 0 * Data.Gaussian.Norm.Basic.normSq mean - 2 * (0 * mean.re + 0 *
        mean.im)
      ring1
  | cons value values ih =>
      simp only [List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum,
        Data.Gaussian.Norm.Sum.Basic.gaussianSum, List.length_cons, Algebra.NatCast.add, Nat.cast_one, ih,
        Data.Gaussian.Norm.Basic.normSq, Data.Gaussian.Basic.Canonical.normSq, Data.Gaussian.Basic.sub_re,
          Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im]
      ring1

/-- Saturation of the finite displacement bound fixes every entry.

The retained sum is the list length times its mean, and every entry has
squared norm at most the mean squared norm. Nonnegativity forces each
displacement norm to vanish. -/
theorem all_eq_of_sum_and_norm_bound (values : List Data.Gaussian.Basic.Canonical) (mean :
  Data.Gaussian.Basic.Canonical)
    (total : Data.Gaussian.Norm.Sum.Basic.gaussianSum values = (values.length : Data.Gaussian.Basic.Canonical) *
      mean)
    (bounded : ∀ value ∈ values, Data.Gaussian.Norm.Basic.normSq value ≤
      Data.Gaussian.Norm.Basic.normSq mean) :
    ∀ value ∈ values, value = mean := by
  have variance := gaussian_variance_identity values mean
  rw [total, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im, Data.Gaussian.Cast.natCast_re,
    Data.Gaussian.Cast.natCast_im] at variance
  have varianceEq : Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum (values.map (fun value => value - mean)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum values - (values.length : Fraction.Rational) *
        Data.Gaussian.Norm.Basic.normSq mean :=
    variance.trans (by dsimp only [Data.Gaussian.Norm.Basic.normSq]; ring1)
  have zero : Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum (values.map (fun value => value - mean)) = 0 := by
    apply le_antisymm _ (normSum_nonnegative _)
    rw [varianceEq]
    exact Fraction.Order.Boundary.sub_nonpositive_iff.mpr (normSum_bounded values
      (Data.Gaussian.Norm.Basic.normSq mean) bounded)
  intro value member
  have small := member_norm_le_sum (Data.List.Map.mem_map.mpr ⟨value, member, rfl⟩ :
    value - mean ∈ values.map (fun entry => entry - mean))
  rw [zero] at small
  exact Algebra.Group.eq_of_sub_eq_zero (Data.Gaussian.Norm.Basic.normSq_eq_zero.mp (le_antisymm small
    (Data.Gaussian.Norm.Basic.normSq_nonneg _)))

end Purelib.LinearAlgebra.Norm

end
