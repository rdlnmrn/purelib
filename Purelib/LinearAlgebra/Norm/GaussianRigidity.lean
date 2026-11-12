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

open Purelib.Data.Gaussian

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
private theorem normSum_nonnegative (values : List Basic.Canonical) : 0 ≤
  Norm.Sum.Basic.gaussianNormSqSum values := by
  induction values with
  | nil => exact le_rfl
  | cons value values ih => exact add_nonneg (Basic.Canonical.normSq_nonneg value) ih

/-- A uniform squared-norm bound controls the finite norm sum.

Each retained occurrence contributes at most the supplied bound. Structural
induction adds one bound per occurrence without changing the norm-sum recurrence. -/
private theorem normSum_bounded (values : List Basic.Canonical) (bound : Fraction.Rational)
    (bounded : ∀ value ∈ values, Norm.Basic.normSq value ≤ bound) :
    Norm.Sum.Basic.gaussianNormSqSum values ≤ (values.length : Fraction.Rational) * bound := by
  induction values with
  | nil => change (0 : Fraction.Rational) ≤ 0 * bound; rw [Fraction.Field.zero_mul_direct]
  | cons value values ih =>
      exact (add_le_add (show Basic.Canonical.normSq value ≤ bound from
        by simpa only [Norm.Basic.normSq_eq_canonical] using bounded value List.mem_cons_self)
        (ih (fun value member => bounded value (List.mem_cons_of_mem _ member)))).trans_eq (by
          simp only [List.length_cons, Algebra.NatCast.add, Nat.cast_one]
          ring1)

/-- A retained member squared norm is bounded by the complete finite norm sum.

The displayed membership locates either the current head or a retained tail
occurrence. All other squared norms are nonnegative. -/
private theorem member_norm_le_sum {values : List Basic.Canonical} {value : Basic.Canonical}
  (member : value ∈ values) :
    Norm.Basic.normSq value ≤ Norm.Sum.Basic.gaussianNormSqSum values := by
  rw [Norm.Basic.normSq_eq_canonical]
  induction values with
  | nil => exact (List.not_mem_nil member).elim
  | cons head tail ih =>
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact le_add_of_nonneg_right (normSum_nonnegative tail)
      · exact (ih member).trans (le_add_of_nonneg_left (Basic.Canonical.normSq_nonneg head))

/-- The Gaussian variance is expressed by the retained finite sums.

Subtracting the same mean from every entry separates the original squared-norm
sum, the length-scaled mean norm and the dot product of the original sum. -/
theorem gaussian_variance_identity (values : List Basic.Canonical) (mean : Basic.Canonical)
  :
    Norm.Sum.Basic.gaussianNormSqSum (values.map (fun value => value - mean)) =
      Norm.Sum.Basic.gaussianNormSqSum values + (values.length : Fraction.Rational) *
        Norm.Basic.normSq mean -
        2 * ((Norm.Sum.Basic.gaussianSum values).re * mean.re +
          (Norm.Sum.Basic.gaussianSum values).im * mean.im) := by
  induction values with
  | nil =>
      change (0 : Fraction.Rational) = 0 + 0 * Norm.Basic.normSq mean - 2 * (0 * mean.re + 0 *
        mean.im)
      ring1
  | cons value values ih =>
      simp only [List.map_cons, Norm.Sum.Basic.gaussianNormSqSum,
        Norm.Sum.Basic.gaussianSum, List.length_cons, Algebra.NatCast.add, Nat.cast_one, ih,
        Norm.Basic.normSq, Basic.Canonical.normSq, Basic.sub_re,
          Basic.sub_im, Basic.add_re, Basic.add_im]
      ring1

/-- Saturation of the finite displacement bound fixes every entry.

The retained sum is the list length times its mean, and every entry has
squared norm at most the mean squared norm. Nonnegativity forces each
displacement norm to vanish. -/
theorem all_eq_of_sum_and_norm_bound (values : List Basic.Canonical) (mean :
  Basic.Canonical)
    (total : Norm.Sum.Basic.gaussianSum values = (values.length : Basic.Canonical) *
      mean)
    (bounded : ∀ value ∈ values, Norm.Basic.normSq value ≤
      Norm.Basic.normSq mean) :
    ∀ value ∈ values, value = mean := by
  have variance := gaussian_variance_identity values mean
  rw [total, Basic.mul_re, Basic.mul_im, Cast.natCast_re,
    Cast.natCast_im] at variance
  have varianceEq : Norm.Sum.Basic.gaussianNormSqSum (values.map (fun value => value - mean)) =
      Norm.Sum.Basic.gaussianNormSqSum values - (values.length : Fraction.Rational) *
        Norm.Basic.normSq mean :=
    variance.trans (by dsimp only [Norm.Basic.normSq]; ring1)
  have zero : Norm.Sum.Basic.gaussianNormSqSum (values.map (fun value => value - mean)) = 0 := by
    apply le_antisymm _ (normSum_nonnegative _)
    rw [varianceEq]
    exact Fraction.Order.Boundary.sub_nonpositive_iff.mpr (normSum_bounded values
      (Norm.Basic.normSq mean) bounded)
  intro value member
  have small := member_norm_le_sum (Data.List.Map.mem_map.mpr ⟨value, member, rfl⟩ :
    value - mean ∈ values.map (fun entry => entry - mean))
  rw [zero] at small
  exact Algebra.Group.eq_of_sub_eq_zero (Norm.Basic.normSq_eq_zero.mp (le_antisymm small
    (Norm.Basic.normSq_nonneg _)))

end Purelib.LinearAlgebra.Norm

end
