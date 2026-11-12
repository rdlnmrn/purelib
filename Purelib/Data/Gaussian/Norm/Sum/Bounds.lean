module
public import Purelib.Algebra.FiniteSum.List.Basic
public import Batteries.Data.List.Basic
import Purelib.Data.List.Map
import Purelib.Algebra.NatCast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
public section

/-!
# Uniform bounds for finite Gaussian sums

A common squared-norm bound controls the sum of entry norms and the norm of
their Gaussian sum. The bounds retain the actual list length, including zero.
-/

namespace Purelib.Data.Gaussian.Norm.Sum.Bounds

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A uniform entry squared-norm bound bounds their sum by list length times that bound.

Structural recursion adds the original head's scalar bound to the retained
tail bound. The exact natural length cast expands into the same two scalar summands. -/
theorem normSum_le (values : List Basic.Canonical) (bound :
  Fraction.Rational)
    (bounded : ∀ value ∈ values, Basic.normSq value ≤ bound) :
    Norm.Sum.Basic.gaussianNormSqSum values ≤ (values.length : Fraction.Rational) * bound := by
  induction values with
  | nil => change (0 : Fraction.Rational) ≤ 0 * bound; rw [Fraction.Field.zero_mul_direct]
  | cons value values ih =>
      have step := add_le_add (show Basic.Canonical.normSq value ≤ bound from
        by simpa only [Norm.Basic.normSq_eq_canonical] using bounded value (List.mem_cons_self ..))
        (ih fun other member => bounded other (List.mem_cons_of_mem _ member))
      apply step.trans_eq
      simp only [List.length_cons, NatCast.add, Nat.cast_one]
      ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A uniform list-entry squared-norm bound bounds the list-sum norm by length squared times the bound. -/
theorem normSq_sum_le (values : List Basic.Canonical) (bound :
  Fraction.Rational)
    (bounded : ∀ value ∈ values, Basic.normSq value ≤ bound) :
    Basic.normSq (Basic.gaussianSum values) ≤ (values.length : Fraction.Rational) *
      ((values.length : Fraction.Rational) * bound) := by
  apply (show Basic.normSq (Basic.gaussianSum values) ≤
      (values.length : Fraction.Rational) * Norm.Sum.Basic.gaussianNormSqSum values from
    by simpa only [Norm.Basic.normSq_eq_canonical] using Norm.Sum.Basic.normSq_gaussianSum_le values).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (normSum_le values bound bounded)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))
end Purelib.Data.Gaussian.Norm.Sum.Bounds

end

public section

namespace Purelib.Data.Gaussian.Norm.Sum.Bounds

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Algebra.FiniteSum.List.Basic (scalarSum)

/-- Ordered pointwise squared-norm payments bound the same finite sum of squared norms.

The existing paired-list relation retains every error and its corresponding
payment in order. Structural recursion adds the actual head payment to the
unchanged tail without replacing the individual bounds by a uniform one.
-/
theorem normSum_le_scalarSum {values : List Basic.Canonical} {payments : List Fraction.Rational}
    (paid : List.Forall₂ (fun value payment => Basic.normSq value ≤ payment) values payments) :
    Norm.Sum.Basic.gaussianNormSqSum values ≤ scalarSum payments := by
  induction paid with
  | nil => exact Fraction.Order.Basic.le_refl 0
  | @cons value payment values payments first _ ih =>
      change Basic.Canonical.normSq value + Norm.Sum.Basic.gaussianNormSqSum values ≤
        payment + scalarSum payments
      rewrite [Norm.Basic.normSq_eq_canonical] at first
      exact Fraction.Order.Arithmetic.add_le_add_direct first ih

/-- A common squared-norm bound controls the difference of two ordered Gaussian sums.

The finite list retains both readings at each entry. Summing their pointwise
differences yields the exact length-squared factor without changing either sum. -/
public theorem normSq_gaussianSum_map_sub_le {Alpha : Type u} (values : List Alpha) (left right : Alpha →
  Basic.Canonical) {bound : Fraction.Rational}
    (small : ∀ value ∈ values, Basic.normSq (left value - right value) ≤ bound) :
    Basic.normSq (Basic.gaussianSum (values.map left) - Basic.gaussianSum
      (values.map right)) ≤
      (values.length : Fraction.Rational) * ((values.length : Fraction.Rational) * bound) := by
  have estimate := normSq_sum_le (values.map (fun value => left value - right value)) bound (by
    intro value member
    obtain ⟨original, member, equal⟩ := Data.List.Map.mem_map.mp member
    rw [← equal]
    exact small original member)
  rw [Norm.Sum.Basic.gaussianSum_map_sub, Data.List.Map.length_map] at estimate
  exact estimate

end Purelib.Data.Gaussian.Norm.Sum.Bounds

end
