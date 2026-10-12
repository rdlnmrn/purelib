module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.NatCast
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Indexed form of the existing finite-sum Cauchy budget. -/

namespace Purelib.Data.Gaussian.Norm.Sum.Indexed

open Purelib

open Purelib.Algebra
open Purelib.Data.Gaussian
open Purelib.Data.List
open Purelib.Data.Rat

/-- The original finite-index Gaussian sum equals the recursive sum of its exact List.ofFn readback. -/
theorem sumFin_eq_gaussianSum {count : Nat} (values : Fin count → Basic.Canonical) :
    FiniteSum.Fin.sumFin values = Basic.gaussianSum (List.ofFn values) := by
  induction count with
  | zero => rfl
  | succ count ih => rw [FiniteSum.Fin.sumFin_succ, OfFn.Basic.ofFn_succ, Basic.gaussianSum, ih]

/-- A pointwise finite-index norm bound holds for each entry in its List.ofFn readback.

The original successor table separates the zero index from its retained bounded
tail. Direct membership alternatives specialize the same supplied bound at that index. -/
private theorem ofFn_bounded {count : Nat} (values : Fin count → Basic.Canonical) (bound : Fraction.Rational)
    (bounded : ∀ index, Basic.normSq (values index) ≤ bound) : ∀ value ∈ List.ofFn values,
      Basic.normSq value ≤ bound := by
  induction count with
  | zero => intro value member; cases member
  | succ count ih =>
      intro value member
      rw [OfFn.Basic.ofFn_succ] at member
      rcases Membership.mem_cons.mp member with equal | member
      · rw [equal]; exact bounded 0
      · exact ih (fun index => values index.succ) (fun index => bounded index.succ) value member

/-- A uniform finite-index norm bound bounds the sum norm by the squared index count.

The original finite sum equals its unchanged List.ofFn materialization.
Its exact retained length turns the list norm estimate into the displayed count budget. -/
theorem normSq_sumFin_le {count : Nat} (values : Fin count → Basic.Canonical) (bound : Fraction.Rational)
    (bounded : ∀ index, Basic.normSq (values index) ≤ bound) : Basic.normSq
      (FiniteSum.Fin.sumFin values) ≤ (count : Fraction.Rational) ^ 2 * bound := by
  rw [Norm.Sum.Indexed.sumFin_eq_gaussianSum]
  have estimate := Norm.Sum.Bounds.normSq_sum_le (List.ofFn values) bound (Norm.Sum.Indexed.ofFn_bounded values bound
    bounded)
  rw [OfFn.Basic.length_ofFn] at estimate
  exact estimate.trans_eq (by ring1)

/-- The norm-square sum of a finite-index list readback equals the original finite sum of pointwise squared norms. -/
private theorem gaussianNormSqSum_ofFn {count : Nat} (values : Fin count → Basic.Canonical) :
    Norm.Sum.Basic.gaussianNormSqSum (List.ofFn values) =
      FiniteSum.Fin.sumFin (fun index => Basic.normSq (values index)) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [OfFn.Basic.ofFn_succ, Norm.Sum.Basic.gaussianNormSqSum,
        inductionHypothesis, FiniteSum.Fin.sumFin_succ]
      rw [Norm.Basic.normSq_eq_canonical]

/-- The norm square of a finite-index sum is bounded by count times its squared-norm sum.

The original list readback retains every bounded index and has exactly that
count. Both Gaussian sum and squared-norm sum equal their retained finite-index sums. -/
theorem normSq_sumFin_le_sum {count : Nat} (values : Fin count → Basic.Canonical) :
    Basic.normSq (FiniteSum.Fin.sumFin values) ≤
      (count : Fraction.Rational) * FiniteSum.Fin.sumFin (fun index => Basic.normSq (values index)) := by
  rw [Norm.Sum.Indexed.sumFin_eq_gaussianSum]
  have estimate := Norm.Sum.Basic.normSq_gaussianSum_le (List.ofFn values)
  rw [OfFn.Basic.length_ofFn, Norm.Sum.Indexed.gaussianNormSqSum_ofFn] at estimate
  rw [Norm.Basic.normSq_eq_canonical]
  exact estimate

/-!
# Indexed Gaussian norm and displacement bounds

Finite summation and the exact list readback use the same retained indices.
Pointwise squared-norm bounds control the sum and the difference of two such sums.
-/

/-! ## Extracting affine errors from prepared constant path models -/

/-- Pointwise squared-norm bounds bound the finite sum norm by count times their sum.

The original list readback supplies the finite norm-sum estimate and exact
count. Pointwise monotonicity then transports each supplied bound at its original index. -/
theorem normSq_sumFin_le_count_mul_sumFin {count : Nat}
    (values : Fin count -> Basic.Canonical) (bounds : Fin count -> Fraction.Rational)
    (bounded : forall index,
      Basic.normSq (values index) <=
        bounds index) :
    Basic.normSq
        (FiniteSum.Fin.sumFin values) <=
      (count : Fraction.Rational) *
        FiniteSum.Fin.sumFin bounds := by
  rw [Norm.Sum.Indexed.sumFin_eq_gaussianSum]
  calc
    Basic.normSq
        (Basic.gaussianSum (List.ofFn values)) <=
      ((List.ofFn values).length : Fraction.Rational) *
        Norm.Sum.Basic.gaussianNormSqSum (List.ofFn values) :=
      by
        rw [Norm.Basic.normSq_eq_canonical]
        exact Norm.Sum.Basic.normSq_gaussianSum_le (List.ofFn values)
    _ = (count : Fraction.Rational) *
        FiniteSum.Fin.sumFin
          (fun index =>
            Basic.normSq (values index)) := by
      rw [OfFn.Basic.length_ofFn, ← Norm.Sum.Indexed.gaussianNormSqSum_ofFn]
    _ <= (count : Fraction.Rational) *
        FiniteSum.Fin.sumFin bounds :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (FiniteSum.Rational.Order.Positivity.sumFin_mono
          (fun index =>
            Basic.normSq (values index))
          bounds bounded)
        (Fraction.Order.NatCast.qNatNonnegative count)

/-- Pointwise displacement bounds bound the squared distance between finite sums by the index count times their sum. -/
theorem normSq_sumFin_sub_le_count_mul_sumFin {count : Nat}
    (left right : Fin count -> Basic.Canonical) (bounds : Fin count -> Fraction.Rational)
    (bounded : forall index,
      Basic.normSq
          (left index - right index) <= bounds index) :
    Basic.normSq
        (FiniteSum.Fin.sumFin left -
          FiniteSum.Fin.sumFin right) <=
      (count : Fraction.Rational) *
        FiniteSum.Fin.sumFin bounds := by
  rw [<- FiniteSum.Fin.sumFin_sub]
  exact Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin
    (fun index => left index - right index) bounds bounded

end Purelib.Data.Gaussian.Norm.Sum.Indexed

end

namespace Purelib.Data.Gaussian.Norm.Sum.Indexed

open Purelib.Algebra
open Purelib.Data.Gaussian

/-- The Gaussian sum of a list of indexed sums equals the indexed sum of list readings.

Both sums retain the original list order and finite index family. Structural
list induction interchanges only scalar addition at the current head. -/
public theorem gaussianSum_sumFin {Alpha : Type u} {count : Nat}
    (entries : List Alpha) (values : Alpha → Fin count → Basic.Canonical) :
    Basic.gaussianSum (entries.map (fun entry => FiniteSum.Fin.sumFin (values entry))) =
      FiniteSum.Fin.sumFin (fun position => Basic.gaussianSum (entries.map (fun entry => values entry
        position))) := by
  induction entries with
  | nil => exact (FiniteSum.Fin.sumFin_zero).symm
  | cons head tail ih =>
    rw [List.map_cons, Basic.gaussianSum, ih, ← FiniteSum.Fin.sumFin_add]
    exact FiniteSum.Fin.sumFin_congr (fun _ => rfl)

/-- The finite indexed readings of a list equal the Gaussian sum of its mapped entries.

The same displayed list order and retained element bounds define both sums.
Structural list induction follows those exact indices and original additions. -/
public theorem sumFin_map {Item : Type u} (entries : List Item) (value : Item → Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun index : Fin entries.length => value (entries[index.val]'index.isLt)) =
      Basic.gaussianSum (entries.map value) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
    rw [FiniteSum.Fin.sumFin_succ]
    exact congrArg (value head + ·) ih

end Purelib.Data.Gaussian.Norm.Sum.Indexed
