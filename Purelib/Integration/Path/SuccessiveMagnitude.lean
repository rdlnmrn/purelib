module
import Purelib.Data.Fin
import Purelib.Data.Nat.Remainder
import Purelib.Data.List.Membership
-- The public displacement formula retains the original successor-size zero index.
public import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! A finite prefix of bounded increments controls displacement from its origin. -/
namespace Purelib.Integration.Path.SuccessiveMagnitude

open Purelib.Data.Gaussian in
open Purelib.Riemann.Periods in
/-- Express an original indexed displacement as a retained list of bounded successive increments.

The witness list has the exact index length and sums to the original vertex value minus the first value. -/
private theorem prefix_terms {count : Nat} (values : Fin (count + 1) → Basic.Canonical) (bound :
  CenteredBilinearPath.Coordinate)
    (steps : ∀ index : Fin count, Data.Gaussian.Norm.Basic.normSq (values index.succ - values index.castSucc) ≤ bound)
    (index : Fin (count + 1)) :
    ∃ terms : List Basic.Canonical, terms.length = index.val ∧
      (∀ term ∈ terms, Data.Gaussian.Norm.Basic.normSq term ≤ bound) ∧ values index - values 0 =
        Data.Gaussian.Norm.Sum.Basic.gaussianSum terms := by
  induction index using Purelib.Data.Fin.induction with
  | zero =>
      have first : (⟨0, Nat.zero_lt_succ count⟩ : Fin (count + 1)) = 0 := by
        apply Fin.ext
        exact (Purelib.Data.Nat.Remainder.mod_eq_of_lt (Nat.zero_lt_succ count)).symm
      refine ⟨[], rfl, (fun _ member => (List.not_mem_nil member).elim), ?_⟩
      change values ⟨0, Nat.zero_lt_succ count⟩ - values 0 = 0
      rw [first]
      ring1
  | succ index ih =>
      obtain ⟨terms, length, bounded, equal⟩ := ih
      refine ⟨(values index.succ - values index.castSucc) :: terms, congrArg (· + 1) length, ?_, ?_⟩
      · intro term member
        rcases Purelib.Data.List.Membership.mem_cons.mp member with same | present
        · rw [same]; exact steps index
        · exact bounded term present
      · change values index.succ - values 0 = (values index.succ - values index.castSucc) +
          Data.Gaussian.Norm.Sum.Basic.gaussianSum terms
        rw [← equal]
        ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
/-- Uniform successive-increment bounds control every original displacement from the initial vertex.

The squared-norm estimate is the original edge count squared times the nonnegative common step bound. -/
theorem successive_magnitude {count : Nat} (values : Fin (count + 1) → Basic.Canonical) {bound :
  CenteredBilinearPath.Coordinate}
    (nonnegative : 0 ≤ bound)
    (steps : ∀ index : Fin count, Data.Gaussian.Norm.Basic.normSq (values index.succ - values index.castSucc) ≤ bound)
    (index : Fin (count + 1)) : Data.Gaussian.Norm.Basic.normSq (values index - values 0) ≤ (count :
      CenteredBilinearPath.Coordinate) ^ 2 * bound := by
  obtain ⟨terms, length, bounded, equal⟩ := SuccessiveMagnitude.prefix_terms values bound steps index
  rw [equal]
  have estimate := Norm.Sum.Bounds.normSq_sum_le terms bound bounded
  rw [length] at estimate
  apply estimate.trans
  have square := Fraction.Order.Arithmetic.pow_le_pow_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le index.val))
    (Fraction.Cast.Order.natCast_le_direct (Nat.le_of_lt_succ index.isLt)) 2
  exact (show (index.val : CenteredBilinearPath.Coordinate) * ((index.val : CenteredBilinearPath.Coordinate) * bound) =
    (index.val : CenteredBilinearPath.Coordinate) ^ 2 * bound by ring1).le.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct square nonnegative)

end Purelib.Integration.Path.SuccessiveMagnitude
