module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.NatCast
public import Purelib.Approximation.Rational.Budget.Weighted
public import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.IncrementArea
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Select a coefficient-independent family budget before chart acquisition.
Each common parent pays four copies of the chosen allowance: fan, arc,
internal connectors and source restoration. -/
namespace Purelib.Integration.Budget.Trace.Family

open Purelib.Integration.Path.IncrementArea (Coordinate)
open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Integration.Path in
/-- Sum each retained count times the common energy plus the per-parent allowance in original family order. -/
@[expose] def basisFamilyLoss (counts : List Nat) (energy allowance : IncrementArea.Coordinate) : Coordinate :=
  match counts with
  | [] => 0
  | count :: rest => (count : IncrementArea.Coordinate) * energy + allowance +
    Purelib.Integration.Budget.Trace.Family.basisFamilyLoss rest energy allowance

open Purelib in
open Purelib.Integration in
open Purelib.Integration.Path in
/-- At zero energy and four equal allowances, the exact family loss is four times the parent count times the allowance.
-/
theorem basisFamilyLoss_common (counts : List Nat) (allowance : IncrementArea.Coordinate) :
    Budget.Trace.Family.basisFamilyLoss counts 0 (allowance + allowance + allowance + allowance) =
      (4 * (counts.length : IncrementArea.Coordinate)) * allowance := by
  induction counts with
  | nil => change (0 : IncrementArea.Coordinate) = (4 * 0) * allowance; ring1
  | cons count rest ih =>
      change (count : IncrementArea.Coordinate) * 0 + (allowance + allowance + allowance + allowance) +
        Budget.Trace.Family.basisFamilyLoss rest 0 (allowance + allowance + allowance + allowance) = _
      rw [ih]
      simp only [List.length_cons, Algebra.NatCast.add, Nat.cast_one]
      ring1

open Purelib.Approximation.Rational in
open Purelib.Integration.Path in
set_option genInjectivity false in
/-- A positive retained common allowance and exact aggregate loss bounded by the original family target.

The allowance respects the supplied ceiling and the weighted target budget, preserving the original parent count and
factor of four. -/
structure BasisFamilyAllowance (parentCount : Nat) (target : IncrementArea.Coordinate) where
  /-- The retained original upper ceiling for the common family allowance. -/ ceiling : IncrementArea.Coordinate
  /-- The retained positive common allowance for the original family. -/ allowance : IncrementArea.Coordinate
  /-- The allowance is the exact minimum of the original ceiling and weighted target budget. -/ allowance_eq : allowance
    = min ceiling (Budget.Weighted.allowance target (4 * (parentCount : IncrementArea.Coordinate)))
  /-- The retained common allowance is positive. -/ positive : 0 < allowance
  /-- The cached exact aggregate family loss. -/ loss : IncrementArea.Coordinate
  /-- The cached loss is four times the original parent count times the retained allowance. -/ loss_eq : loss = (4 *
    (parentCount : IncrementArea.Coordinate)) * allowance
  /-- The exact retained aggregate loss is bounded by the original target. -/ paid : loss ≤ target

constructive_injectivity BasisFamilyAllowance

namespace BasisFamilyAllowance

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Integration in
open Purelib.Integration.Path in
/-- Allocate the positive common family allowance below the original ceiling and certify its exact paid loss. -/
@[expose] def build (parentCount : Nat) (target ceiling : IncrementArea.Coordinate) (positive : 0 < target)
  (ceilingPositive : 0 < ceiling) :
    Budget.Trace.Family.BasisFamilyAllowance parentCount target := by
  have weightNonnegative : (0 : IncrementArea.Coordinate) ≤ 4 * (parentCount : IncrementArea.Coordinate) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))
  let allowance := min ceiling (Budget.Weighted.allowance target (4 * (parentCount : IncrementArea.Coordinate)))
  exact ⟨ceiling, allowance, rfl, Fraction.Order.Basic.lt_min ceilingPositive (Budget.Weighted.allowance_positive
    positive weightNonnegative),
    (4 * (parentCount : IncrementArea.Coordinate)) * allowance, rfl,
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.min_le_right _ _)
      weightNonnegative).trans
      (Budget.Weighted.mul_allowance_le positive.le weightNonnegative)⟩

open Purelib.Integration in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- The retained common family allowance is bounded by its original ceiling. -/
theorem allowance_le_ceiling {parentCount : Nat} {target : IncrementArea.Coordinate} (allocation :
  Budget.Trace.Family.BasisFamilyAllowance parentCount target) :
    allocation.allowance ≤ allocation.ceiling := by
  rw [allocation.allowance_eq]
  exact Fraction.Order.Basic.min_le_left _ _

end BasisFamilyAllowance
end Purelib.Integration.Budget.Trace.Family
