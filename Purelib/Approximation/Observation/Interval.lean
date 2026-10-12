module
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Interval.Basic

public import Purelib.Approximation.Observation.Basic
public import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Rational enclosures as finite observations

This module connects the rational-bound and neutral observation interfaces.
The symmetric rational separation is the maximum of the two directed
differences, so no absolute-value or completed metric structure is required.
-/

namespace Purelib.Data.Rat.Interval

open Purelib
open Purelib.Approximation
open Purelib.Data
open Purelib.Data.Rat

/-- A rational enclosure as an inhabited finite observation of its admitted rational candidates. -/
@[expose] def toObservation (bound : Rat.Interval) :
    Approximation.Observation Fraction.Rational Distance.rationalSeparation where
  Possible := bound.Contains
  witness := bound.sample
  witness_possible := bound.sample_contains
  spread := bound.width
  spread_nonnegative := bound.width_nonneg
  pairwise := by
    intro left right leftInside rightInside
    have directed := Interval.pairwise_difference_le leftInside rightInside
    exact Fraction.Order.Basic.max_le directed.1 directed.2

/-- Rational interval refinement induces refinement of the associated finite observations. -/
theorem Refines.toObservation {inner outer : Rat.Interval}
    (refines : Interval.Refines inner outer) :
    Observation.Refines inner.toObservation outer.toObservation :=
  ⟨fun possible => refines.contains possible⟩

end Purelib.Data.Rat.Interval

namespace Purelib.Approximation.Observation

open Purelib
open Purelib.Approximation
open Purelib.Data
open Purelib.Data.Rat

/-- Center a rational enclosure at the displayed witness of a rational observation and use its certified spread as the
radius.

The lower and upper endpoints subtract and add the same retained spread from the original witness. Its nonnegative
spread certifies the order of these endpoints. -/
@[expose] def rationalBound
    (observation : Approximation.Observation Fraction.Rational Distance.rationalSeparation) : Rat.Interval where
  lower := observation.witness - observation.spread
  upper := observation.witness + observation.spread
  valid := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    have scalar : (observation.witness + observation.spread) -
        (observation.witness - observation.spread) = observation.spread + observation.spread := by ring1
    rw [scalar]
    exact (Fraction.Field.zero_add (0 : Fraction.Rational)).symm.trans_le
      (Fraction.Order.Arithmetic.add_le_add_direct observation.spread_nonnegative observation.spread_nonnegative)

/-- Every admitted rational candidate lies in the witness-centred enclosure. The result uses only the displayed witness
and the finite pairwise-spread certificate.

The pairwise separation certificate bounds both directed differences from the retained witness. Translating those bounds
places the original admitted value between the displayed endpoints. -/
theorem rationalBound_contains
    (observation : Approximation.Observation Fraction.Rational Distance.rationalSeparation)
    {value : Fraction.Rational} (possible : observation.Possible value) :
    observation.rationalBound.Contains value := by
  have separation := observation.pairwise possible observation.witness_possible
  have directed :
      value - observation.witness ≤ observation.spread ∧
        observation.witness - value ≤ observation.spread :=
    ⟨(Fraction.Order.Basic.le_max_left _ _).trans separation,
      (Fraction.Order.Basic.le_max_right _ _).trans separation⟩
  constructor
  · apply (Fraction.Order.Arithmetic.sub_le_iff_le_add_direct).2
    calc
      observation.witness ≤ observation.spread + value :=
        (Fraction.Order.Arithmetic.sub_le_iff_le_add_direct).1 directed.2
      _ = value + observation.spread := by ring1
  · calc
      value ≤ observation.spread + observation.witness :=
        (Fraction.Order.Arithmetic.sub_le_iff_le_add_direct).1 directed.1
      _ = observation.witness + observation.spread := by ring1

/-- The witness-centred enclosure has exactly twice the displayed rational spread. -/
theorem rationalBound_width
    (observation : Approximation.Observation Fraction.Rational Distance.rationalSeparation) :
    observation.rationalBound.width = 2 * observation.spread := by
  dsimp only [Approximation.Observation.rationalBound, Interval.width]
  ring1

end Purelib.Approximation.Observation

end
