module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Rational.Budget.Aggregate
public import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Algebra.NatCast
open Purelib.Algebra

@[expose] public section

/-!
# Cached uniform rational samples of the unit interval

Both count and step are executable data.  Their exact product is one, so
uniform boundary-ribbon estimates lose no accuracy as the sample count grows.
Generated partitions may supply the same finite equations directly.
-/

namespace Purelib.Integration.Path.Dyadic.UniformParameters

open Purelib.Integration.Path.BoundaryRibbon

set_option genInjectivity false in
open Purelib.Integration.Path in
/-- A retained uniform rational partition of the unit interval with a positive exact step.

The indexed parameter vector includes both endpoints, has the supplied step on every edge, and records that the step
times the original edge count is one. -/
structure UnitPartition (count : Nat) where
  /-- The retained common rational edge width. -/ step : BoundaryRibbon.Coordinate
  /-- The common edge width is positive. -/ positive : 0 < step
  /-- The cached rational parameters at the original vertex indices. -/ parameters : BoundaryRibbon.Vector
    BoundaryRibbon.Coordinate (count + 1)
  /-- Every retained parameter lies in the unit interval. -/ inside : ∀ vertex, 0 ≤ parameters vertex ∧ parameters
    vertex ≤ 1
  /-- The original first vertex parameter is zero. -/ first_eq : parameters 0 = 0
  /-- The original last vertex parameter is one. -/ last_eq : parameters (Fin.last count) = 1
  /-- Every original indexed edge has the retained common width. -/ increment_eq : ∀ edge : Fin count, parameters
    edge.succ - parameters edge.castSucc = step
  /-- The retained width times the exact edge count equals one. -/ span_eq : (count : BoundaryRibbon.Coordinate) * step
    = 1

constructive_injectivity UnitPartition

namespace UnitPartition

open Purelib.Approximation.Rational in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Construct the unit partition with one more edge than the supplied natural number.

The reciprocal edge count determines the exact step, and the cached parameter vector multiplies each retained vertex
index by that step. -/
def build (extra : Nat) : Dyadic.UniformParameters.UnitPartition (extra + 1) :=
  let count := Budget.Aggregate.countCoordinate (extra + 1)
  have countEq : count = ((extra + 1 : Nat) : BoundaryRibbon.Coordinate) := Budget.Aggregate.countCoordinate_eq _
  have countPositive : 0 < count := (Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ extra)).trans_eq
    countEq.symm
  let step := 1 / count
  have span : count * step = 1 := by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne 1 count countPositive.ne'
  let parameters := Vector.Basic.vectorOfFn fun vertex : Fin (extra + 1 + 1) =>
    Budget.Aggregate.countCoordinate vertex.val * step
  have readback (vertex : Fin (extra + 1 + 1)) : parameters vertex = (vertex.val : BoundaryRibbon.Coordinate) * step :=
    by
    dsimp only [parameters]
    rw [Vector.Basic.vectorOfFn_apply, Budget.Aggregate.countCoordinate_eq]
  have positive : 0 < step := Fraction.Order.Field.div_pos_direct (by decide) countPositive
  { step := step
    positive := positive
    parameters := parameters
    inside := fun vertex => by
      rw [readback]
      exact ⟨Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
        vertex.val)) positive.le,
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          ((Fraction.Cast.Order.natCast_le_direct (Nat.le_of_lt_succ vertex.isLt)).trans_eq countEq.symm)
            positive.le).trans_eq span⟩
    first_eq := by rw [readback]; exact Fraction.Field.zero_mul_direct step
    last_eq := by
      rw [readback]
      change ((extra + 1 : Nat) : BoundaryRibbon.Coordinate) * step = 1
      rw [← countEq]
      exact span
    increment_eq := fun edge => by
      rw [readback, readback]
      change (((edge.val + 1 : Nat) : BoundaryRibbon.Coordinate) * step - (edge.val : BoundaryRibbon.Coordinate) * step)
        = step
      rw [NatCast.add, Nat.cast_one]
      ring1
    span_eq := by rw [← countEq]; exact span }

end UnitPartition

end Purelib.Integration.Path.Dyadic.UniformParameters
