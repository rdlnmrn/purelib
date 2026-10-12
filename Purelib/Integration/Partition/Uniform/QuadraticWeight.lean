module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Integration.Partition.Interval
public import Purelib.Integration.Partition.QuadraticWeight
import Purelib.Integration.Partition.Unit.Basic
import Purelib.Integration.Partition.Unit.Normalize

import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.NatCast
import Purelib.CCL.Progressive.IntegrationPrograms
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Partition.Uniform.Grid
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Exact allowance amplification of every finite uniform partition

This theorem concerns the existing `uniformCuts` constructor and its actual
normalization and interval generation, not a hypothesis that the supplied
intervals happen to have equal widths.  Arbitrary positive cell counts are
covered; all arithmetic is on the finite rational grid.
-/

namespace Purelib.Integration.Partition.Uniform.QuadraticWeight

open Purelib.Algebra

open Purelib.Data.Rat in
open Purelib.Integration.Partition in
/-- A consecutive grid chain has squared-width sum equal to count times reciprocal denominator squared.

Every retained interval has the same scalar step. Structural recursion sums
those squared steps in their original order for any starting index and count. -/
theorem grid_weightSum (denominator : Nat) : ∀ start count,
    QuadraticWeight.weightSum (Interval.intervalsBetween (Uniform.Grid.point denominator start) (Uniform.Grid.point
      denominator (start + count + 1))
      (Uniform.Grid.nodes denominator start count)) =
        ((count + 1 : Nat) : Fraction.Rational) * (1 / (denominator : Fraction.Rational)) ^ 2
  | start, 0 => by
      change (Uniform.Grid.point denominator (start + 1) - Uniform.Grid.point denominator start) ^ 2 + 0 =
        (1 : Fraction.Rational) * (1 / (denominator : Fraction.Rational)) ^ 2
      rw [Uniform.Grid.point_step]
      ring1
  | start, count + 1 => by
      change (Uniform.Grid.point denominator (start + 1) - Uniform.Grid.point denominator start) ^ 2 +
        QuadraticWeight.weightSum (Interval.intervalsBetween (Uniform.Grid.point denominator (start + 1))
          (Uniform.Grid.point denominator (start + (count + 1) + 1)) (Uniform.Grid.nodes denominator (start + 1) count))
            = _
      rw [show start + (count + 1) + 1 = start + 1 + count + 1 from by omega,
        grid_weightSum denominator (start + 1) count, Uniform.Grid.point_step]
      simp only [NatCast.add, Nat.cast_one]
      ring1

open Purelib in
open Purelib.Data.Rat in
open Purelib.Integration.Partition in
/-- The exact normalized uniform unit partition has quadratic amplification equal to one. -/
theorem uniform_amplification (extra : Nat) :
    QuadraticWeight.amplification (Unit.Normalized.ofRequest (CCL.Progressive.IntegrationPrograms.uniformCuts
      extra)) = 1 := by
  have intervals : (Unit.Normalized.ofRequest (CCL.Progressive.IntegrationPrograms.uniformCuts extra)).intervals =
      Interval.intervalsBetween (Uniform.Grid.point (extra + 1) 0) (Uniform.Grid.point (extra + 1) (0 + extra + 1))
        (Uniform.Grid.nodes (extra + 1) 0 extra) := by
    change Interval.intervalsBetween 0 1 (Unit.Normalize.normalize (CCL.Progressive.IntegrationPrograms.uniformCuts
      extra)) = _
    rw [Uniform.Grid.uniform_normalized, Uniform.Grid.uniformCuts_eq_nodes, Uniform.Grid.point_zero, Nat.zero_add,
      Uniform.Grid.point_self (Nat.succ_pos extra)]
  unfold QuadraticWeight.amplification
  rw [intervals, Interval.intervalsBetween_length, Uniform.Grid.nodes_length, grid_weightSum]
  have nonzero : ((extra + 1 : Nat) : Fraction.Rational) ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct (Nat.succ_pos extra)).ne'
  calc
    ((extra + 1 : Nat) : Fraction.Rational) *
        (((extra + 1 : Nat) : Fraction.Rational) * (1 / ((extra + 1 : Nat) : Fraction.Rational)) ^ 2) =
      (((extra + 1 : Nat) : Fraction.Rational) * (((extra + 1 : Nat) : Fraction.Rational)⁻¹)) ^ 2 := by
        rw [Field.ExplicitField.div_eq_mul_inv]
        ring1
    _ = 1 := by rw [Field.ExplicitField.mul_inv_cancel _ nonzero, one_pow]
end Purelib.Integration.Partition.Uniform.QuadraticWeight
