module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Rounding.Floor
import Purelib.Data.Rat.Rounding.Floor.Bounds
import Purelib.Data.List.Membership
public import Purelib.Integration.Partition.Length
import Purelib.Integration.Partition.Unit.Normalize

import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.NatCast
public import Purelib.CCL.Progressive.IntegrationPrograms
import Purelib.Data.List.Range.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Exponential.Geometry.Policy
import Purelib.Integration.Partition.QuadraticWeight
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
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

namespace Purelib.Integration.Partition.Uniform.Grid

open Purelib.CCL.Progressive

open Purelib.Data.Rat in
/-- The exact rational grid point given by index divided by denominator. -/
@[expose] def point (denominator index : Nat) : Fraction.Rational :=
  (index : Fraction.Rational) / (denominator : Fraction.Rational)

open Purelib.Data.Rat in
open Purelib.Integration.Partition in
/-- Enumerate consecutive rational grid points after the supplied starting index. -/
@[expose] def nodes (denominator : Nat) : Nat → Nat → List Fraction.Rational
  | _, 0 => []
  | start, count + 1 => point denominator (start + 1) :: nodes denominator (start + 1) count

open Purelib.Integration.Partition in
/-- The retained grid node list has exactly the requested count. -/
theorem nodes_length (denominator : Nat) : ∀ start count,
    (nodes denominator start count).length = count
  | _, 0 => rfl
  | start, count + 1 => by
      change (nodes denominator (start + 1) count).length + 1 = count + 1
      rw [nodes_length]

open Purelib.Data.List in
open Purelib.Integration.Partition in
/-- Consecutive grid nodes equal the natural range mapped with the retained index offset.

Structural recursion retains the original count and starting index. Scalar
index transport relates each same occurrence without comparing functions. -/
theorem nodes_eq_map (denominator : Nat) : ∀ start count,
    nodes denominator start count =
      (List.range count).map (fun index => point denominator (start + index + 1))
  | _, 0 => rfl
  | start, count + 1 => by
      rw [nodes, Range.Basic.range_succ_eq_map, List.map_cons, Map.map_map,
        nodes_eq_map denominator (start + 1) count]
      apply congrArg (List.cons (point denominator (start + 1)))
      apply Map.map_congr_left
      intro index _
      change point denominator (start + 1 + index + 1) = point denominator (start + (index + 1) + 1)
      rw [show start + 1 + index + 1 = start + (index + 1) + 1 from by omega]

open Purelib in
open Purelib.Data.List in
open Purelib.Integration.Partition in
/-- The original uniform cut request is the consecutive interior node list with denominator one more than its length. -/
theorem uniformCuts_eq_nodes (extra : Nat) :
    IntegrationPrograms.uniformCuts extra = nodes (extra + 1) 0 extra := by
  rw [nodes_eq_map]
  unfold IntegrationPrograms.uniformCuts
  apply Map.map_congr_left
  intro index _
  unfold point
  rw [Nat.zero_add]

section
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Integration.Partition
/-- A positive denominator preserves strict order between natural grid indices. -/
theorem point_lt {denominator left right : Nat} (positive : 0 < denominator) (order : left < right) :
    point denominator left < point denominator right := by
  change (left : Fraction.Rational) * (denominator : Fraction.Rational)⁻¹ <
    (right : Fraction.Rational) * (denominator : Fraction.Rational)⁻¹
  exact Arithmetic.mul_lt_mul_of_pos_right_direct
    (Fraction.Cast.Order.natCast_lt_direct order)
    (Fraction.Order.Field.inv_pos_direct (Fraction.Cast.Order.natCast_pos_direct positive))

/-- The zero-index grid point is zero for every denominator. -/
theorem point_zero (denominator : Nat) : point denominator 0 = 0 :=
  Fraction.Field.zero_div_direct _

end

open Purelib.Algebra in
open Purelib.Data.Rat in
open Purelib.Integration.Partition in
/-- A positive denominator's own grid index gives the unit endpoint. -/
theorem point_self {denominator : Nat} (positive : 0 < denominator) : point denominator denominator = 1 := by
  change (denominator : Fraction.Rational) * (denominator : Fraction.Rational)⁻¹ = 1
  exact Field.ExplicitField.mul_inv_cancel _ (Fraction.Cast.Order.natCast_pos_direct positive).ne'

section
open Purelib.Data.List
open Purelib.Integration.Partition
/-- Grid nodes are strictly increasing when their denominator is positive. -/
theorem nodes_sorted {denominator : Nat} (positive : 0 < denominator) : ∀ start count,
    (nodes denominator start count).Pairwise (· < ·)
  | _, 0 => List.Pairwise.nil
  | start, count + 1 => by
      apply List.pairwise_cons.mpr
      refine ⟨?_, nodes_sorted positive (start + 1) count⟩
      intro value member
      rw [nodes_eq_map] at member
      obtain ⟨index, _, rfl⟩ := Map.mem_map.mp member
      exact point_lt positive (by omega)

/-- Every retained uniform interior node lies strictly between zero and one. -/
theorem uniform_nodes_inside (extra : Nat) :
    ∀ value ∈ nodes (extra + 1) 0 extra, 0 < value ∧ value < 1 := by
  intro value member
  rw [nodes_eq_map] at member
  obtain ⟨index, inRange, rfl⟩ := Map.mem_map.mp member
  have indexBound := Range.Basic.mem_range.mp inRange
  constructor
  · rw [← point_zero (extra + 1)]
    exact point_lt (Nat.succ_pos extra) (by omega)
  · rw [← point_self (Nat.succ_pos extra)]
    exact point_lt (Nat.succ_pos extra) (by omega)

end

open Purelib in
open Purelib.Integration.Partition in
/-- Normalizing the original uniform cut request leaves it unchanged. -/
theorem uniform_normalized (extra : Nat) :
    Unit.Normalize.normalize (IntegrationPrograms.uniformCuts extra) =
      IntegrationPrograms.uniformCuts extra := by
  rw [uniformCuts_eq_nodes]
  exact Unit.Normalize.normalize_eq_of_sorted (nodes_sorted (Nat.succ_pos extra) 0 extra) (uniform_nodes_inside extra)

open Purelib.Algebra in
open Purelib.Data.Rat in
open Purelib.Integration.Partition in
/-- Consecutive grid points differ by the reciprocal of their retained denominator.

The scalar successor cast separates the next index into its predecessor and
one. Total division preserves the identity even for denominator zero. -/
theorem point_step (denominator start : Nat) :
    point denominator (start + 1) - point denominator start = 1 / (denominator : Fraction.Rational) := by
  unfold point
  rw [NatCast.add, Nat.cast_one]
  simp only [Field.ExplicitField.div_eq_mul_inv]
  ring1

section
open Purelib
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Integration.Partition

/-- Every interval in a consecutive rational grid has the original reciprocal step as its exact length.

The finite node list and both endpoint indices are retained. The identity also
holds for denominator zero, where rational division is total. -/
theorem intervals_length (denominator : Nat) : ∀ (start count : Nat) (interval : Interval),
    interval ∈ Interval.intervalsBetween (point denominator start) (point denominator (start + count + 1))
      (nodes denominator start count) →
      interval.signedLength = 1 / (denominator : Fraction.Rational)
  | start, 0, interval, member => by
      change interval ∈ [⟨point denominator start, point denominator (start + 1)⟩] at member
      have equal := Membership.mem_singleton.mp member
      cases equal
      exact point_step denominator start
  | start, count + 1, interval, member => by
      change interval ∈ ⟨point denominator start, point denominator (start + 1)⟩ ::
        Interval.intervalsBetween (point denominator (start + 1)) (point denominator (start + (count + 1) + 1))
          (nodes denominator (start + 1) count) at member
      rcases Membership.mem_cons.mp member with equal | remaining
      · cases equal
        exact point_step denominator start
      · rw [show start + (count + 1) + 1 = (start + 1) + count + 1 from by omega0] at remaining
        exact intervals_length denominator (start + 1) count interval remaining

/-- The normalized original uniform request retains its exact consecutive grid intervals. -/
theorem uniform_intervals (extra : Nat) :
    (Unit.Normalized.ofRequest (IntegrationPrograms.uniformCuts extra)).intervals =
      Interval.intervalsBetween (point (extra + 1) 0) (point (extra + 1) (0 + extra + 1))
        (nodes (extra + 1) 0 extra) := by
  change Interval.intervalsBetween 0 1 (Unit.Normalize.normalize (IntegrationPrograms.uniformCuts
    extra)) = _
  rw [uniform_normalized, uniformCuts_eq_nodes, point_zero, Nat.zero_add, point_self (Nat.succ_pos extra)]

/-- Every retained interval in the original normalized uniform request has the same exact length. -/
theorem uniform_interval_length (extra : Nat) (interval : Interval)
    (member : interval ∈ (Unit.Normalized.ofRequest
      (IntegrationPrograms.uniformCuts extra)).intervals) :
    interval.signedLength = 1 / ((extra + 1 : Nat) : Fraction.Rational) := by
  rw [uniform_intervals] at member
  exact intervals_length (extra + 1) 0 extra interval member

/-- Compute a normalized uniform partition from the reciprocal ceiling of the requested width. -/
@[expose] def forWidth (width : Fraction.Rational) : Unit.Normalized :=
  Unit.Normalized.ofRequest (IntegrationPrograms.uniformCuts (Rounding.Floor.ceilNat (1 / width)))

/-- Every interval of the computed uniform partition is narrower than the supplied positive width. -/
theorem forWidth_interval_lt {width : Fraction.Rational} (positive : 0 < width) (interval : Interval)
    (member : interval ∈ (forWidth width).intervals) : interval.signedLength < width := by
  change interval ∈ (Unit.Normalized.ofRequest
    (IntegrationPrograms.uniformCuts (Rounding.Floor.ceilNat (1 / width)))).intervals at member
  rw [uniform_interval_length _ interval member]
  exact Rounding.Floor.Bounds.reciprocal_ceilNat_lt width positive

end

end Purelib.Integration.Partition.Uniform.Grid
