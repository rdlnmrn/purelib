module
public import Purelib.Integration.Partition.Length
import Purelib.Data.List.Rat.Linear
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-!
# Initial exceptional regions of unit partitions

Closed cells meeting an initial interval are charged only once. Their total
length is bounded by the interval's endpoint plus one mesh width, including
the cell that meets the endpoint.
-/

public section

namespace Purelib.Integration.Partition.Unit.Normalized

open Purelib.Data.Rat
open Purelib.Data.List.Rat.Linear
open Purelib.Integration.Partition

/-- Sum the lengths of the actual closed cells that meet the initial interval. -/
@[expose] def initialLength (partition : Normalized) (endpoint : Fraction.Rational) : Fraction.Rational :=
  (partition.intervals.map (fun interval =>
    if interval.start ≤ endpoint then interval.signedLength else 0)).sum

/-- Cells meeting an initial region cost at most its endpoint plus one mesh width.

Every marked cell is contained in the initial region expanded by the positive
mesh bound and clipped to the unit interval. Exact clamped lengths telescope
over the original partition, including a cell touching the endpoint. -/
theorem initialLength_le (partition : Normalized) (endpoint radius : Fraction.Rational)
    (endpointNonnegative : 0 ≤ endpoint) (radiusPositive : 0 < radius)
    (small : ∀ interval ∈ partition.intervals, interval.signedLength < radius) :
    partition.initialLength endpoint ≤ endpoint + radius := by
  let cover : Interval := ⟨0, min 1 (endpoint + radius)⟩
  have totalNonnegative : 0 ≤ endpoint + radius := by
    have added := Fraction.Order.Arithmetic.add_le_add_direct endpointNonnegative radiusPositive.le
    change (0 : Fraction.Rational) ≤ endpoint + radius at added
    exact added
  have coverNonnegative : 0 ≤ cover.finish :=
    Fraction.Order.Basic.le_min (by decide) totalNonnegative
  have coverLower : 0 ≤ cover.start := by
    change (0 : Fraction.Rational) ≤ 0
    decide
  have coverUpper : cover.finish ≤ 1 := Fraction.Order.Basic.min_le_left _ _
  have each : ∀ interval ∈ partition.intervals,
      (if interval.start ≤ endpoint then interval.signedLength else 0) ≤ cover.clampedLength interval := by
    intro interval member
    have valid := partition.valid interval member
    by_cases marked : interval.start ≤ endpoint
    · rw [if_pos marked]
      have shifted := Fraction.Order.Arithmetic.add_le_add_direct marked (small interval member).le
      have lengthIdentity : interval.start + interval.signedLength = interval.finish := by
        dsimp [Interval.signedLength]
        ring1
      rw [lengthIdentity] at shifted
      have inside : interval.finish ≤ cover.finish := Fraction.Order.Basic.le_min valid.2.2 shifted
      have equal := cover.clamp_child_length interval valid.1 valid.2.1.le inside
      change cover.clampedLength interval = interval.signedLength at equal
      rw [equal]
    · rw [if_neg marked]
      exact cover.clampedLength_nonnegative interval valid.2.1.le
  have bounded := sum_le (fun interval => if interval.start ≤ endpoint then interval.signedLength else 0)
    (fun interval => cover.clampedLength interval) partition.intervals each
  have total := partition.clampedLength_sum_of_bounds cover coverLower coverNonnegative coverUpper
  rw [total] at bounded
  have coverLength : cover.signedLength = min 1 (endpoint + radius) := by dsimp [cover, Interval.signedLength]; ring1
  rw [coverLength] at bounded
  exact bounded.trans (Fraction.Order.Basic.min_le_right _ _)

end Purelib.Integration.Partition.Unit.Normalized

end
