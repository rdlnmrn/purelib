module
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map

import Purelib.Integration.Path.IncrementArea
public import Purelib.Riemann.Paths.SegmentGapArea
import Purelib.Tactic.Ring

open Purelib

public section

/-! A closed polygon obtained by filling the retained endpoint gaps bounds
the sum of the original segment increments. The finite count is the number
of original segments, independent of later child subdivisions. -/

namespace Purelib.Riemann.Periods.SegmentGapPeriods

open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (Gaussian Coordinate)
open Purelib.Riemann.Paths.SegmentGapArea

open Purelib.Integration
open Purelib.Data
/-- Summing paired Gaussian differences equals the difference of the two component sums. -/
private theorem sum_errors (values : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map (fun value => value.1 - value.2)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map Prod.fst) - Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (values.map Prod.snd) := by
  induction values with
  | nil => change (0 : Path.IncrementArea.Gaussian) = 0 - 0; ring1
  | cons head tail ih => simp only [List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, ih]; ring1

/-- Closing-gap bounds control the sum of all original segment increments.

Every retained endpoint gap has quadrance at most the supplied error. The total is bounded by original segment count
squared times that error, including an empty polygon. -/
theorem closed_total_bound (segments : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian)) {error :
  Path.IncrementArea.Coordinate}
    (gaps : GapsSmall segments (first segments 0) error) :
    normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (segments.map (fun segment => segment.2 - segment.1))) ≤
      (segments.length : Path.IncrementArea.Coordinate) * ((segments.length : Path.IncrementArea.Coordinate) * error) :=
        by
  have bound := Gaussian.Norm.Sum.Bounds.normSq_sum_le
    ((pairs segments (first segments 0)).map (fun pair => pair.1 - pair.2)) error (by
      intro value member
      obtain ⟨pair, member, equal⟩ := List.Map.mem_map.mp member
      exact equal ▸ pairs_errors gaps pair member)
  have same : first segments (first segments 0) = first segments 0 := by cases segments <;> rfl
  have equal := sum_errors (pairs segments (first segments 0))
  rw [pairs_left, pairs_right_sum, same, Gaussian.Basic.sub_self, Gaussian.Basic.sub_zero] at equal
  have count : ((pairs segments (first segments 0)).map (fun pair => pair.1 - pair.2)).length = segments.length :=
    (Data.List.Map.length_map ..).trans (pairs_length segments (first segments 0))
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
  exact (congrArg Data.Gaussian.Norm.Basic.normSq equal).symm.trans_le
    (bound.trans_eq (congrArg (fun size : Nat => (size : Path.IncrementArea.Coordinate) * ((size :
      Path.IncrementArea.Coordinate) * error)) count))

end Purelib.Riemann.Periods.SegmentGapPeriods
