module

import Purelib.Polynomial.Geometry.Grid.AxisWalks
public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Geometry.Grid.ClearGrid
meta import Mathlib.Tactic.Linter.Lint
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Geometry.Rectangle.Partition

open Purelib.Polynomial.Geometry.Grid

@[expose] public section

/-! Consecutive retained partition intervals share their exact endpoint. -/
namespace Purelib.Geometry.Rectangle

open _root_.Purelib.Geometry.Rectangle renaming AxisPartition -> Partition
open _root_.Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval Coordinate)
open Purelib.Polynomial.Geometry.Grid.AxisWalks (IncreasingWalk)

namespace Partition.PreparedAxisAdjacency

/-- A nonempty increasing walk starts at its first interval's lower endpoint. -/
private theorem first_lower {intervals : List PreparedAxisPartitions.Interval} {first last :
  PreparedAxisPartitions.Coordinate}
    (walk : AxisWalks.IncreasingWalk intervals first last) (positive : 0 < walk.edges.length) :
    walk.edges[0].lower = first := by
  cases walk with
  | nil => exact (Nat.not_lt_zero _ positive).elim
  | cons => rfl

/-- Consecutive intervals traversed by an increasing walk share their endpoint. -/
private theorem walk_consecutive {intervals : List PreparedAxisPartitions.Interval} :
    ∀ {first last : PreparedAxisPartitions.Coordinate} (walk : AxisWalks.IncreasingWalk intervals first last)
      (index : Nat) (bound : index + 1 < walk.edges.length),
      walk.edges[index].upper = walk.edges[index + 1].lower
  | _, _, .nil _, _, bound => (Nat.not_lt_zero _ bound).elim
  | _, _, .cons _ _ tail, 0, bound =>
      (first_lower tail (Nat.lt_of_succ_lt_succ bound)).symm
  | _, _, .cons _ _ tail, index + 1, bound =>
      walk_consecutive tail index (Nat.lt_of_succ_lt_succ
        bound)

end Partition.PreparedAxisAdjacency

namespace AxisPartition.Adjacency

/-- Consecutive cached partition intervals share their exact coordinate endpoint. -/
theorem consecutive {first last : PreparedAxisPartitions.Coordinate} {cuts : List
  PreparedAxisPartitions.Coordinate}
    (partition : AxisPartition first last cuts) (index : Nat) (bound : index + 1 <
      partition.intervals.length) :
    partition.intervals[index].upper = partition.intervals[index + 1].lower := by
  have equal := Geometry.Rectangle.Partition.PreparedAxisAdjacency.walk_consecutive partition.walk index (by
      rw [partition.walk_edges];
      exact bound)
  simpa only [partition.walk_edges] using equal

end AxisPartition.Adjacency

end Purelib.Geometry.Rectangle
