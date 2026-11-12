module

public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
public import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Data.List.Map

/-! # Requested walks on the retained cut-partition axis

Both endpoints come from the same cached coordinate bank. The original
axis-walk constructor chooses orientation; the original interval-cache
identity transports its steps to the actual retained adjacent intervals.
-/

public section

namespace Purelib.Geometry.Rectangle.AxisPartition

open Purelib.Data.List
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Coordinate)
open Purelib.Polynomial.Geometry.Grid

variable {lower upper : Coordinate} {cuts : List Coordinate}

/-- Construct an oriented walk between two original cached coordinates on the same retained interval bank. -/
def between (partition : AxisPartition lower upper cuts) (start finish : Coordinate)
    (first : start ∈ partition.coordinates) (last : finish ∈ partition.coordinates) :
    AxisWalks.Walk partition.intervals start finish :=
  let original := AxisWalks.walk partition.coordinates partition.ordered start finish
    (Eq.mp (congrArg (fun values => start ∈ values) (Map.map_id partition.coordinates).symm) first)
    (Eq.mp (congrArg (fun values => finish ∈ values) (Map.map_id partition.coordinates).symm) last)
  Eq.mp (congrArg (fun intervals => AxisWalks.Walk intervals start finish) partition.intervals_eq.symm) original

/-- The original constructor and interval transport are the complete retained walk factory. -/
theorem between_eq (partition : AxisPartition lower upper cuts) (start finish : Coordinate)
    (first : start ∈ partition.coordinates) (last : finish ∈ partition.coordinates) :
    partition.between start finish first last =
      Eq.mp (congrArg (fun intervals => AxisWalks.Walk intervals start finish) partition.intervals_eq.symm)
        (AxisWalks.walk partition.coordinates partition.ordered start finish
          (Eq.mp (congrArg (fun values => start ∈ values) (Map.map_id partition.coordinates).symm) first)
          (Eq.mp (congrArg (fun values => finish ∈ values) (Map.map_id partition.coordinates).symm) last)) := by
  unfold between
  rfl

end Purelib.Geometry.Rectangle.AxisPartition

end
