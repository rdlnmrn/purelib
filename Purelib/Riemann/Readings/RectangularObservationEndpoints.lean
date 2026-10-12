module
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting

import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Geometry.Grid.AxisWalks
public import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Geometry.Rectangle.Partition.PreparedAxisAdjacency
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Tactic.QuotientFreeOmega

@[expose] public section

/-! The retained first and last intervals meet the original face boundary. -/
namespace Purelib

section PreparedAxisPartitions
open Purelib.Polynomial.Geometry.Grid.AxisWalks (IncreasingWalk)
open _root_.Purelib.Geometry.Rectangle renaming AxisPartition -> Partition
open _root_.Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval Coordinate)

section
open Purelib.Geometry.Rectangle.Partition
open Purelib.Polynomial
namespace Riemann.Readings.RectangularObservationEndpoints.PreparedAxisPartitions

/-- The first edge of a nonempty increasing interval walk starts at its original lower endpoint. -/
private theorem walk_first {intervals : List PreparedAxisPartitions.Interval} {first last :
  PreparedAxisPartitions.Coordinate}
    (walk : Geometry.Grid.AxisWalks.IncreasingWalk intervals first last) (positive : 0 < walk.edges.length) :
    walk.edges[0].lower = first := by
  cases walk with
  | nil => exact (Nat.not_lt_zero _ positive).elim
  | cons => rfl

/-- An empty increasing interval walk has equal original endpoints. -/
private theorem walk_empty {intervals : List PreparedAxisPartitions.Interval} {first last :
  PreparedAxisPartitions.Coordinate}
    (walk : Geometry.Grid.AxisWalks.IncreasingWalk intervals first last) (empty : walk.edges.length = 0) : first = last
      := by
  cases walk with
  | nil => rfl
  | cons => simp only [Geometry.Grid.AxisWalks.IncreasingWalk.edges, List.length_cons] at empty; omega

/-- The final edge of an increasing interval walk finishes at its original upper endpoint. -/
private theorem walk_last {intervals : List PreparedAxisPartitions.Interval} :
    ∀ {first last : PreparedAxisPartitions.Coordinate} (walk : Geometry.Grid.AxisWalks.IncreasingWalk intervals first
      last)
      (index : Nat) (bound : index < walk.edges.length) (_finalIndex : index + 1 = walk.edges.length),
      walk.edges[index].upper = last
  | _, _, .nil _, _, bound, _ => (Nat.not_lt_zero _ bound).elim
  | _, _, .cons _ _ tail, 0, _, finalIndex => by
      exact walk_empty tail (Nat.succ.inj finalIndex).symm
  | _, _, .cons _ _ tail, index + 1, bound, finalIndex =>
      walk_last tail index (Nat.lt_of_succ_lt_succ bound) (Nat.succ.inj finalIndex)

end Riemann.Readings.RectangularObservationEndpoints.PreparedAxisPartitions

end

open Purelib.Geometry.Rectangle.Partition
namespace Geometry.Rectangle.AxisPartition

/-- The first interval in the original nonempty axis partition begins at its lower endpoint. -/
theorem first_lower {first last :
  PreparedAxisPartitions.Coordinate} {cuts : List PreparedAxisPartitions.Coordinate}
    (partition : AxisPartition first last cuts) (positive : 0 < partition.intervals.length) :
    partition.intervals[0].lower = first := by
  have equal := Riemann.Readings.RectangularObservationEndpoints.PreparedAxisPartitions.walk_first partition.walk (by
      rw [partition.walk_edges]; exact positive)
  simpa only [partition.walk_edges] using equal

/-- The interval at the original axis partition's final bounded index ends at its upper endpoint. -/
theorem last_upper {first last :
  PreparedAxisPartitions.Coordinate} {cuts : List PreparedAxisPartitions.Coordinate}
    (partition : AxisPartition first last cuts) (index : Fin partition.intervals.length)
    (finalIndex : index.val + 1 = partition.intervals.length) :
    partition.intervals[index].upper = last := by
  have equal := Riemann.Readings.RectangularObservationEndpoints.PreparedAxisPartitions.walk_last partition.walk
      index.val
    (by rw [partition.walk_edges]; exact index.isLt) (by rw [partition.walk_edges]; exact finalIndex)
  simpa only [partition.walk_edges, Fin.getElem_fin] using equal

end Geometry.Rectangle.AxisPartition

end PreparedAxisPartitions

namespace Riemann.Meshes.RectangularObservationMesh.ObservationMesh
open Purelib.Riemann.Normalization.InverseRootPolynomial (Box)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
variable {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry} {box :
  Purelib.Geometry.Rational.Box}

/-- The original observation mesh's first horizontal interval begins at the box's lower coordinate. -/
theorem x_first (mesh : ObservationMesh cuts
  box) :
    mesh.partition.x.intervals[Fin.cast mesh.boundaryColumns_eq 0].lower = box.xLower :=
  mesh.partition.x.first_lower (Fin.cast mesh.boundaryColumns_eq 0).isLt

/-- The original observation mesh's last horizontal interval ends at the box's upper coordinate. -/
theorem x_last (mesh : ObservationMesh cuts
  box) :
    mesh.partition.x.intervals[Fin.cast mesh.boundaryColumns_eq (Fin.last mesh.boundaryColumns)].upper = box.xUpper :=
  mesh.partition.x.last_upper _ mesh.boundaryColumns_eq

/-- The original observation mesh's first vertical interval begins at the box's lower coordinate. -/
theorem y_first (mesh : ObservationMesh cuts
  box) :
    mesh.partition.y.intervals[Fin.cast mesh.boundaryRows_eq 0].lower = box.yLower :=
  mesh.partition.y.first_lower (Fin.cast mesh.boundaryRows_eq 0).isLt

/-- The original observation mesh's last vertical interval ends at the box's upper coordinate. -/
theorem y_last (mesh : ObservationMesh cuts
  box) :
    mesh.partition.y.intervals[Fin.cast mesh.boundaryRows_eq (Fin.last mesh.boundaryRows)].upper = box.yUpper :=
  mesh.partition.y.last_upper _ mesh.boundaryRows_eq

end Riemann.Meshes.RectangularObservationMesh.ObservationMesh
end Purelib
