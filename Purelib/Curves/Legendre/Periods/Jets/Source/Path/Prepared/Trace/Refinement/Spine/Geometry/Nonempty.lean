module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Chain
public import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks

/-! # Nonempty actual refined child words from original nonempty root-closed walks

The original walk edge count and complete-segment requests bound the SAME
retained child count. The original primitive cover supplies strict request
parameters. No request, geometry or root preparation is executed by these
propositions, and physically stationary child occurrences still count.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count : Nat} {sheet : Fin 2} {ambient : Purelib.Geometry.Rational.Box}

/-- A genuine original nonempty root-closed grid walk has a nonempty SAME retained global refined child list.

Original complete segments contain at least one request per grid edge.
Every original request is strict by its SAME primitive cover and therefore
contributes a positive actual child count. No nonzero coordinate movement,
root-owner comparison or numerical sample is assumed to prove nonemptiness.
-/
theorem parents_nonempty_of_walk
    {grid : ClearGrid (Paths.polynomial parameter) ambient} {base : Canonical}
    (owner : Owner ((Paths.polynomial parameter).eval base)) (closed : RootClosedWalk grid base owner)
    {inputCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) closed.traced.lineage}
    {materialized : OwnerPath (Paths.polynomial parameter) base owner base
      (PreparedPathGluing.finishOwner closed.traced.prepared)}
    {factory : materialized = closed.traced.lineage.ownerPath} {diameter : Rational} {positive : 0 < diameter}
    (retained : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (walkPositive : 0 < closed.walk.edgeCount) : retained.parents ≠ [] := by
  have segmentsPositive : 0 < closed.walk.path.segmentCount :=
    Eq.mpr (congrArg (fun size : Nat => 0 < size) closed.walk.path_segmentCount) walkPositive
  have oldPositive : 0 < closed.traced.prepared.stepCount :=
    Nat.lt_of_lt_of_le segmentsPositive
      (PeriodNonempty.PreparedClearPathModels.PreparedPath.segmentCount_le_stepCount closed.traced.prepared)
  have childPositive : 0 < retained.childCount :=
    Nat.lt_of_lt_of_le oldPositive (retained.stepCount_le_childCount closed.proper)
  have lengthPositive : 0 < retained.parents.length :=
    Eq.mpr (congrArg (fun size : Nat => 0 < size) retained.parents_length) childPositive
  intro empty
  exact Nat.ne_of_gt lengthPositive (congrArg List.length empty)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry

end
