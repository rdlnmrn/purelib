module
import Purelib.Data.List.OfFn.Basic

import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Integration.Path.JoinedTraceIncrements

@[expose] public section

/-! Assemble cached samples in the original joined-trace order. Junction
samples retain both owners, including when their physical points coincide. -/
namespace Purelib.Integration.Polynomial.Rectangle.JoinedSampleBlocks

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

open Purelib.Integration.Path.JoinedTraceIncrements.VertexTrace
  (incrementBlocks incrementBlocks_flatten IncrementPartition indexed_increments)
variable {Vertex : Type}

open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The two original endpoint readings forming the joining edge between the retained traces. -/
def JunctionValues (values : Vertex → Stokes.PrimitivePoint) (first last : JoinedTrace.VertexTrace Vertex)
    (vertex : Fin 2) : PrimitivePoint :=
  if vertex.val = 0 then values first.last else values last.first

open Purelib.Data.List in
open Purelib.Integration.Path in
open Purelib.Integration.Polynomial in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- The sampled junction's increments consist of the exact difference from the first trace's end to the next trace's
start. -/
theorem junction_increments (values : Vertex → Stokes.PrimitivePoint) (first last : JoinedTrace.VertexTrace Vertex)
    (sample : CenteredBilinearPath.Sample (Rectangle.JoinedSampleBlocks.JunctionValues values first last)) :
    CenteredPathIncrements.Sample.increments sample =
      [(Stokes.PrimitivePoint.sub (values last.first)) (values first.last)] := by
  rw [CenteredPathIncrements.Sample.increments_raw,
    CenteredPathIncrements.increments, OfFn.Basic.ofFn_succ]
  rfl

open Purelib.Integration.Path in
open Purelib.Integration.Polynomial in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- Read the retained piece and junction samples' own increment lists in their original alternating order.

The recursion retains one block for each piece and one singleton junction block between adjacent pieces. -/
def sampledBlocks (values : Vertex → Stokes.PrimitivePoint) : {count : Nat} →
    (traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex) →
    ((position : Fin (count + 1)) → CenteredBilinearPath.Sample (fun vertex => values ((traces position).indexed
      vertex))) →
    ((position : Fin count) → CenteredBilinearPath.Sample (Rectangle.JoinedSampleBlocks.JunctionValues values (traces
      position.castSucc) (traces position.succ))) →
    List (List Stokes.PrimitivePoint)
  | 0, _, pieces, _ => [CenteredPathIncrements.Sample.increments (pieces 0)]
  | _ + 1, traces, pieces, junctions =>
    CenteredPathIncrements.Sample.increments (pieces 0) ::
      CenteredPathIncrements.Sample.increments (junctions 0) ::
      Purelib.Integration.Polynomial.Rectangle.JoinedSampleBlocks.sampledBlocks values (fun position => traces
        position.succ) (fun position => pieces position.succ)
        (fun position => junctions position.succ)

open Purelib.Data.List in
open Purelib.Integration.Path in
open Purelib.Integration.Polynomial in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- The retained sample blocks equal the original trace family's canonical component-and-junction decomposition. -/
theorem sampledBlocks_eq (values : Vertex → Stokes.PrimitivePoint) {count : Nat}
    (traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex)
    (pieces : (position : Fin (count + 1)) → CenteredBilinearPath.Sample (fun vertex => values ((traces
      position).indexed vertex)))
    (junctions : (position : Fin count) → CenteredBilinearPath.Sample (Rectangle.JoinedSampleBlocks.JunctionValues
      values (traces position.castSucc) (traces position.succ))) :
    Rectangle.JoinedSampleBlocks.sampledBlocks values traces pieces junctions =
      JoinedTraceIncrements.VertexTrace.incrementBlocks values (traces 0) (List.ofFn (fun position : Fin count => traces
        position.succ)) := by
  induction count with
  | zero =>
    exact congrArg (fun block => [block]) ((CenteredPathIncrements.Sample.increments_raw (pieces 0)).trans
      (JoinedTraceIncrements.VertexTrace.indexed_increments (traces 0) values))
  | succ count ih =>
    rw [Rectangle.JoinedSampleBlocks.sampledBlocks, OfFn.Basic.ofFn_succ,
      JoinedTraceIncrements.VertexTrace.incrementBlocks]
    exact congrArg₂ List.cons ((CenteredPathIncrements.Sample.increments_raw (pieces 0)).trans
      (JoinedTraceIncrements.VertexTrace.indexed_increments (traces 0) values))
      (congrArg₂ List.cons (Rectangle.JoinedSampleBlocks.junction_increments values _ _ (junctions 0))
        (ih (fun position => traces position.succ) (fun position => pieces position.succ) (fun position => junctions
          position.succ)))

open Purelib.Integration.Path
open Purelib.Integration.Polynomial
open Purelib.Riemann.Periods
open Purelib.Topology.Polygon
/-- The retained piece and junction blocks flatten to the exact whole sample's increments when its trace is their
concatenation. -/
theorem sampledBlocks_flatten (values : Vertex → Stokes.PrimitivePoint) {count : Nat}
    (traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex)
    (pieces : (position : Fin (count + 1)) → CenteredBilinearPath.Sample (fun vertex => values ((traces
      position).indexed vertex)))
    (junctions : (position : Fin count) → CenteredBilinearPath.Sample (Rectangle.JoinedSampleBlocks.JunctionValues
      values (traces position.castSucc) (traces position.succ)))
    {whole : JoinedTrace.VertexTrace Vertex} (sample : CenteredBilinearPath.Sample (fun vertex => values (whole.indexed
      vertex)))
    (traceEq : whole = JoinedTrace.VertexTrace.concatenate traces) :
    (Rectangle.JoinedSampleBlocks.sampledBlocks values traces pieces junctions).flatten =
      CenteredPathIncrements.Sample.increments sample := by
  rw [Rectangle.JoinedSampleBlocks.sampledBlocks_eq, JoinedTraceIncrements.VertexTrace.incrementBlocks_flatten,
    CenteredPathIncrements.Sample.increments_raw, JoinedTraceIncrements.VertexTrace.indexed_increments, traceEq]
  rfl

/-- The sampled piece and junction block readback equals the original retained increment partition's blocks. -/
theorem sampledBlocks_partition (values : Vertex → Stokes.PrimitivePoint) {count : Nat}
    (traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex)
    (pieces : (position : Fin (count + 1)) → CenteredBilinearPath.Sample (fun vertex => values ((traces
      position).indexed vertex)))
    (junctions : (position : Fin count) → CenteredBilinearPath.Sample (Rectangle.JoinedSampleBlocks.JunctionValues
      values (traces position.castSucc) (traces position.succ)))
    {whole : JoinedTrace.VertexTrace Vertex} {sample : CenteredBilinearPath.Sample (fun vertex => values (whole.indexed
      vertex))}
    (partition : JoinedTraceIncrements.VertexTrace.IncrementPartition values (traces 0)
      (List.ofFn (fun position : Fin count => traces position.succ)) sample) :
    Rectangle.JoinedSampleBlocks.sampledBlocks values traces pieces junctions = partition.blocks :=
  (Rectangle.JoinedSampleBlocks.sampledBlocks_eq values traces pieces junctions).trans partition.blocks_eq.symm

end Purelib.Integration.Polynomial.Rectangle.JoinedSampleBlocks
