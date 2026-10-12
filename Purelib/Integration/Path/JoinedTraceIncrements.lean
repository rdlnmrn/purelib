module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.List.OfFn.Basic

import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Integration.Path.JoinedTrace
public import Purelib.Integration.Path.CenteredPathIncrements

public section

/-! Exact increment blocks of a joined trace, including one separate block
for every joining edge. Executable extraction reads cached increments only. -/
namespace Purelib.Integration.Path.JoinedTraceIncrements
open Purelib.Riemann.Periods
open Purelib.Integration.Path
open Purelib.Topology.Polygon

open Purelib.Data.List

open Purelib.Integration.Path.JoinedTrace (VertexTrace)

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

namespace VertexTrace
variable {Vertex : Type}

/-- List consecutive differences of the original primitive readings from the retained first vertex through its tail. -/
@[expose] def incrementsFrom (values : Vertex → Stokes.PrimitivePoint) (first : Vertex) : List Vertex → List
  Stokes.PrimitivePoint
  | [] => []
  | next :: rest => (Stokes.PrimitivePoint.sub (values next)) (values first) ::
    Purelib.Integration.Path.JoinedTraceIncrements.VertexTrace.incrementsFrom values next rest

/-- Read the exact consecutive primitive increments of the original retained vertex trace. -/
@[expose] def increments (trace : JoinedTrace.VertexTrace Vertex) (values : Vertex → Stokes.PrimitivePoint) : List
  PrimitivePoint :=
  JoinedTraceIncrements.VertexTrace.incrementsFrom values trace.first trace.rest

/-- The trace increment count equals its original tail length. -/
theorem increments_length (trace : JoinedTrace.VertexTrace Vertex) (values : Vertex → Stokes.PrimitivePoint) :
    (JoinedTraceIncrements.VertexTrace.increments trace values).length = trace.rest.length := by
  obtain ⟨first, rest⟩ := trace
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih => exact congrArg Nat.succ (ih next)

open Purelib.Data.List in
/-- Taking increments of the indexed trace agrees with its original ordered list increments. -/
theorem indexed_increments (trace : JoinedTrace.VertexTrace Vertex) (values : Vertex → Stokes.PrimitivePoint) :
    CenteredPathIncrements.increments (fun vertex => values (trace.indexed vertex)) =
      JoinedTraceIncrements.VertexTrace.increments trace values := by
  obtain ⟨first, rest⟩ := trace
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
    rw [CenteredPathIncrements.increments, OfFn.Basic.ofFn_succ]
    change (Stokes.PrimitivePoint.sub (values next)) (values first) ::
      CenteredPathIncrements.increments (fun vertex => values ((⟨next, rest⟩ : JoinedTrace.VertexTrace Vertex).indexed
        vertex)) = _
    exact congrArg (List.cons ((Stokes.PrimitivePoint.sub (values next)) (values first))) (ih next)

/-- Increments of concatenated tails split at the first tail's original terminal vertex. -/
private theorem incrementsFrom_append (values : Vertex → Stokes.PrimitivePoint) (first : Vertex) (left right : List
  Vertex) :
    JoinedTraceIncrements.VertexTrace.incrementsFrom values first (left ++ right) =
      JoinedTraceIncrements.VertexTrace.incrementsFrom values first left ++
        JoinedTraceIncrements.VertexTrace.incrementsFrom values (Dyadic.DyadicTrace.terminal first left) right := by
  induction left generalizing first with
  | nil => rfl
  | cons next rest ih => exact congrArg (List.cons ((Stokes.PrimitivePoint.sub (values next)) (values first))) (ih next)

/-- Joining traces concatenates their original increments with the explicit joining increment between them. -/
theorem join_increments (first last : JoinedTrace.VertexTrace Vertex) (values : Vertex → Stokes.PrimitivePoint) :
    JoinedTraceIncrements.VertexTrace.increments (first.join last) values = JoinedTraceIncrements.VertexTrace.increments
      first values ++
      (Stokes.PrimitivePoint.sub (values last.first)) (values first.last) ::
        JoinedTraceIncrements.VertexTrace.increments last values := by
  exact JoinedTraceIncrements.VertexTrace.incrementsFrom_append values first.first first.rest (last.first :: last.rest)

/-- Retain each original trace's increment list and each intervening joining increment as separate ordered blocks. -/
@[expose] def incrementBlocks (values : Vertex → Stokes.PrimitivePoint) (first : JoinedTrace.VertexTrace Vertex) :
    List (JoinedTrace.VertexTrace Vertex) → List (List Stokes.PrimitivePoint)
  | [] => [JoinedTraceIncrements.VertexTrace.increments first values]
  | next :: rest => JoinedTraceIncrements.VertexTrace.increments first values :: [(Stokes.PrimitivePoint.sub (values
    next.first)) (values first.last)] :: Purelib.Integration.Path.JoinedTraceIncrements.VertexTrace.incrementBlocks
    values next rest

/-- List the original trace edge counts interleaved with singleton joining-edge counts. -/
@[expose] def blockLengths (first : JoinedTrace.VertexTrace Vertex) : List (JoinedTrace.VertexTrace Vertex) → List Nat
  | [] => [first.rest.length]
  | next :: rest => first.rest.length :: 1 :: Purelib.Integration.Path.JoinedTraceIncrements.VertexTrace.blockLengths
    next rest

/-- The retained increment block lengths equal the original trace-and-junction count list. -/
theorem incrementBlocks_lengths (values : Vertex → Stokes.PrimitivePoint) (first : JoinedTrace.VertexTrace Vertex)
    (rest : List (JoinedTrace.VertexTrace Vertex)) :
    (JoinedTraceIncrements.VertexTrace.incrementBlocks values first rest).map List.length =
      JoinedTraceIncrements.VertexTrace.blockLengths first rest := by
  induction rest generalizing first with
  | nil => exact congrArg (fun length => [length]) (JoinedTraceIncrements.VertexTrace.increments_length first values)
  | cons next rest ih =>
    change (JoinedTraceIncrements.VertexTrace.increments first values).length :: 1 ::
      (JoinedTraceIncrements.VertexTrace.incrementBlocks values next rest).map List.length = _
    rw [JoinedTraceIncrements.VertexTrace.increments_length first, ih]
    rfl

/-- Flattening the retained component and junction blocks yields the exact glued trace increments.

The original ordered component blocks retain each singleton joining increment. Structural gluing identifies their
flattened list with the same joined-trace increment spine. -/
theorem incrementBlocks_flatten (values : Vertex → Stokes.PrimitivePoint) (first : JoinedTrace.VertexTrace Vertex)
    (rest : List (JoinedTrace.VertexTrace Vertex)) :
    (JoinedTraceIncrements.VertexTrace.incrementBlocks values first rest).flatten =
      JoinedTraceIncrements.VertexTrace.increments (first.glue rest) values := by
  induction rest generalizing first with
  | nil => exact Append.append_nil _
  | cons next rest ih =>
    change JoinedTraceIncrements.VertexTrace.increments first values ++ ((Stokes.PrimitivePoint.sub (values next.first))
      (values first.last) ::
      (JoinedTraceIncrements.VertexTrace.incrementBlocks values next rest).flatten) = _
    rw [ih, JoinedTrace.VertexTrace.glue, JoinedTraceIncrements.VertexTrace.join_increments,
      JoinedTrace.VertexTrace.glue_first]

/-- Split the supplied items by the ordered requested block sizes, using successive take and drop operations.

An empty size list stops the operation; insufficient items produce the corresponding truncated blocks. -/
def splitBlocks {Item : Type} : List Nat → List Item → List (List Item)
  | [], _ => []
  | size :: sizes, items => items.take size :: Purelib.Integration.Path.JoinedTraceIncrements.VertexTrace.splitBlocks
    sizes (items.drop size)

/-- Splitting the flattened original blocks at their exact lengths recovers those blocks. -/
private theorem splitBlocks_spec {Item : Type} (blocks : List (List Item)) :
    JoinedTraceIncrements.VertexTrace.splitBlocks (blocks.map List.length) blocks.flatten = blocks := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
    change (block ++ rest.flatten).take block.length ::
      JoinedTraceIncrements.VertexTrace.splitBlocks (rest.map List.length) ((block ++ rest.flatten).drop block.length) =
        _
    rw [List.take_left, List.drop_left, ih]

set_option genInjectivity false in
/-- Retained component and junction blocks indexed by the exact original traces and whole sample.

The blocks equal the canonical ordered trace decomposition and flatten to the supplied sample's exact cached increments.
-/
structure IncrementPartition (values : Vertex → Stokes.PrimitivePoint) (first : JoinedTrace.VertexTrace Vertex)
    (rest : List (JoinedTrace.VertexTrace Vertex)) {trace : JoinedTrace.VertexTrace Vertex}
    (sample : CenteredBilinearPath.Sample (fun vertex => values (trace.indexed vertex))) where
  /-- The retained original component and junction increment blocks. -/ blocks : List (List Stokes.PrimitivePoint)
  /-- The retained blocks equal the canonical decomposition of these exact traces. -/ blocks_eq : blocks =
    JoinedTraceIncrements.VertexTrace.incrementBlocks values first rest
  /-- Flattening the retained blocks gives the supplied whole sample's exact increments. -/ flatten_eq : blocks.flatten
    = CenteredPathIncrements.Sample.increments sample

constructive_injectivity IncrementPartition

/-- Partition the supplied whole sample's own increment list using the original trace and junction lengths.

The original trace equality certifies the resulting blocks without replacing the sample or recomputing its retained
centered values. -/
@[expose] def IncrementPartition.build (values : Vertex → Stokes.PrimitivePoint) (first : JoinedTrace.VertexTrace
  Vertex)
    (rest : List (JoinedTrace.VertexTrace Vertex)) {trace : JoinedTrace.VertexTrace Vertex}
    (sample : CenteredBilinearPath.Sample (fun vertex => values (trace.indexed vertex))) (traceEq : trace = first.glue
      rest) :
    JoinedTraceIncrements.VertexTrace.IncrementPartition values first rest sample :=
  let blocks := JoinedTraceIncrements.VertexTrace.splitBlocks (JoinedTraceIncrements.VertexTrace.blockLengths first
    rest) (CenteredPathIncrements.Sample.increments sample)
  have exactBlocks : blocks = JoinedTraceIncrements.VertexTrace.incrementBlocks values first rest := by
    dsimp only [blocks]
    rw [CenteredPathIncrements.Sample.increments_raw sample, JoinedTraceIncrements.VertexTrace.indexed_increments,
      traceEq, ← JoinedTraceIncrements.VertexTrace.incrementBlocks_flatten,
      ← JoinedTraceIncrements.VertexTrace.incrementBlocks_lengths values first rest]
    exact JoinedTraceIncrements.VertexTrace.splitBlocks_spec _
  { blocks := blocks
    blocks_eq := exactBlocks
    flatten_eq := by
      rw [exactBlocks, JoinedTraceIncrements.VertexTrace.incrementBlocks_flatten,
        CenteredPathIncrements.Sample.increments_raw sample, JoinedTraceIncrements.VertexTrace.indexed_increments,
        traceEq] }

end VertexTrace
end Purelib.Integration.Path.JoinedTraceIncrements

end
