module

meta import Purelib.Elab.ConstructiveInjectivity

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Edges
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Calculus.Jet.Quadratic.Basic
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table

/-! # Retained positive-node programme and adjacent-integral tables

One original node vector and its alignment, programme and edge caches
form the table. Its readbacks retain the same original integral certificates.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

namespace PositiveGridNode

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Vector (DependentVector)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry
  (ValueBlocks BetweenRows Position)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat}
    (intervals : Nat) (positive : 0 < intervals) (direction : Canonical) (moving : direction ≠ 0)
    (spatial : AccuracyRequest)
    (source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving))))
    (member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt })
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    (admitted : Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    {root : Named} (roots : RootChain (parent :: parents) root root)
    (targetCurrent targetFloor targetRootStage : Nat)

variable {intervals positive direction moving spatial source member ranges allocation admitted widths roots
    targetCurrent targetFloor targetRootStage}

variable (intervals positive direction moving spatial source member ranges allocation admitted widths roots
    targetCurrent targetFloor targetRootStage)

set_option genInjectivity false in
/-- Original nodes, common alignments, node programmes and ordered actual positive-positive integral edges.

The raw field retains the complete original dependent tuple and every
once-executed node and edge factory. All four caches keep their original
parents and indices. Every adjacent edge reads the same node vector and
alignment product; for intervals=1 the original edge vector is empty.
-/
structure Table
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat}
    (intervals : Nat) (positive : 0 < intervals) (direction : Canonical) (moving : direction ≠ 0)
    (spatial : AccuracyRequest)
    (source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving))))
    (member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt })
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    (admitted : Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    {root : Named} (roots : RootChain (parent :: parents) root root)
    (targetCurrent targetFloor targetRootStage : Nat) : Type _ where
  /-- The same original node, alignment, programme and edge caches in their complete dependent tuple. -/
  raw :
    (nodes : Nodes intervals positive direction moving spatial source member
        ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage) ×
    (aligned : Nodes.Alignments nodes) ×
    (_programmes : Nodes.Programmes nodes) ×
    nodes.Edges aligned

constructive_injectivity Table

namespace Table

/-- Materialize the actual finite positive-node and adjacent-integral table on ONE retained original source.

The order is nodes, their common alignment products, their original
programme caches, then adjacent positions/rows/weighted sums. No target
Completion, node-zero edge or stationary geometry is constructed here.
-/
def build : Table intervals positive direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage :=
  let nodes : Nodes intervals positive direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage :=
    Nodes.build intervals positive direction moving spatial source member ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage
  let aligned : Nodes.Alignments nodes := Nodes.Alignments.build nodes
  let programmes : Nodes.Programmes nodes := Nodes.Programmes.build nodes
  let edges : nodes.Edges aligned := Nodes.Edges.build nodes aligned
  ⟨⟨nodes, aligned, programmes, edges⟩⟩

/-- The whole retained table is the same original four-factory execution in its raw field. -/
private theorem build_factory :
    build intervals positive direction moving spatial source member ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage =
    (let nodes : Nodes intervals positive direction moving spatial source member
         ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage :=
       Nodes.build intervals positive direction moving spatial source member ranges allocation admitted widths roots
         targetCurrent targetFloor targetRootStage
     let aligned : Nodes.Alignments nodes := Nodes.Alignments.build nodes
     let programmes : Nodes.Programmes nodes := Nodes.Programmes.build nodes
     let edges : nodes.Edges aligned := Nodes.Edges.build nodes aligned
     ⟨⟨nodes, aligned, programmes, edges⟩⟩) := rfl

variable {intervals positive direction moving spatial source member ranges allocation admitted widths roots
    targetCurrent targetFloor targetRootStage}
    (table : Table intervals positive direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)

/-- Read the SAME whole retained positive-node vector. -/
@[expose] def nodes : Nodes intervals positive direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage := table.raw.1

/-- Read the SAME common-view alignment vector, shared by both incident positive-positive edges. -/
@[expose] def aligned : Nodes.Alignments table.nodes := table.raw.2.1

/-- Read the SAME original programme cache vector on the actual node-producing shifted tuples. -/
@[expose] def programmes : Nodes.Programmes table.nodes := table.raw.2.2.1

/-- Read one SAME edge cache at its exact original ordered position. -/
@[expose] def edge (index : Fin (intervals - 1)) : Adjacent table.nodes table.aligned index :=
  (DependentVector.get table.raw.2.2.2 index).val

/-- Each whole stored edge retains the exact original once-executed adjacent factory. -/
theorem edge_eq (index : Fin (intervals - 1)) : table.edge index = Adjacent.build table.nodes table.aligned index :=
  (DependentVector.get table.raw.2.2.2 index).property

/-- Read the SAME original quadratic row certificate for an actual positive-positive edge. -/
@[expose] def certificate (edge : Fin (intervals - 1)) (order coordinate : Fin 2) :
    Calculus.Jet.Quadratic.Basic.Certificate
      (Sampling.gridPositiveIncrement intervals (Sampling.gridPairIndex intervals edge)
        (Sampling.gridPairFollowing intervals edge) direction) :=
  (table.edge edge).actual.certificates order coordinate

/-- The SAME stored base reads the literal first programme at its own actual selected stage. -/
theorem base (edge : Fin (intervals - 1)) (order coordinate : Fin 2) :
    (table.certificate edge order coordinate).base =
      (((table.programmes.entry (Sampling.gridPairIndex intervals edge)).targetProgram
        (next := (table.nodes.node (Sampling.gridPairIndex intervals edge)).next) (Specification.Table.baseIndex order
          coordinate)).model
        (table.nodes.node (Sampling.gridPairIndex intervals edge)).next.requested.selected.stage).integralSample :=
  base_program (index := Sampling.gridPairIndex intervals edge)
    (following := Sampling.gridPairFollowing intervals edge)
    (firstNode := table.nodes.node (Sampling.gridPairIndex intervals edge))
    (lastNode := table.nodes.node (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
      (Sampling.gridPairFollowing intervals edge)))
    (unit := pair_unit ranges allocation direction admitted intervals positive edge)
    (firstPositions := (table.edge edge).firstPositions) (lastPositions := (table.edge edge).lastPositions)
    (firstAligned := table.aligned.entry (Sampling.gridPairIndex intervals edge))
    (lastAligned := table.aligned.entry (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
      (Sampling.gridPairFollowing intervals edge))) (rows := (table.edge edge).rows)
    (table.edge edge).actual (table.programmes.entry (Sampling.gridPairIndex intervals edge)) order
    coordinate

/-- The SAME stored output reads the literal last programme at its own actual selected stage. -/
theorem output (edge : Fin (intervals - 1)) (order coordinate : Fin 2) :
    (table.certificate edge order coordinate).output =
      (((table.programmes.entry (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
        (Sampling.gridPairFollowing intervals edge))).targetProgram
        (next := (table.nodes.node (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
          (Sampling.gridPairFollowing intervals edge))).next) (Specification.Table.baseIndex order coordinate)).model
        (table.nodes.node (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
          (Sampling.gridPairFollowing intervals edge))).next.requested.selected.stage).integralSample :=
  output_program (index := Sampling.gridPairIndex intervals edge)
    (following := Sampling.gridPairFollowing intervals edge)
    (firstNode := table.nodes.node (Sampling.gridPairIndex intervals edge))
    (lastNode := table.nodes.node (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
      (Sampling.gridPairFollowing intervals edge)))
    (unit := pair_unit ranges allocation direction admitted intervals positive edge)
    (firstPositions := (table.edge edge).firstPositions) (lastPositions := (table.edge edge).lastPositions)
    (firstAligned := table.aligned.entry (Sampling.gridPairIndex intervals edge))
    (lastAligned := table.aligned.entry (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
      (Sampling.gridPairFollowing intervals edge))) (rows := (table.edge edge).rows)
    (table.edge edge).actual (table.programmes.entry (Sampling.gridNextIndex intervals
    (Sampling.gridPairIndex intervals edge) (Sampling.gridPairFollowing intervals edge))) order coordinate

/-- The SAME stored slope reads the literal first programme channel at its own actual selected stage. -/
theorem slope (edge : Fin (intervals - 1)) (order coordinate : Fin 2) :
    (table.certificate edge order coordinate).slope =
      (((table.programmes.entry (Sampling.gridPairIndex intervals edge)).targetProgram
        (next := (table.nodes.node (Sampling.gridPairIndex intervals edge)).next) (Specification.Table.slopeIndex
          order coordinate)).model
        (table.nodes.node (Sampling.gridPairIndex intervals edge)).next.requested.selected.stage).integralSample :=
  slope_program (index := Sampling.gridPairIndex intervals edge)
    (following := Sampling.gridPairFollowing intervals edge)
    (firstNode := table.nodes.node (Sampling.gridPairIndex intervals edge))
    (lastNode := table.nodes.node (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
      (Sampling.gridPairFollowing intervals edge)))
    (unit := pair_unit ranges allocation direction admitted intervals positive edge)
    (firstPositions := (table.edge edge).firstPositions) (lastPositions := (table.edge edge).lastPositions)
    (firstAligned := table.aligned.entry (Sampling.gridPairIndex intervals edge))
    (lastAligned := table.aligned.entry (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
      (Sampling.gridPairFollowing intervals edge))) (rows := (table.edge edge).rows)
    (table.edge edge).actual (table.programmes.entry (Sampling.gridPairIndex intervals edge)) order
    coordinate

/-- The four exact original programme rows satisfy the stored fixed-parent Taylor bound on every actual edge.

All three displayed samples use the original selected target stages. The
factor remains the original ValueBlocks.factor of the fixed old parents;
no claim replaces it by a smaller bound, completes a target bank, or attaches
a canonical cycle. Both actual target preparations and restriction banks
remain stored inside the original edge rows.
-/
theorem remainder_program_le (edge : Fin (intervals - 1)) (order coordinate : Fin 2) :
    Canonical.normSq
      ((((table.programmes.entry (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
        (Sampling.gridPairFollowing intervals edge))).targetProgram
          (next := (table.nodes.node (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
            (Sampling.gridPairFollowing intervals edge))).next)
          (Specification.Table.baseIndex order coordinate)).model
          (table.nodes.node (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
            (Sampling.gridPairFollowing intervals edge))).next.requested.selected.stage).integralSample -
        (((table.programmes.entry (Sampling.gridPairIndex intervals edge)).targetProgram
          (next := (table.nodes.node (Sampling.gridPairIndex intervals edge)).next)
          (Specification.Table.baseIndex order coordinate)).model
          (table.nodes.node (Sampling.gridPairIndex intervals edge)).next.requested.selected.stage).integralSample -
        Sampling.gridPositiveIncrement intervals (Sampling.gridPairIndex intervals edge) (Sampling.gridPairFollowing
          intervals edge) direction *
        (((table.programmes.entry (Sampling.gridPairIndex intervals edge)).targetProgram
          (next := (table.nodes.node (Sampling.gridPairIndex intervals edge)).next)
          (Specification.Table.slopeIndex order coordinate)).model
          (table.nodes.node (Sampling.gridPairIndex intervals edge)).next.requested.selected.stage).integralSample) ≤
      ValueBlocks.factor (covered := covered) order coordinate *
        Canonical.normSq (Sampling.gridPositiveIncrement intervals (Sampling.gridPairIndex intervals edge)
          (Sampling.gridPairFollowing intervals edge) direction) ^ 2 :=
  PositiveGridNode.remainder_program_le (index := Sampling.gridPairIndex intervals edge)
    (following := Sampling.gridPairFollowing intervals edge)
    (firstNode := table.nodes.node (Sampling.gridPairIndex intervals edge))
    (lastNode := table.nodes.node (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
      (Sampling.gridPairFollowing intervals edge)))
    (unit := pair_unit ranges allocation direction admitted intervals positive edge)
    (firstPositions := (table.edge edge).firstPositions) (lastPositions := (table.edge edge).lastPositions)
    (firstAligned := table.aligned.entry (Sampling.gridPairIndex intervals edge))
    (lastAligned := table.aligned.entry (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
      (Sampling.gridPairFollowing intervals edge))) (rows := (table.edge edge).rows)
    (table.edge edge).actual
    (table.programmes.entry (Sampling.gridPairIndex intervals edge)) (table.programmes.entry (Sampling.gridNextIndex
      intervals (Sampling.gridPairIndex intervals edge) (Sampling.gridPairFollowing intervals edge))) order coordinate

end Table

end PositiveGridNode

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
