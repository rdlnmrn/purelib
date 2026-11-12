module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Programs
public import Purelib.Data.Vector.Dependent
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Alignment
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip

/-! # Stored positive grid nodes and their original programme and alignment products

One original common-accuracy source request and its genuine completed member
precede the finite node producer. Each entry retains the entire original
node factory. Original programme caches and signed alignment products are
then stored once on those SAME entries, before adjacent comparisons.
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
  (ValueBlocks)

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

/-- The original positive-node factories stored once in the original finite node order.

Each existing dependent-vector entry retains the whole original factory
identity, including its frame, common source/member view and actual target
Request. No target Completion or independently prepared source is an input.
-/
@[expose] def Nodes := DependentVector (fun index : Fin intervals =>
  { value : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage //
    value = atPositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage })

namespace Nodes

/-- Materialize each original positive node once, sharing the SAME original source and completed member. -/
def build : Nodes intervals positive direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage :=
  DependentVector.ofFn (fun index =>
    ⟨atPositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage, rfl⟩)

variable {intervals positive direction moving spatial source member ranges allocation admitted widths roots
    targetCurrent targetFloor targetRootStage}
    (nodes : Nodes intervals positive direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)

/-- Read one SAME actual node, retaining its complete source and target indices. -/
@[expose] def node (index : Fin intervals) : PositiveGridNode intervals positive index direction moving spatial source
  member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage :=
  (DependentVector.get nodes index).val

/-- The entire retained node has its original once-executed factory at this literal positive index. -/
theorem node_eq (index : Fin intervals) : nodes.node index =
    atPositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage :=
  (DependentVector.get nodes index).property

/-- One original signed alignment product on the SAME stored common block caches. -/
@[expose] def Alignment (index : Fin intervals) :=
  DependentProduct (parent :: parents) (fun outer => Acquisition.Segment.RootComparisons.Alignment
    (DependentProduct.get (parent :: parents) (nodes.node index).common.blocks outer).comparison.paths
    (DependentProduct.get (parent :: parents) (nodes.node index).common.blocks outer).comparison.firstReference)

/-- Actual original signed alignment products retained once per node, outside every adjacent/query callback. -/
@[expose] def Alignments := DependentVector (fun index : Fin intervals =>
  { value : nodes.Alignment index // value = DependentProduct.ofFn (parent :: parents) (fun outer =>
    (DependentProduct.get (parent :: parents) (nodes.node index).common.blocks outer).comparison.align) })

namespace Alignments

/-- Derive each original block alignment from its actual retained comparison, with no signed-relation premise. -/
def build : Alignments nodes := DependentVector.ofFn (fun index =>
  ⟨DependentProduct.ofFn (parent :: parents) (fun outer =>
    (DependentProduct.get (parent :: parents) (nodes.node index).common.blocks outer).comparison.align), rfl⟩)

variable {nodes} (aligned : Alignments nodes)

/-- Read the SAME stored original alignment product for one actual node. -/
@[expose] def entry (index : Fin intervals) : nodes.Alignment index :=
  (DependentVector.get aligned index).val

/-- Exact quantified alignment-entry factory readback on its original retained nodes and comparisons. -/
abbrev EntryEquation : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current : Nat}
    {floor : Nat}
    {rootStage : Nat}
    {intervals : Nat}
    {positive : 0 < intervals}
    {direction : Canonical}
    {moving : direction ≠ 0}
    {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered}
    {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named}
    {roots : RootChain (parent :: parents) root root}
    {targetCurrent : Nat}
    {targetFloor : Nat}
    {targetRootStage : Nat}
    {nodes : Nodes intervals positive direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    (aligned : Alignments nodes)
    (index : Fin intervals),
    aligned.entry index =
    DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) (nodes.node index).common.blocks outer).comparison.align)

/-- The complete alignment product retains the exact original producer on those SAME block comparisons. -/
theorem entry_eq : EntryEquation := by
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage nodes aligned index
  exact (DependentVector.get aligned index).property

end Alignments

/-- The original four-row programme cache owner on the SAME actual node-producing shifted tuple. -/
@[expose] def Programme (index : Fin intervals) := ValueBlocks
  (source := (nodes.node index).paid.1) (next := (nodes.node index).next)
  (spatial := spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
    (Sampling.gridIncrement_nonzero intervals positive direction moving)))
  (nonzero := Sampling.gridOffset_nonzero intervals positive index direction moving)

/-- Original programme caches stored once per node, preserving their own six channels and selected Request. -/
@[expose] def Programmes := DependentVector (fun index : Fin intervals =>
  { value : nodes.Programme index // value = ValueBlocks.build (next := (nodes.node index).next) })

namespace Programmes

/-- Construct each original programme block cache once on its SAME retained node, without another acquisition.

These are genuinely new original restriction/integral caches. Their bounded
query callbacks retain their own Sample factories. Their internal alignments
are distinct original caches from the common-view products above; no
historical or cross-owner cache sharing is claimed between those producers.
-/
def build : Programmes nodes := DependentVector.ofFn (fun index =>
  ⟨ValueBlocks.build (next := (nodes.node index).next), rfl⟩)

variable {nodes} (programmes : Programmes nodes)

/-- Read one SAME original programme owner on its actual node's retained shifted tuple. -/
@[expose] def entry (index : Fin intervals) : nodes.Programme index :=
  (DependentVector.get programmes index).val

/-- The complete original programme cache retains its actual once-executed builder. -/
theorem entry_eq (index : Fin intervals) : programmes.entry index = ValueBlocks.build (next := (nodes.node
  index).next) :=
  (DependentVector.get programmes index).property

end Programmes

end Nodes

end PositiveGridNode

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
