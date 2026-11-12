module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Transport
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy.Grid
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Regular

/-! # One actual positive-node shifted acquisition on a common retained source

The original grid fraction derives admission from the single old strip
payment. The same retained source request and completed member are viewed
at that node's equal accuracy. One original target frame and one original
shifted request execute. A pure equality view retains the whole result on
the common old source for a later two-absolute-target comparison.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)
open Purelib.Curves.Legendre.Periods.Jets.Variation

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat}
    (intervals : Nat) (positive : 0 < intervals) (index : Fin intervals)
    (direction : Canonical) (moving : direction ≠ 0) (spatial : AccuracyRequest)
    (source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving))))
    (member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt })
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    (admitted : Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    {root : Named} (roots : RootChain (parent :: parents) root root)
    (targetCurrent targetFloor targetRootStage : Nat)

/-- One actual node frame, original request/member pair, shifted result and its SAME common-source view.

The existing Sigma/Subtype containers retain the whole original factories.
The target Request keeps its actual global Targets and selected stage. The
last field is only exact source-accuracy elimination on that result; it
contains no second shifted acquisition or independently prepared source.
-/
@[expose] def PositiveGridNode :=
  let offset := Sampling.gridOffset intervals index.succ direction
  let nodePaid := (Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted
  let equal := (Sampling.gridRequest_minimum intervals positive index direction moving spatial).symm
  (target : { value : Paths.Frame (parameter + offset) //
    value = ranges.targetFrame offset (nodePaid.trans allocation.bound_le_regularBound) }) ×
  (paid : { value : PositiveGridRequest (covered := covered) (chain := chain) (current := current)
      (floor := floor) (rootStage := rootStage) intervals positive index direction moving spatial //
    value = Requested.atPositiveGridNode intervals positive index direction moving spatial source member }) ×
  (next : { value : Shifted (increment := offset) (target := target.val) paid.val.1 ranges allocation
      nodePaid widths roots targetCurrent targetFloor targetRootStage //
    value = paid.val.1.shifted (increment := offset) (target := target.val) ranges allocation nodePaid widths roots
      targetCurrent targetFloor targetRootStage }) ×
  { common : Shifted (increment := offset) (target := target.val) source ranges allocation nodePaid widths roots
      targetCurrent targetFloor targetRootStage //
    common = ofSourceAccuracy (increment := offset) (target := target.val) equal source paid.val.1
      ((congrArg (fun retained : PositiveGridRequest (covered := covered) (chain := chain) (current := current)
          (floor := floor) (rootStage := rootStage) intervals positive index direction moving spatial => retained.1)
        paid.property).trans
          (Requested.atPositiveGridNode_requested_eq intervals positive index direction moving spatial source member))
      next.val }

/-- Materialize one actual positive-node shifted request and retain its equal-index common-source view.

The node's strip/regular admission is derived from the single original
whole-direction payment. The original source and its completed member are
not rebuilt. A target frame executes once, then the original shifted factory
executes once. Exact equality elimination performs no further acquisition.
-/
def atPositiveGridNode : PositiveGridNode intervals positive index direction moving spatial source member
    ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage :=
  let offset := Sampling.gridOffset intervals index.succ direction
  let nodePaid := (Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted
  let target := ranges.targetFrame offset (nodePaid.trans allocation.bound_le_regularBound)
  let paid := Requested.atPositiveGridNode intervals positive index direction moving spatial source member
  let next := paid.1.shifted (increment := offset) (target := target) ranges allocation nodePaid widths roots
    targetCurrent targetFloor targetRootStage
  let common := ofSourceAccuracy (increment := offset) (target := target)
    (Sampling.gridRequest_minimum intervals positive index direction moving spatial).symm source paid.1
    (Requested.atPositiveGridNode_requested_eq intervals positive index direction moving spatial source member) next
  ⟨⟨target, rfl⟩, ⟨paid, rfl⟩, ⟨next, rfl⟩, ⟨common, rfl⟩⟩

namespace PositiveGridNode

variable {intervals positive index direction moving spatial source member ranges allocation admitted widths roots
    targetCurrent targetFloor targetRootStage}
    (retained : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)

/-- Read the SAME once-built regular frame at the literal original positive-node absolute parameter. -/
@[expose] def target : Paths.Frame (parameter + Sampling.gridOffset intervals index.succ direction) :=
  retained.1.val

/-- Read the SAME entire source request/member pair produced by the original exact positive-node factory. -/
@[expose] def paid :
    PositiveGridRequest (covered := covered) (chain := chain) (current := current)
      (floor := floor) (rootStage := rootStage) intervals positive index direction moving spatial :=
  retained.2.1.val

/-- Read the SAME original target-producing shifted tuple at its precise node-minimum source index. -/
@[expose] def next :
    Shifted (increment := Sampling.gridOffset intervals index.succ direction) (target := retained.target)
      retained.paid.1 ranges allocation
      ((Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted)
      widths roots targetCurrent targetFloor targetRootStage :=
  retained.2.2.1.val

/-- Read the SAME complete shifted tuple over the common old source for a two-absolute-target comparison. -/
@[expose] def common :
    Shifted (increment := Sampling.gridOffset intervals index.succ direction) (target := retained.target)
      source ranges allocation
      ((Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted)
      widths roots targetCurrent targetFloor targetRootStage :=
  retained.2.2.2.val

/-- The retained target frame has its whole original same-node regular-frame factory. -/
theorem target_eq : retained.target = ranges.targetFrame (Sampling.gridOffset intervals index.succ direction)
    (((Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted).trans
      allocation.bound_le_regularBound) := retained.1.property

/-- The complete original source request and completed-member pair keep their exact whole factory. -/
theorem paid_eq : retained.paid =
    Requested.atPositiveGridNode intervals positive index direction moving spatial source member :=
  retained.2.1.property

/-- The retained original node source is exactly the common source at the equal whole accuracy index. -/
theorem source_eq : retained.paid.1 =
    source.castAccuracy (Sampling.gridRequest_minimum intervals positive index direction moving spatial).symm :=
  (congrArg (fun paid : PositiveGridRequest (covered := covered) (chain := chain) (current := current)
      (floor := floor) (rootStage := rootStage) intervals positive index direction moving spatial => paid.1)
    retained.paid_eq).trans
      (Requested.atPositiveGridNode_requested_eq intervals positive index direction moving spatial source member)

/-- The node's exact source view retains the SAME complete common original Requested value. -/
theorem source_heq : HEq retained.paid.1 source :=
  (heq_of_eq retained.source_eq).trans
    (source.castAccuracy_heq
      (Sampling.gridRequest_minimum intervals positive index direction moving spatial).symm)

/-- The node keeps the SAME already-completed source member; no readiness, root acquisition or checking is replayed. -/
theorem member_heq : HEq retained.paid.2 member := by
  have project (first last : PositiveGridRequest (covered := covered) (chain := chain) (current := current)
      (floor := floor) (rootStage := rootStage) intervals positive index direction moving spatial)
      (equal : first = last) : HEq first.2 last.2 := by
    cases equal
    rfl
  exact (project retained.paid _ retained.paid_eq).trans
    (Requested.atPositiveGridNode_member_heq intervals positive index direction moving spatial source member)

/-- The entire target-producing shifted tuple keeps the original factory on its own literal node-source cache. -/
theorem next_eq : retained.next = retained.paid.1.shifted
    (increment := Sampling.gridOffset intervals index.succ direction) (target := retained.target) ranges allocation
    ((Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted) widths roots
      targetCurrent targetFloor targetRootStage := retained.2.2.1.property

/-- Every actual target model at the node pays the SAME common local-increment request.

The original target factory already pays its own node-minimum request.
The whole exact request identity transports that scalar bound without
replacing a model, reading, observation or target allocation.
-/
theorem target_allowance_lt
    (targetIndex : Fin (retained.next.requested.request.shape.val.1 ::
      retained.next.requested.request.shape.val.2).length) (channel : Fin 6) :
    ((retained.next.requested.prepared.entry targetIndex).preparation.cell.models.cell channel).localAllowance <
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving))).tolerance :=
  (retained.next.target_allowance_lt targetIndex channel).trans_eq
    (congrArg AccuracyRequest.tolerance
      (Sampling.gridRequest_minimum intervals positive index direction moving spatial))

/-- The common-source view keeps the exact pure transport factory on the SAME actual node result. -/
theorem common_eq : retained.common = ofSourceAccuracy
    (increment := Sampling.gridOffset intervals index.succ direction) (target := retained.target)
    (Sampling.gridRequest_minimum intervals positive index direction moving spatial).symm source retained.paid.1
    retained.source_eq retained.next := retained.2.2.2.property

/-- Both source-index displays retain the entire SAME target request, traces, geometry, Steps and factory equations. -/
theorem common_heq : HEq retained.common retained.next :=
  (heq_of_eq retained.common_eq).trans
    (ofSourceAccuracy_heq
      (increment := Sampling.gridOffset intervals index.succ direction) (target := retained.target)
      (Sampling.gridRequest_minimum intervals positive index direction moving spatial).symm source retained.paid.1
      retained.source_eq retained.next)

end PositiveGridNode

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
