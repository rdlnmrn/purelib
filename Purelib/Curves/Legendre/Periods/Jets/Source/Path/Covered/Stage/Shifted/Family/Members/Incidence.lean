module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Sewing
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Closed
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Queries
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Comparison.Incidence
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.TraceEndpoints
import Purelib.Riemann.Integration.PreparedConstantModels.Query.Transport
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Paths.PreparedSegmentSources
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Linked
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Alignment
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.RootPath
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents
import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Comparison
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Data.List.DependentProduct
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Actual sewn-path incidence on the SAME retained member's closed state

Each actual comparison-cache View supplies its original three links. The
GIVEN StripData retains the same occurrence map, endpoint observations and
Alignments. One original closedState is bound on this member's own Frame;
its actual child occurrences and stages consume those SAME caches.
Stationary erasure below is geometric incidence, not cancellation of any
independently normalized primitive observations.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.LocalMember

open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Comparison
open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

attribute [local irreducible] Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] PreparedParent.ShiftedAcquisition.Linked.first
attribute [local irreducible] Shifted.requested ShiftedGeometry.Requested.request ShiftedGeometry.Request.shape

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {reference : AccuracyRequest}
    {source : Requested covered chain current floor rootStage reference}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    {zeroPaid : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound}
    {zero : LocalMember source ranges allocation roots widths targetCurrent targetFloor targetRootStage 0 zeroPaid}
    {increment : Canonical} {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    (cached : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage increment admitted)

/-- A GIVEN actual stage cache retains the same whole original jet stage through its complete family factory.

The source model/Targets owner is the GIVEN StageData value. This transports
only its actual whole factory; the new centered state models are never
substituted for the independent original source-model bank.
-/
theorem queryStage_heq (stage : Nat) (retained : QueryStage cached stage) :
    HEq (cached.jet.source.stages stage) retained.val.2.stage :=
  Eq.rec (motive := fun (value : StageData cached stage) _ =>
    HEq (cached.jet.source.stages stage) value.2.stage)
    (LocalMember.stage_heq (cached := cached) stage) retained.property.symm

/-- The original comparison-cache incidence type at one literal GIVEN member block. -/
@[expose] def BlockIncidence (outer : Fin (parent :: parents).length) : Type _ :=
  let block := DependentProduct.get (parent :: parents) cached.member.blocks outer
  Cache.Incidence (curve := Fibre.frameCurve cached.targetFrame) (differential := basis)
    block.comparison.paths

/-- One actual pieces spine per GIVEN block, retaining the SAME cache/View construction factory. -/
@[expose] def PieceBank :=
  DependentProduct (parent :: parents) (fun outer =>
    {value : BlockIncidence (cached := cached) outer // value = Cache.Incidence.build
      (curve := Fibre.frameCurve cached.targetFrame) (differential := basis)
      (DependentProduct.get (parent :: parents) cached.member.blocks outer).comparison.paths})

/-- Read every original block cache once and retain its actual pieces without another source, View or reference. -/
def pieceBank : PieceBank (cached := cached) :=
  DependentProduct.ofFn (parent :: parents) (fun outer =>
    let pieces := Cache.Incidence.build
      (curve := Fibre.frameCurve cached.targetFrame) (differential := basis)
      (DependentProduct.get (parent :: parents) cached.member.blocks outer).comparison.paths
    ⟨pieces, rfl⟩)

namespace Incidence

/-- The exact original closed-state type on this member's target Frame and retained first root name. -/
@[expose] def State :=
  let first := DependentProduct.get (parent :: parents) cached.member.blocks 0
  RootClosedState (Fibre.frameCurve cached.targetFrame) basis first.first.root.value.name

/-- The whole given sewing and strip data retain their original input identities. -/
@[expose] def Inputs
    {continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted}
    (sewn : Sewing (cached := cached) (zero := zero) continued) (data : StripData cached) :=
  {value : Sewing (cached := cached) (zero := zero) continued × StripData cached // value = (sewn, data)}

/-- The whole once-bound original closed state retains its complete same-member constructor factory. -/
@[expose] def StateCache :=
  {state : State (cached := cached) // state = closedState (cached := cached)}

end Incidence

attribute [local irreducible] LocalMember Sewing StripData PieceBank Incidence.Inputs Incidence.StateCache in
set_option genInjectivity false in
/-- The GIVEN sewn path and strip caches, actual original closed state and complete retained pieces bank.

All geometric/root conclusions are derived from these constructors and
whole old factories. There is no supplied erasure, flatness, path equality,
period equality or final comparison bound. The named cache preserves this
ownership boundary without expanding the whole input products during compilation.
-/
structure Incidence
    {continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted}
    (sewn : Sewing (cached := cached) (zero := zero) continued) (data : StripData cached) : Type _ where
  /-- The same whole original sewing and strip caches, with their defining input identity. -/
  originals : Incidence.Inputs (cached := cached) (zero := zero) (continued := continued) sewn data
  /-- The same actual finite pieces bank and its original per-block factories. -/
  pieceCache : PieceBank (cached := cached)
  /-- The once-bound original member closed state and its whole factory. -/
  closedCache : Incidence.StateCache (cached := cached)

attribute [local irreducible] LocalMember Sewing StripData PieceBank Incidence.Inputs Incidence.StateCache in
constructive_injectivity Incidence

section Assembly

attribute [local irreducible] LocalMember Sewing StripData

/-- Attach the SAME supplied sewn representative to one original closed-state view and its GIVEN strip query caches.

The original StripData already owns its occurrences, shared endpoint
observations and once-built Alignments. This operation projects them; its
new work is actual pieces extraction/sign outputs and one closed-state
representation. It executes no member, source, stage or query producer.
-/
def incidence
    {continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted}
    (sewn : Sewing (cached := cached) (zero := zero) continued) (data : StripData cached) :
    Incidence (cached := cached) (zero := zero) (continued := continued) sewn data :=
  let originals : Incidence.Inputs (cached := cached) (zero := zero) (continued := continued) sewn data :=
    ⟨(sewn, data), rfl⟩
  let pieces : PieceBank (cached := cached) := pieceBank (cached := cached)
  let state : Incidence.StateCache (cached := cached) :=
    ⟨closedState (cached := cached), rfl⟩
  ⟨originals, pieces, state⟩

end Assembly

namespace Incidence

variable {cached}
    {continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted}
    {sewn : Sewing (cached := cached) (zero := zero) continued} {data : StripData cached}
    (attached : Incidence (cached := cached) (zero := zero) (continued := continued) sewn data)

/-- The whole GIVEN sewing and actual original strip caches remain retained unchanged. -/
theorem originals_eq : attached.originals.val = (sewn, data) := attached.originals.property

/-- Read the SAME actual finite pieces bank. -/
@[expose] def pieces : PieceBank (cached := cached) := attached.pieceCache

/-- Read the SAME once-bound original member closed state on its OWN target Frame. -/
@[expose] def state : State (cached := cached) := attached.closedCache.val

/-- The whole original closed state is its actual same-member constructor, without any new preparation. -/
theorem state_eq : attached.state = closedState (cached := cached) := attached.closedCache.property

/-- The retained state has exactly the SAME complete original member parent list. -/
theorem state_parents : attached.state.state.parents = cached.member.geometry.parents :=
  cached.member.closedState_parents attached.state
    (attached.state_eq.trans (closedState_eq (cached := cached)))

/-- The retained state keeps the SAME member's whole original centered path under its actual dependent endpoints. -/
theorem state_path : HEq attached.state.state.path cached.member.geometry.chain.path :=
  cached.member.closedState_path attached.state
    (attached.state_eq.trans (closedState_eq (cached := cached)))

/-- The retained state keeps the SAME actual signed child RootChain, including every original ordered handoff. -/
theorem state_roots : HEq attached.state.roots cached.member.geometry.roots :=
  cached.member.closedState_roots attached.state
    (attached.state_eq.trans (closedState_eq (cached := cached)))

/-- Every actual member jet stage has this SAME complete closed lifted representative. -/
theorem cycle_at (stage : Nat) : cached.jet.cycle.liftedPath stage =
    attached.state.state.closedLift attached.state.closed :=
  closedState_cycle (cached := cached) attached.state attached.state_eq stage

/-- Read one retained block pieces spine without evaluating its constructor again. -/
@[expose] def block (outer : Fin (parent :: parents).length) : BlockIncidence (cached := cached) outer :=
  (DependentProduct.get (parent :: parents) attached.pieces outer).val

/-- Every actual retained block pieces spine is its SAME original comparison-cache factory. -/
theorem block_eq (outer : Fin (parent :: parents).length) : attached.block outer =
    Cache.Incidence.build (curve := Fibre.frameCurve cached.targetFrame) (differential := basis)
      (DependentProduct.get (parent :: parents) cached.member.blocks outer).comparison.paths :=
  (DependentProduct.get (parent :: parents) attached.pieces outer).property

/-- Every block's expanded pieces preserve every actual original physical OwnerPath vertex. -/
theorem block_vertices (outer : Fin (parent :: parents).length) :
    (blockPath (cached := cached) outer).vertices =
      Cache.Incidence.vertices (curve := Fibre.frameCurve cached.targetFrame) (differential := basis)
        (DependentProduct.get (parent :: parents) cached.member.blocks outer).comparison.paths (attached.block outer) :=
  ((DependentProduct.get (parent :: parents) cached.member.blocks outer).shifted.acquired.rootTrace_vertices
    (DependentProduct.get (parent :: parents) cached.member.blocks outer).actual.val
    (DependentProduct.get (parent :: parents) cached.member.blocks outer).actual.property).symm.trans
      (Cache.Incidence.vertices_eq (curve := Fibre.frameCurve cached.targetFrame) (differential := basis)
        (DependentProduct.get (parent :: parents) cached.member.blocks outer).comparison.paths (attached.block outer))

/-- Omitting only the two recorded stationary positions leaves this SAME block's actual centered-child endpoint word. -/
theorem block_moving (outer : Fin (parent :: parents).length) :
    Cache.Incidence.movingVertices (curve := Fibre.frameCurve cached.targetFrame) (differential := basis)
      (DependentProduct.get (parent :: parents) cached.member.blocks outer).comparison.paths (attached.block outer) =
      ((DependentProduct.get (parent :: parents) cached.member.blocks outer).shifted.parents.covered.parents).map
        (fun child => child.edge.point 1) :=
  (Cache.Incidence.moving_parents (curve := Fibre.frameCurve cached.targetFrame) (differential := basis)
    (DependentProduct.get (parent :: parents) cached.member.blocks outer).comparison.paths (attached.block outer)
    (DependentProduct.get (parent :: parents) cached.member.blocks outer).shifted.parents.centers).trans
      (congrArg (List.map (fun child => child.edge.point 1))
        (DependentProduct.get (parent :: parents) cached.member.blocks outer).shifted.parents.parents_eq).symm

/-- The actual whole sewn word retains every expanded original piece and every separate interior handoff.

The block comparison uses exact original rootTrace transports and the SAME
retained View pieces. The final/first join remains the distinct original
closing cache; it is not inserted again into this open vertex word.
-/
theorem sewn_vertices :
    (returningPath (cached := cached) (Sewing.path (cached := cached) (zero := zero) sewn)).vertices =
      OwnerPath.interleaveVertices parents.length
        (fun outer => Cache.Incidence.vertices
          (curve := Fibre.frameCurve cached.targetFrame) (differential := basis)
          (DependentProduct.get (parent :: parents) cached.member.blocks outer).comparison.paths
          (attached.block outer))
        (fun index => (startVertex (cached := cached) index.succ).1) :=
  (Sewing.vertices (cached := cached) (zero := zero) sewn).trans
    (OwnerPath.interleaveVertices_congr parents.length _ _ _
      (fun outer => attached.block_vertices outer))

/-- Erasing just the retained stationary positions gives the SAME state's entire ordered child endpoint word.

The finite table uses the original outer occurrences, including equal or
stationary parents. The original flattened geometry factory identifies
this word; no Owner, root sign, Frame or primitive offset is inferred from
this scalar endpoint-list equality.
-/
theorem moving_state_word :
    (List.ofFn (fun outer => Cache.Incidence.movingVertices
      (curve := Fibre.frameCurve cached.targetFrame) (differential := basis)
      (DependentProduct.get (parent :: parents) cached.member.blocks outer).comparison.paths
      (attached.block outer))).flatten =
      attached.state.state.parents.map (fun child => child.edge.point 1) := by
  have blocks := OfFn.Basic.ofFn_congr (fun outer => attached.block_moving outer)
  have allParents : attached.state.state.parents =
      (ShiftedGeometry.blockWords source.prepared ranges allocation admitted widths cached.member.blocks).flatten :=
    attached.state_parents.trans (childWords_eq (cached := cached))
  have flattened := Flatten.map_flatten (fun child => child.edge.point 1)
    (ShiftedGeometry.blockWords source.prepared ranges allocation admitted widths cached.member.blocks)
  have indexed := OfFn.Basic.map_ofFn
    (function := fun outer =>
      (DependentProduct.get (parent :: parents) cached.member.blocks outer).shifted.parents.covered.parents)
    (transform := List.map (fun child => child.edge.point 1))
  exact (congrArg List.flatten blocks).trans
    ((congrArg List.flatten indexed.symm).trans
      (flattened.symm.trans (congrArg (List.map (fun child => child.edge.point 1)) allParents.symm)))

/-- The original target Request and retained closed state have the SAME whole parent word. -/
theorem request_parents :
    (cached.member.requested.request.shape.val.1 :: cached.member.requested.request.shape.val.2) =
      attached.state.state.parents :=
  cached.member.requested.request.shape.property.symm.trans attached.state_parents.symm

/-- Reindex one bounded closed-state occurrence into the SAME original target Request word. -/
@[expose] def sourceIndex (index : Fin attached.state.state.parents.length) :
    Fin (cached.member.requested.request.shape.val.1 :: cached.member.requested.request.shape.val.2).length :=
  ⟨index.val, Eq.mp (congrArg (fun word => index.val < word.length) attached.request_parents.symm) index.isLt⟩

/-- The occurrence transport preserves the original literal natural position, including repeated parents. -/
theorem sourceIndex_val (index : Fin attached.state.state.parents.length) :
    (attached.sourceIndex index).val = index.val := by rfl

/-- The actual whole centered parent is preserved when moving from the state to the original Request occurrence. -/
theorem state_requestParent (index : Fin attached.state.state.parents.length) :
    attached.state.state.parents[index.val]'index.isLt =
      (cached.member.requested.request.shape.val.1 :: cached.member.requested.request.shape.val.2)[
        (attached.sourceIndex index).val]'(attached.sourceIndex index).isLt :=
  getElem_congr attached.request_parents.symm rfl index.isLt

/-- Locate the state child through the SAME already retained original strip occurrence map. -/
@[expose] def located (index : Fin attached.state.state.parents.length) :
    ShiftedGeometry.Occurrence
      (parameter := parameter) (increment := increment) (frame := frame) (basis := basis)
      (target := cached.targetFrame) (count := count) (firstParent := parent) (remaining := parents)
      (covered := covered) (floor := floor) (original := chain.path)
      (stage := source.selected.stage) (targets := source.targets) (prepared := source.prepared)
      (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
      (whole := cached.member.geometry) (requestIndex := cached.member.requested.selected.stage)
      (globalFloor := targetFloor) (rootStage := targetRootStage)
      cached.member.blocks cached.member.requested.request (attached.sourceIndex index) :=
  StripQueryCache.located (cached := cached) (StripData.queries (cached := cached) data) (attached.sourceIndex index)

/-- Each state child is the SAME original block/local child, with its actual occurrence and whole edge record. -/
theorem parent_eq (index : Fin attached.state.state.parents.length) :
    attached.state.state.parents[index.val]'index.isLt =
      (DependentProduct.get (parent :: parents) cached.member.blocks
        (attached.located index).block).shifted.parents.covered.parents[
        (attached.located index).child.val]'(attached.located index).child.isLt :=
  (attached.state_requestParent index).trans (attached.located index).parent_eq

/-- Every actual state occurrence keeps its original ordered interval on the SAME block's own shifted segment.

The existing SegmentSource retains its two endpoint fractions and their
orientation. Only the whole centered-parent identity is transported; no
common ambient, new path or independently prepared child is introduced.
-/
theorem child_source (index : Fin attached.state.state.parents.length) :
    Riemann.Paths.PreparedSegmentSources.SegmentSource
      (DependentProduct.get (parent :: parents) cached.member.blocks (attached.located index).block).shifted.segment
      (attached.state.state.parents[index.val]'index.isLt) :=
  Eq.mp (congrArg (fun child => Riemann.Paths.PreparedSegmentSources.SegmentSource
      (DependentProduct.get (parent :: parents) cached.member.blocks (attached.located index).block).shifted.segment
      child) (attached.parent_eq index).symm)
    (child_segmentSource (cached := cached) (attached.located index).block (attached.located index).child)

/-- All rational child fractions read the SAME original source-parent parameter map at the literal state occurrence.

Both scalar transports come from the whole actual parent equality. The
old source's Frame and the member's target Frame remain distinct; the
statement identifies physical fractions without retyping either root.
-/
theorem source_point (index : Fin attached.state.state.parents.length) (input : Rational) :
    (attached.state.state.parents[index.val]'index.isLt).edge.point input =
      ((parent :: parents)[(attached.located index).block.val]'(attached.located index).block.isLt).edge.point
        (Riemann.Branches.PreparedSheetContinuation.parameterAt
          (attached.state.state.parents[index.val]'index.isLt).edge.left
          (attached.state.state.parents[index.val]'index.isLt).edge.request input) := by
  have point := congrArg (fun child => child.edge.point input) (attached.parent_eq index)
  have fraction := congrArg (fun child =>
    ((parent :: parents)[(attached.located index).block.val]'(attached.located index).block.isLt).edge.point
      (Riemann.Branches.PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input))
    (attached.parent_eq index)
  exact point.trans ((child_point (cached := cached)
    (attached.located index).block (attached.located index).child input).trans fraction.symm)

/-- Reindex the SAME GIVEN direct Query through literal identity of the state and Request whole edge records. -/
def stateQuery (index : Fin attached.state.state.parents.length) (input : Rational)
    (inside : 0 ≤ input ∧ input ≤ 1)
    (direct : ChildQuery cached (attached.sourceIndex index) input inside) :
    PreparedEdge.Query (attached.state.state.parents[index.val]'index.isLt).edge input inside :=
  PreparedEdge.Query.castEdge (congrArg CenteredEdge.edge (attached.state_requestParent index).symm) direct

/-- The state-indexed direct Query is the SAME complete original cache and factory under its exact edge transport. -/
theorem stateQuery_heq (index : Fin attached.state.state.parents.length) (input : Rational)
    (inside : 0 ≤ input ∧ input ≤ 1)
    (direct : ChildQuery cached (attached.sourceIndex index) input inside) :
    HEq (attached.stateQuery index input inside direct) direct :=
  PreparedEdge.Query.castEdge_heq (congrArg CenteredEdge.edge (attached.state_requestParent index).symm) direct

/-- The physical-index Owner of the state Query is the whole original direct-query Owner, not a new root selection. -/
theorem stateQuery_owner_heq (index : Fin attached.state.state.parents.length) (input : Rational)
    (inside : 0 ≤ input ∧ input ≤ 1)
    (direct : ChildQuery cached (attached.sourceIndex index) input inside) :
    HEq (attached.stateQuery index input inside direct).owner direct.owner :=
  PreparedEdge.Query.castEdge_owner_heq (congrArg CenteredEdge.edge (attached.state_requestParent index).symm) direct

/-- Consume GIVEN original old/new observations and direct Query at the SAME actual state occurrence.

The original queryStrip constructs its actual parameter Step/reference
comparison using this SAME given Stage and retained Alignment. All input
answers remain the original caches; no observation is executed by this
entry and no finishing/query agreement is an input.
-/
def queryGiven (stage : Nat) (retained : QueryStage cached stage)
    (index : Fin attached.state.state.parents.length) (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (old : SourceObservations cached (StripData.queries (cached := cached) data)
      (attached.sourceIndex index) input inside)
    (observed : TargetObservations cached stage retained (attached.sourceIndex index) input inside)
    (direct : ChildQuery cached (attached.sourceIndex index) input inside) :
    StripQuery cached (StripData.queries (cached := cached) data) stage retained
      (attached.sourceIndex index) input inside old observed :=
  queryStrip (cached := cached) (StripData.queries (cached := cached) data) stage retained
    (attached.sourceIndex index) input inside old observed direct

/-- Read the three actual internal boundaries of one retained block child and restore the SAME original block path.

The original raw child index reads the given comparison-cache pieces.
Exact original endpoint/Owner inverse casts restore those three given
splits; no materialized trace, source, query or path factory is replayed.
-/
def localSplits (outer : Fin (parent :: parents).length)
    (inner : Fin (DependentProduct.get (parent :: parents) cached.member.blocks
      outer).shifted.parents.covered.parents.length) :
    OwnerPath.Split (blockPath (cached := cached) outer) ×
      OwnerPath.Split (blockPath (cached := cached) outer) × OwnerPath.Split (blockPath (cached := cached) outer) :=
  let row := DependentProduct.get (parent :: parents) cached.member.blocks outer
  let raw := Trace.rawIndex (curve := Fibre.frameCurve cached.targetFrame) (differential := basis)
    (sheet := ((parent :: parents)[outer.val]'outer.isLt).edge.sheet)
    row.shifted.acquired.traced.prepared.subdivision row.shifted.parents.centers
    (Acquisition.Segment.Parents.centeredIndex row.shifted.parents inner)
  let divided := Cache.Incidence.splitsAt
    (curve := Fibre.frameCurve cached.targetFrame) (differential := basis)
    row.comparison.paths (attached.block outer) raw
  ⟨row.shifted.acquired.restoreSplit row.actual.val row.actual.property divided.1,
    row.shifted.acquired.restoreSplit row.actual.val row.actual.property divided.2.1,
    row.shifted.acquired.restoreSplit row.actual.val row.actual.property divided.2.2⟩

/-- Restoring all three local boundaries preserves their complete original internal point/Owner pairs.

Only the actual rootTrace's original endpoint and Owner reindices are
reversed. The source, moving and retention boundaries stay separate even
when their physical coordinates agree.
-/
theorem localSplits_vertices (outer : Fin (parent :: parents).length)
    (inner : Fin (DependentProduct.get (parent :: parents) cached.member.blocks
      outer).shifted.parents.covered.parents.length) :
    let row := DependentProduct.get (parent :: parents) cached.member.blocks outer
    let raw := Trace.rawIndex (curve := Fibre.frameCurve cached.targetFrame) (differential := basis)
      (sheet := ((parent :: parents)[outer.val]'outer.isLt).edge.sheet)
      row.shifted.acquired.traced.prepared.subdivision row.shifted.parents.centers
      (Acquisition.Segment.Parents.centeredIndex row.shifted.parents inner)
    let divided := Cache.Incidence.splitsAt
      (curve := Fibre.frameCurve cached.targetFrame) (differential := basis)
      row.comparison.paths (attached.block outer) raw
    ((attached.localSplits outer inner).1.vertex,
      (attached.localSplits outer inner).2.1.vertex, (attached.localSplits outer inner).2.2.vertex) =
        (divided.1.vertex, divided.2.1.vertex, divided.2.2.vertex) := by
  unfold localSplits
  exact congrArg₂ Prod.mk
    (Acquisition.Segment.restoreSplit_vertex _ _ _ _)
    (congrArg₂ Prod.mk
      (Acquisition.Segment.restoreSplit_vertex _ _ _ _)
      (Acquisition.Segment.restoreSplit_vertex _ _ _ _))

/-- The actual three constructor boundaries of a closed-state child on the SAME whole sewn path.

The original occurrence map supplies both bounded local indices. All
three local splits are bound once, then the same whole path is read at
those boundaries; repeated/stationary slots remain separate occurrences.
The final/first closing join stays separately retained in the given Sewing.
-/
def childSplits (index : Fin attached.state.state.parents.length) :
    OwnerPath.Split (Sewing.path (cached := cached) (zero := zero) sewn) ×
      OwnerPath.Split (Sewing.path (cached := cached) (zero := zero) sewn) ×
      OwnerPath.Split (Sewing.path (cached := cached) (zero := zero) sewn) :=
  let slot := attached.located index
  let localPieces := attached.localSplits slot.block slot.child
  ⟨Sewing.splitBlock (cached := cached) (zero := zero) sewn slot.block localPieces.1,
    Sewing.splitBlock (cached := cached) (zero := zero) sewn slot.block localPieces.2.1,
    Sewing.splitBlock (cached := cached) (zero := zero) sewn slot.block localPieces.2.2⟩

/-- Each actual whole-path child boundary keeps the SAME complete selected original block point and Owner.

The global operation reads the given path at the original prefix count.
Its proof uses the retained concatenation factory and never constructs a
second tail path or a coordinate-derived replacement Owner.
-/
theorem childSplits_vertices (index : Fin attached.state.state.parents.length) :
    let slot := attached.located index
    let divided := attached.localSplits slot.block slot.child
    ((attached.childSplits index).1.vertex,
      (attached.childSplits index).2.1.vertex, (attached.childSplits index).2.2.vertex) =
        (divided.1.vertex, divided.2.1.vertex, divided.2.2.vertex) := by
  unfold childSplits
  exact congrArg₂ Prod.mk
    (Sewing.splitBlock_vertex (cached := cached) (zero := zero) sewn _ _)
    (congrArg₂ Prod.mk
      (Sewing.splitBlock_vertex (cached := cached) (zero := zero) sewn _ _)
      (Sewing.splitBlock_vertex (cached := cached) (zero := zero) sewn _ _))

/-- Run one original actual stage/query operation at the state occurrence, retaining its complete old/new answer caches.

The original producer performs its genuine per-query observations, direct
Query and parameter Step work. It reuses this SAME StripData occurrence
map/Alignment and GIVEN actual Stage value. No all-query result is claimed
to have been precomputed or memoized.
-/
def queryAt (stage : Nat) (retained : QueryStage cached stage)
    (index : Fin attached.state.state.parents.length) (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1) :
    StripQueryAt cached (StripData.queries (cached := cached) data) stage retained
      (attached.sourceIndex index) input inside :=
  queryStripAt (cached := cached) (StripData.queries (cached := cached) data) stage retained
    (attached.sourceIndex index) input inside

/-- The complete per-query output is exactly the original producer on the SAME retained caches and actual stage. -/
theorem queryAt_eq (stage : Nat) (retained : QueryStage cached stage)
    (index : Fin attached.state.state.parents.length) (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1) :
    attached.queryAt stage retained index input inside =
      queryStripAt (cached := cached) (StripData.queries (cached := cached) data) stage retained
        (attached.sourceIndex index) input inside := by
  unfold queryAt
  rfl

/-- Read the SAME already produced direct Query under its actual closed-state edge index. -/
def stateDirect (stage : Nat) (retained : QueryStage cached stage)
    (index : Fin attached.state.state.parents.length) (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (queried : StripQueryAt cached (StripData.queries (cached := cached) data) stage retained
      (attached.sourceIndex index) input inside) :
    PreparedEdge.Query (attached.state.state.parents[index.val]'index.isLt).edge input inside :=
  attached.stateQuery index input inside queried.2.2.1.val

/-- The state direct Owner is the actual Owner of that SAME whole original stage/query result. -/
theorem stateDirect_owner_heq (stage : Nat) (retained : QueryStage cached stage)
    (index : Fin attached.state.state.parents.length) (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (queried : StripQueryAt cached (StripData.queries (cached := cached) data) stage retained
      (attached.sourceIndex index) input inside) :
    HEq (attached.stateDirect stage retained index input inside queried).owner queried.2.2.1.val.owner :=
  attached.stateQuery_owner_heq index input inside queried.2.2.1.val

end Incidence

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.LocalMember

end
