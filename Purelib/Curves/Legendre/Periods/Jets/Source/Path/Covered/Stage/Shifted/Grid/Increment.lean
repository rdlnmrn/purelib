module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Increment
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy.Following
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms.Increment
import Purelib.Riemann.Topology.PreparedBankRootChains

/-! # Joint endpoint transport of the same following-window caches

Exact first-increment and whole first-Frame equality transports the
original ranges/allocation/widths and five-cache following Grid together.
The two original operation values remain functions; no sufficient source,
query, table, completion, trace or acquisition factory runs in this view.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Riemann.Topology

variable {parameter firstIncrement lastIncrement : Canonical}
    {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {firstTarget : Paths.Frame (parameter + firstIncrement)}
    {lastTarget : Paths.Frame (parameter + lastIncrement)}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {spatial : AccuracyRequest}
    {firstNonzero : firstIncrement ≠ 0} {lastNonzero : lastIncrement ≠ 0}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest firstIncrement firstNonzero))}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {firstAdmitted : Norm.Basic.normSq firstIncrement ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastIncrement ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : Shifted (target := firstTarget) source ranges allocation firstAdmitted widths roots
      targetCurrent targetFloor targetRootStage)

variable (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent refinement : Nat) (positive : 0 < refinement)
    (nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat)

/-- The exact whole following-window fibre over the SAME increment/frame-transported first endpoint Request.

The nominal first Shifted tuple determines the transported raw Request
and original geometric root chain. Every second-window field is indexed
by that same Request, source Frame and cover; no new node is reconstructed.
-/
@[expose] def FollowingAtIncrement (equal : firstIncrement = lastIncrement)
    (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget) : Type _ :=
  Requested.FollowingGrid.Window
    (endpoint := (retained.castIncrement (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
      equal frameEqual).requested.asSource)
    (roots := PreparedBankRootChains.RootChain.castChildren
      (retained.castIncrement (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
        equal frameEqual).requested.request.shape.property
      (retained.castIncrement (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
        equal frameEqual).geometry.roots)
    nextDirection nextMoving nextSpatial nextCurrent refinement positive
    nextTargetCurrent nextTargetFloor nextTargetRootStage

/-- Transport all original following-window geometry and caches jointly over the first endpoint equality.

The same equality elimination as the original Shifted and ValueBlocks
casts retains the entire dependent window. Its source/query operations are
not invoked, and every stored factory predicate remains part of the cache.
-/
def castFollowingWindow (window : Requested.FollowingGrid.Window
    (endpoint := retained.requested.asSource)
    (roots := PreparedBankRootChains.RootChain.castChildren
      retained.requested.request.shape.property retained.geometry.roots)
    nextDirection nextMoving nextSpatial nextCurrent refinement positive
    nextTargetCurrent nextTargetFloor nextTargetRootStage)
    (equal : firstIncrement = lastIncrement)
    (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget) :
    FollowingAtIncrement (retained := retained) (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
      nextDirection nextMoving nextSpatial nextCurrent refinement positive
      nextTargetCurrent nextTargetFloor nextTargetRootStage equal frameEqual := by
  cases equal
  change firstTarget = lastTarget at frameEqual
  cases frameEqual
  exact window

/-- Joint endpoint transport retains the complete original window value, including all original factory proofs. -/
theorem castFollowingWindow_heq
    {parameter firstIncrement lastIncrement : Canonical}
    {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {firstTarget : Paths.Frame (parameter + firstIncrement)}
    {lastTarget : Paths.Frame (parameter + lastIncrement)}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {spatial : AccuracyRequest}
    {firstNonzero : firstIncrement ≠ 0} {lastNonzero : lastIncrement ≠ 0}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest firstIncrement firstNonzero))}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {firstAdmitted : Norm.Basic.normSq firstIncrement ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastIncrement ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : Shifted (target := firstTarget) source ranges allocation firstAdmitted widths roots
      targetCurrent targetFloor targetRootStage)

(nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent refinement : Nat) (positive : 0 < refinement)
    (nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat)
    (window : Requested.FollowingGrid.Window
    (endpoint := retained.requested.asSource)
    (roots := PreparedBankRootChains.RootChain.castChildren
      retained.requested.request.shape.property retained.geometry.roots)
    nextDirection nextMoving nextSpatial nextCurrent refinement positive
    nextTargetCurrent nextTargetFloor nextTargetRootStage)
    (equal : firstIncrement = lastIncrement)
    (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget) :
    HEq (retained.castFollowingWindow (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
      nextDirection nextMoving nextSpatial nextCurrent refinement positive
      nextTargetCurrent nextTargetFloor nextTargetRootStage window equal frameEqual) window := by
  cases equal
  change firstTarget = lastTarget at frameEqual
  cases frameEqual
  rfl

/-- The whole first programme product, completed-family callback and following-window cache at one endpoint view.

All three fibres use the SAME transported first Shifted Request. Their
original inputs remain available separately; no independently acquired
preparation or replacement polynomial is an input to this exact view.
-/
@[expose] def FollowingCachesAtIncrement (rows : ShiftedGeometry.ValueBlocks (next := retained))
    (equal : firstIncrement = lastIncrement) (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget) : Type _ :=
  ShiftedGeometry.ValueBlocks.AtIncrement
      (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted) rows equal frameEqual ×
    (retained.CompletedFamilyAtIncrement (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
        equal frameEqual ×
      FollowingAtIncrement (retained := retained) (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
      nextDirection nextMoving nextSpatial nextCurrent refinement positive
      nextTargetCurrent nextTargetFloor nextTargetRootStage equal frameEqual)

/-- Jointly transport the actual first rows/family and the entire second-window geometry/cache using original casts.

Exactly the existing ValueBlocks, CompletedFamily and whole-window casts
are applied to retained values. No source member, reprepare callback,
query observation, table, trace or programme factory is executed.
-/
def castFollowingCaches (rows : ShiftedGeometry.ValueBlocks (next := retained))
    (family : retained.requested.request.attempt.CompletedFamily) (window : Requested.FollowingGrid.Window
    (endpoint := retained.requested.asSource)
    (roots := PreparedBankRootChains.RootChain.castChildren
      retained.requested.request.shape.property retained.geometry.roots)
    nextDirection nextMoving nextSpatial nextCurrent refinement positive
    nextTargetCurrent nextTargetFloor nextTargetRootStage)
    (equal : firstIncrement = lastIncrement) (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget) :
    FollowingCachesAtIncrement (retained := retained) (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
      nextDirection nextMoving nextSpatial nextCurrent refinement positive
      nextTargetCurrent nextTargetFloor nextTargetRootStage rows equal frameEqual :=
  ⟨rows.castIncrement (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted) equal frameEqual,
    ⟨retained.castIncrementFamily (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
      equal frameEqual family,
      retained.castFollowingWindow (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
        nextDirection nextMoving nextSpatial nextCurrent refinement positive
        nextTargetCurrent nextTargetFloor nextTargetRootStage window equal frameEqual⟩⟩

/-- The complete joint view uses exactly the three original cached transport operations in their displayed order. -/
private theorem packaged_caches
    {parameter firstIncrement lastIncrement : Canonical}
    {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {firstTarget : Paths.Frame (parameter + firstIncrement)}
    {lastTarget : Paths.Frame (parameter + lastIncrement)}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {spatial : AccuracyRequest}
    {firstNonzero : firstIncrement ≠ 0} {lastNonzero : lastIncrement ≠ 0}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest firstIncrement firstNonzero))}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {firstAdmitted : Norm.Basic.normSq firstIncrement ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastIncrement ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : Shifted (target := firstTarget) source ranges allocation firstAdmitted widths roots
      targetCurrent targetFloor targetRootStage)

(nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent refinement : Nat) (positive : 0 < refinement)
    (nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat)
    (rows : ShiftedGeometry.ValueBlocks (next := retained))
    (family : retained.requested.request.attempt.CompletedFamily) (window : Requested.FollowingGrid.Window
    (endpoint := retained.requested.asSource)
    (roots := PreparedBankRootChains.RootChain.castChildren
      retained.requested.request.shape.property retained.geometry.roots)
    nextDirection nextMoving nextSpatial nextCurrent refinement positive
    nextTargetCurrent nextTargetFloor nextTargetRootStage)
    (equal : firstIncrement = lastIncrement) (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget) :
    retained.castFollowingCaches (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
      nextDirection nextMoving nextSpatial nextCurrent refinement positive
      nextTargetCurrent nextTargetFloor nextTargetRootStage rows family window equal frameEqual =
      ⟨rows.castIncrement (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted) equal frameEqual,
    ⟨retained.castIncrementFamily (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
      equal frameEqual family,
      retained.castFollowingWindow (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
        nextDirection nextMoving nextSpatial nextCurrent refinement positive
        nextTargetCurrent nextTargetFloor nextTargetRootStage window equal frameEqual⟩⟩ := rfl

/-- The complete joint view uses exactly the three original cached transport operations in their displayed order. -/
theorem castFollowingCaches_factory
    {parameter firstIncrement lastIncrement : Canonical}
    {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {firstTarget : Paths.Frame (parameter + firstIncrement)}
    {lastTarget : Paths.Frame (parameter + lastIncrement)}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {spatial : AccuracyRequest}
    {firstNonzero : firstIncrement ≠ 0} {lastNonzero : lastIncrement ≠ 0}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest firstIncrement firstNonzero))}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {firstAdmitted : Norm.Basic.normSq firstIncrement ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastIncrement ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : Shifted (target := firstTarget) source ranges allocation firstAdmitted widths roots
      targetCurrent targetFloor targetRootStage)

(nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent refinement : Nat) (positive : 0 < refinement)
    (nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat)
    (rows : ShiftedGeometry.ValueBlocks (next := retained))
    (family : retained.requested.request.attempt.CompletedFamily) (window : Requested.FollowingGrid.Window
    (endpoint := retained.requested.asSource)
    (roots := PreparedBankRootChains.RootChain.castChildren
      retained.requested.request.shape.property retained.geometry.roots)
    nextDirection nextMoving nextSpatial nextCurrent refinement positive
    nextTargetCurrent nextTargetFloor nextTargetRootStage)
    (equal : firstIncrement = lastIncrement) (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget) :
    retained.castFollowingCaches (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
      nextDirection nextMoving nextSpatial nextCurrent refinement positive
      nextTargetCurrent nextTargetFloor nextTargetRootStage rows family window equal frameEqual =
      ⟨rows.castIncrement (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted) equal frameEqual,
    ⟨retained.castIncrementFamily (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
      equal frameEqual family,
      retained.castFollowingWindow (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
        nextDirection nextMoving nextSpatial nextCurrent refinement positive
        nextTargetCurrent nextTargetFloor nextTargetRootStage window equal frameEqual⟩⟩ :=
  packaged_caches (retained := retained) (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
    nextDirection nextMoving nextSpatial nextCurrent refinement positive
    nextTargetCurrent nextTargetFloor nextTargetRootStage rows family window equal frameEqual

/-- The entire joint endpoint view retains all three original cached input values and factory predicates. -/
theorem castFollowingCaches_heq
    {parameter firstIncrement lastIncrement : Canonical}
    {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {firstTarget : Paths.Frame (parameter + firstIncrement)}
    {lastTarget : Paths.Frame (parameter + lastIncrement)}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {spatial : AccuracyRequest}
    {firstNonzero : firstIncrement ≠ 0} {lastNonzero : lastIncrement ≠ 0}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest firstIncrement firstNonzero))}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {firstAdmitted : Norm.Basic.normSq firstIncrement ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastIncrement ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : Shifted (target := firstTarget) source ranges allocation firstAdmitted widths roots
      targetCurrent targetFloor targetRootStage)

(nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent refinement : Nat) (positive : 0 < refinement)
    (nextTargetCurrent nextTargetFloor nextTargetRootStage : Nat)
    (rows : ShiftedGeometry.ValueBlocks (next := retained))
    (family : retained.requested.request.attempt.CompletedFamily) (window : Requested.FollowingGrid.Window
    (endpoint := retained.requested.asSource)
    (roots := PreparedBankRootChains.RootChain.castChildren
      retained.requested.request.shape.property retained.geometry.roots)
    nextDirection nextMoving nextSpatial nextCurrent refinement positive
    nextTargetCurrent nextTargetFloor nextTargetRootStage)
    (equal : firstIncrement = lastIncrement) (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget) :
    HEq (retained.castFollowingCaches (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
      nextDirection nextMoving nextSpatial nextCurrent refinement positive
      nextTargetCurrent nextTargetFloor nextTargetRootStage rows family window equal frameEqual)
      (rows, (family, window)) := by
  cases equal
  change firstTarget = lastTarget at frameEqual
  cases frameEqual
  have familySame := eq_of_heq (retained.castIncrementFamily_heq
    (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted) rfl rfl family)
  exact heq_of_eq (congrArg (fun original : retained.requested.request.attempt.CompletedFamily =>
    (rows, (original, window))) familySame)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
