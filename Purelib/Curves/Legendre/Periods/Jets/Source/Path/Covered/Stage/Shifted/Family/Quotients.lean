module

import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedGeometry.Between.Reference.Requested
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet.Occurrences
import Purelib.Curves.Legendre.Periods.Jets.Basic
import Purelib.Curves.Legendre.Periods.Jets.Connection
import Purelib.Curves.Legendre.Periods.Jets.PicardFuchs
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Regular

/-! # Actual local reference jets and their four internally derived quotients

One original source Request, root chain and geometric allocation determine
both retained offset members. Their positional six-channel jets are fixed
before the fresh comparison requests. One original four-row constructor
then supplies all-later derivative estimates with its complete row bank.
-/

public section

universe u

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {reference : AccuracyRequest}

/-- The two actual local members and the original four-row comparison continuation.

Both generated Frame owners, complete shifted members, six-channel
completion families and jets are retained. The final continuation receives
the original fresh Requests, Positions, Alignments, row bank and Integral,
followed by their internally proved all-later quotient bounds.
-/
abbrev LocalQuotientConsumer (source : Requested covered chain current floor rootStage reference)
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    {root : Named} (roots : RootChain (parent :: parents) root root)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)
    (firstOffset lastOffset : Canonical)
    (firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound)
    (lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound)
    (firstStart lastStart freshStart : Nat)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1)
    (nonzero : lastOffset - firstOffset ≠ 0) (spatial : AccuracyRequest) (Result : Type u) : Type _ :=
  (firstFrame : Paths.Frame (parameter + firstOffset)) →
  firstFrame = ranges.targetFrame firstOffset (firstAdmitted.trans allocation.bound_le_regularBound) →
  (firstMember : Shifted (parameter := parameter) (increment := firstOffset) (frame := frame)
    (basis := basis) (target := firstFrame) (count := count) (parent := parent) (parents := parents)
    (covered := covered) (chain := chain) (current := current) (floor := floor)
    (rootStage := rootStage) (accuracy := reference) source ranges allocation firstAdmitted widths roots
    targetCurrent targetFloor targetRootStage) →
  (firstCompleted : firstMember.requested.request.attempt.OccurrenceFamily) →
  (firstActual : (jet : SynchronizedPeriodJet firstFrame) ×
    Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet) →
  firstActual.1 = OccurrenceCompletion.jet (parameter := parameter + firstOffset) (frame := firstFrame)
    (basis := basis) (count := count) (floor := targetFloor) (rootStage := targetRootStage)
    firstMember.requested.request.covered firstMember.requested.request.chain
    (fun stage => (firstCompleted stage).val) →
  (lastFrame : Paths.Frame (parameter + lastOffset)) →
  lastFrame = ranges.targetFrame lastOffset (lastAdmitted.trans allocation.bound_le_regularBound) →
  (lastMember : Shifted (parameter := parameter) (increment := lastOffset) (frame := frame)
    (basis := basis) (target := lastFrame) (count := count) (parent := parent) (parents := parents)
    (covered := covered) (chain := chain) (current := current) (floor := floor)
    (rootStage := rootStage) (accuracy := reference) source ranges allocation lastAdmitted widths roots
    targetCurrent targetFloor targetRootStage) →
  (lastCompleted : lastMember.requested.request.attempt.OccurrenceFamily) →
  (lastActual : (jet : SynchronizedPeriodJet lastFrame) ×
    Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet) →
  lastActual.1 = OccurrenceCompletion.jet (parameter := parameter + lastOffset) (frame := lastFrame)
    (basis := basis) (count := count) (floor := targetFloor) (rootStage := targetRootStage)
    lastMember.requested.request.covered lastMember.requested.request.chain
    (fun stage => (lastCompleted stage).val) →
  ShiftedGeometry.BetweenRows.ReferenceConsumer source.prepared ranges allocation
    firstAdmitted lastAdmitted widths widths firstMember.blocks lastMember.blocks
    firstMember.requested lastMember.requested firstActual.1 lastActual.1
    firstStart lastStart freshStart unit nonzero spatial Result

namespace LocalMember

/-- Derive four reference quotients from two already retained members without reacquiring either vertex.

The same stored blocks, Requests, completion families and jets feed one
fresh comparison/row constructor. Adjacent parameter edges may therefore
share their actual cached member and select their sample floors later.
The callback's bounds are indexed by those same given jets.
-/
def withQuotients {source : Requested covered chain current floor rootStage reference}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    {firstOffset lastOffset : Canonical}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound}
    (first : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage firstOffset firstAdmitted)
    (last : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage lastOffset lastAdmitted)
    (firstStart lastStart freshStart : Nat)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1)
    (nonzero : lastOffset - firstOffset ≠ 0) (spatial : AccuracyRequest)
    {Result : Type u}
    (consume : ShiftedGeometry.BetweenRows.ReferenceConsumer source.prepared ranges allocation
      firstAdmitted lastAdmitted widths widths first.member.blocks last.member.blocks
      first.member.requested last.member.requested first.jet last.jet
      firstStart lastStart freshStart unit nonzero spatial Result) : Result :=
  ShiftedGeometry.BetweenRows.withReferenceQuotients
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (remaining := parents) (covered := covered)
    (firstFrame := first.targetFrame) (lastFrame := last.targetFrame)
    (oldGeometry := chain) (oldRoots := roots)
    source.prepared ranges allocation firstAdmitted lastAdmitted widths widths
    first.member.blocks last.member.blocks first.member.geometry_eq last.member.geometry_eq
    first.member.requested last.member.requested first.completed last.completed
    first.jet last.jet first.jet_eq last.jet_eq firstStart lastStart freshStart unit nonzero spatial consume

/-- The actual two reference floors with the four all-later bounds on the same retained member pair. -/
@[expose] def QuotientFloors {source : Requested covered chain current floor rootStage reference}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    {firstOffset lastOffset : Canonical}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound}
    (first : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage firstOffset firstAdmitted)
    (last : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage lastOffset lastAdmitted) :=
  {floors : Nat × Nat // ShiftedGeometry.BetweenRows.QuotientBounds covered first.jet last.jet floors.1 floors.2}

/-- Derive the exact finite reference-floor view from one original four-row construction.

The original member pair remains fixed. Its comparison banks compute the
two floors, and the retained row construction proves all four bounds.
Consumers needing the complete intermediate banks use withQuotients.
-/
def quotientFloors {source : Requested covered chain current floor rootStage reference}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    {firstOffset lastOffset : Canonical}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound}
    (first : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage firstOffset firstAdmitted)
    (last : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage lastOffset lastAdmitted)
    (firstStart lastStart freshStart : Nat)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1)
    (nonzero : lastOffset - firstOffset ≠ 0) (spatial : AccuracyRequest) : QuotientFloors first last :=
  withQuotients first last firstStart lastStart freshStart unit nonzero spatial
    (fun firstBank lastBank _firstFresh _lastFresh _firstPaid _lastPaid
      _firstPositions _lastPositions _firstAligned _lastAligned _rows _actual bounded =>
      ⟨(ShiftedGeometry.Request.Comparisons.leftFloor firstBank,
        ShiftedGeometry.Request.Comparisons.leftFloor lastBank), bounded⟩)

end LocalMember

/-- Construct both genuine offset members before deriving their four all-later parameter quotients.

The fixed source Request and root chain precede the offsets. Each member
is acquired once at the source's original reference accuracy and supplies
one positional six-channel jet. Their retained whole-geometry and jet
factory equations feed one shared comparison/row constructor. No final
quotient, connection or residual inequality is an input.
-/
def withLocalQuotients (source : Requested covered chain current floor rootStage reference)
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    {root : Named} (roots : RootChain (parent :: parents) root root)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)
    (firstOffset lastOffset : Canonical)
    (firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound)
    (lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound)
    (firstStart lastStart freshStart : Nat)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1)
    (nonzero : lastOffset - firstOffset ≠ 0) (spatial : AccuracyRequest)
    {Result : Type u}
    (consume : LocalQuotientConsumer source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage firstOffset lastOffset firstAdmitted lastAdmitted
      firstStart lastStart freshStart unit nonzero spatial Result) : Result :=
  let first := LocalMember.build source ranges allocation roots widths
    targetCurrent targetFloor targetRootStage firstOffset firstAdmitted
  let last := LocalMember.build source ranges allocation roots widths
    targetCurrent targetFloor targetRootStage lastOffset lastAdmitted
  LocalMember.withQuotients first last firstStart lastStart freshStart unit nonzero spatial
    (consume first.targetFrame first.targetFrame_eq first.member first.completed first.actual first.jet_eq
      last.targetFrame last.targetFrame_eq last.member last.completed last.actual last.jet_eq)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

end
