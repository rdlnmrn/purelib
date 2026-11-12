module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet.Occurrences
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Comparison
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Geometry.Path.Gaussian.Lifted.Closed
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain

/-! # The actual joined cycle and six original model lists of one retained local member

Only the original nonempty-list and base-point transports are eliminated.
The stored member, joined geometry, Request, completion family and jet stay
unchanged. Every finite stage reads that same closed lifted representative
and its same completed Stage; all six uniform certificates are transported
from the original jet's actual model lists.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Jets (UniformPathCertificates)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Geometry.Path.Gaussian.Lifted.Closed (ClosedLiftedPath)
open Purelib.Geometry.Path.Gaussian.Lifted.Refinement (LiftedCycleRefinement)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

/-- Reindexing one free original closed chain preserves its complete displayed closed path at each stage. -/
private theorem cycle_reindexed {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {kept : List (CenteredEdge (Fibre.frameCurve frame) basis)} {point : LiftedPoint 2}
    (chain : CenteredPathChain kept (start := point) (finish := point))
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} (same : kept = parent :: parents) (index : Nat) :
    (constantCycle (parameter := parameter) (frame := frame) (basis := basis)
      (chain.castParents same).basedAtFirst).liftedPath index =
      (constantCycle (parameter := parameter) (frame := frame) (basis := basis) chain).liftedPath index := by
  cases same
  cases chain
  rfl

/-- The retained Request's head view preserves the entire independently retained joined closed representative. -/
private theorem request_cycle_at {parameter increment : Canonical} {target : Paths.Frame (parameter + increment)}
    {basis : Differential 1} {count : Nat} {point : LiftedPoint 2} {root : Named}
    {geometry : ShiftedGeometry (target := target) (basis := basis) (count := count) point point root root}
    {index floor rootStage : Nat} (request : ShiftedGeometry.Request geometry index floor rootStage) (stage : Nat) :
    (constantCycle (parameter := parameter + increment) (frame := target) (basis := basis)
      request.chain).liftedPath stage =
      (constantCycle (parameter := parameter + increment) (frame := target) (basis := basis)
        geometry.chain).liftedPath stage := by
  have retained := congrArg (fun chain : CenteredPathChain (request.shape.val.1 :: request.shape.val.2)
    (start := startPoint request.shape.val.1) (finish := startPoint request.shape.val.1) =>
      (constantCycle (parameter := parameter + increment) (frame := target) (basis := basis)
        chain).liftedPath stage) request.chain_eq
  exact retained.trans (cycle_reindexed (parameter := parameter + increment) (frame := target) (basis := basis)
    geometry.chain request.shape.property stage)

namespace ShiftedGeometry

/-- Derive the signed handoff between two actual endpoint Steps from their original source occurrences.

Both Steps may be at any common absolute offset, including a rational
section of the original strip. The same original geometric incidence and
closed-chain root link identify their source samples before the existing
Step transport compares their unchanged target Owners.
-/
def adjacentSteps {parameter offset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {left right : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)} {start finish : LiftedPoint 2}
    (chain : CenteredPathChain (left :: right :: remaining) (start := start) (finish := finish))
    {first last : Named} (roots : RootChain (left :: right :: remaining) first last)
    {leftPatch : PreparedPatch left} {rightPatch : PreparedPatch right} {count floor : Nat}
    {leftInside : (leftPatch.neighborhood count).box.Contains (left.edge.point 1)}
    {rightInside : (rightPatch.neighborhood count).box.Contains (right.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {path : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets path stage}
    (leftSource : PreparedParent leftPatch count floor leftInside targets)
    (rightSource : PreparedParent rightPatch count floor rightInside targets)
    (leftStep : Variation.Point.Step leftSource.lastSample offset)
    (rightStep : Variation.Point.Step rightSource.firstSample offset) :
    NamedEquivalent leftStep.root.value.name rightStep.root.value.name :=
  leftStep.equivalent_of_source_eq rightStep
    (congrArg (fun point : LiftedPoint 2 => point.coordinate) chain.remaining.start_eq.symm)
    (leftSource.lastQueryEquivalent.symm.trans (roots.nextEquivalent.trans rightSource.firstQueryEquivalent))

/-- Derive the actual final-to-first Step return from the same original closed root chain and geometric endpoints.

The prefix equality retains the literal final occurrence, including repeated
or stationary parents. Only the original chain is reindexed; the supplied
endpoint samples, absolute Steps and their root Owners stay unchanged.
-/
def returningSteps {parameter offset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {head final : CenteredEdge (Fibre.frameCurve frame) basis}
    {tail before : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (chain : CenteredPathChain (head :: tail) (start := startPoint head) (finish := startPoint head))
    (same : head :: tail = before ++ [final]) {root : Named} (roots : RootChain (head :: tail) root root)
    {firstPatch : PreparedPatch head} {finalPatch : PreparedPatch final} {count floor : Nat}
    {firstInside : (firstPatch.neighborhood count).box.Contains (head.edge.point 1)}
    {finalInside : (finalPatch.neighborhood count).box.Contains (final.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {path : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets path stage}
    (firstSource : PreparedParent firstPatch count floor firstInside targets)
    (finalSource : PreparedParent finalPatch count floor finalInside targets)
    (finalStep : Variation.Point.Step finalSource.lastSample offset)
    (firstStep : Variation.Point.Step firstSource.firstSample offset) :
    NamedEquivalent finalStep.root.value.name firstStep.root.value.name :=
  let lastRoots := Riemann.Topology.PreparedBankRootChains.RootChain.castChildren same roots
  let closing := RootChain.lastEquivalent before lastRoots
  finalStep.equivalent_of_source_eq firstStep
    (congrArg (fun point : LiftedPoint 2 => point.coordinate)
      (CenteredPathChain.last_eq before (chain.castParents same)))
    (finalSource.lastQueryEquivalent.symm.trans
      (closing.trans (roots.firstEquivalent.trans firstSource.firstQueryEquivalent)))

/-- Compare supplied Steps at consecutive original occurrences, including the literal closing occurrence.

The prepared sources, closed geometric chain and original root chain stay
abstract. Their actual endpoint comparisons and incidence derive the signed
source relation before the existing Step comparison consumes both retained
Steps. No source, Step, observation or desired target relation is constructed.
-/
def followingSteps {parameter offset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} {count floor : Nat}
    {covered : CoveredParents count (parent :: parents)}
    {baseStart baseFinish : LiftedPoint 2} {path : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets path stage} (prepared : PreparedParents covered floor targets)
    (chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent))
    {root : Named} (roots : RootChain (parent :: parents) root root)
    (index : Fin (parent :: parents).length)
    (left : Variation.Point.Step (prepared.entry index).lastSample offset)
    (right : Variation.Point.Step
      (prepared.entry (StageAttempt.followingIndex parent parents index)).firstSample offset) :
    NamedEquivalent left.root.value.name right.root.value.name :=
  let next := StageAttempt.followingIndex parent parents index
  let lastNames := PreparedParent.lastQueryEquivalent (parameter := parameter) (frame := frame) (basis := basis)
    (parent := (parent :: parents)[index.val]'index.isLt) (patch := (covered.entry index).val)
    (count := count) (floor := floor) (covered := (covered.entry index).property)
    (original := path) (stage := stage) (targets := targets) (prepared.entry index)
  let firstNames := PreparedParent.firstQueryEquivalent (parameter := parameter) (frame := frame) (basis := basis)
    (parent := (parent :: parents)[next.val]'next.isLt) (patch := (covered.entry next).val)
    (count := count) (floor := floor) (covered := (covered.entry next).property)
    (original := path) (stage := stage) (targets := targets) (prepared.entry next)
  let sourceNames : NamedEquivalent (prepared.entry index).lastSample.certificate.value.name
      (prepared.entry next).firstSample.certificate.value.name :=
    lastNames.symm.trans ((StageAttempt.followingEquivalent roots index).trans firstNames)
  Variation.Point.Step.equivalent_of_source_eq (parameter := parameter) (increment := offset)
    (firstCount := count) (lastCount := count)
    (firstPatch := (covered.entry index).val.neighborhood count)
    (lastPatch := (covered.entry next).val.neighborhood count)
    (firstSource := (prepared.entry index).lastSample) (lastSource := (prepared.entry next).firstSample)
    left right
    (congrArg (fun point : LiftedPoint 2 => point.coordinate) (StageAttempt.following_point chain index).symm)
    sourceNames

end ShiftedGeometry

namespace StageAttempt.Requested.LocalMember

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
    {targetCurrent targetFloor targetRootStage : Nat} {offset : Canonical}
    {admitted : Norm.Basic.normSq offset ≤ allocation.bound}
    (cached : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage offset admitted)

/-- Every stage of the actual jet displays the same whole joined closed path, including its original base point.

The full jet factory is consumed first. The Request's original parent-list
and first-point transports then identify the complete closed representative;
no Frame equality or reconstructed acquisition is used.
-/
theorem cycle_at (stage : Nat) : cached.jet.cycle.liftedPath stage =
    (constantCycle (parameter := parameter + offset) (frame := cached.targetFrame) (basis := basis)
      cached.member.geometry.chain).liftedPath stage := by
  have retained := congrArg (fun jet : SynchronizedPeriodJet cached.targetFrame => jet.cycle) cached.jet_eq
  have original := OccurrenceCompletion.jet_cycle (parameter := parameter + offset) (frame := cached.targetFrame)
    (basis := basis) (count := count) (floor := targetFloor) (rootStage := targetRootStage)
    cached.member.requested.request.covered cached.member.requested.request.chain
    (fun index => (cached.completed index).val)
  exact (congrArg (fun cycle : LiftedCycleRefinement 2 => cycle.liftedPath stage)
    (retained.trans original)).trans (request_cycle_at (parameter := parameter) (increment := offset)
      (target := cached.targetFrame)
      (basis := basis) (count := count) cached.member.requested.request stage)

/-- The actual member jet retains the same whole completed Stage at every original finite stage. -/
theorem stage_heq (stage : Nat) :
    HEq (cached.jet.source.stages stage) (cached.completed stage).val.2.stage := by
  have original := OccurrenceCompletion.jet_stages (parameter := parameter + offset) (frame := cached.targetFrame)
    (basis := basis) (count := count) (floor := targetFloor) (rootStage := targetRootStage)
    cached.member.requested.request.covered cached.member.requested.request.chain
    (fun index => (cached.completed index).val) stage
  exact Eq.rec (motive := fun (jet : SynchronizedPeriodJet cached.targetFrame) _ =>
    HEq (jet.source.stages stage) (cached.completed stage).val.2.stage) original cached.jet_eq.symm

/-- Both actual value model lists uniformly certify the same retained joined path. -/
def valueCertificates (coordinate : Fin 2) (stage : Nat) :
    UniformPathCertificates (Fibre.frameCurve cached.targetFrame)
      (Specification.valueSpecification (parameter + offset) coordinate)
      (((cached.jet.value coordinate).integral.model stage).cells) cached.member.geometry.chain.path :=
  Eq.mp (congrArg (fun path : ClosedLiftedPath 2 =>
    UniformPathCertificates (Fibre.frameCurve cached.targetFrame)
      (Specification.valueSpecification (parameter + offset) coordinate)
      (((cached.jet.value coordinate).integral.model stage).cells) path.path) (cached.cycle_at stage))
    ((cached.jet.value coordinate).certificates stage)

/-- Both actual first-channel model lists uniformly certify that same retained joined path. -/
def firstCertificates (coordinate : Fin 2) (stage : Nat) :
    UniformPathCertificates (Fibre.frameCurve cached.targetFrame)
      (Specification.firstDerivativeSpecification (parameter + offset) coordinate)
      (((cached.jet.first coordinate).integral.model stage).cells) cached.member.geometry.chain.path :=
  Eq.mp (congrArg (fun path : ClosedLiftedPath 2 =>
    UniformPathCertificates (Fibre.frameCurve cached.targetFrame)
      (Specification.firstDerivativeSpecification (parameter + offset) coordinate)
      (((cached.jet.first coordinate).integral.model stage).cells) path.path) (cached.cycle_at stage))
    ((cached.jet.first coordinate).certificates stage)

/-- Both actual second-channel model lists uniformly certify that same retained joined path. -/
def secondCertificates (coordinate : Fin 2) (stage : Nat) :
    UniformPathCertificates (Fibre.frameCurve cached.targetFrame)
      (Specification.secondDerivativeSpecification (parameter + offset) coordinate)
      (((cached.jet.second coordinate).integral.model stage).cells) cached.member.geometry.chain.path :=
  Eq.mp (congrArg (fun path : ClosedLiftedPath 2 =>
    UniformPathCertificates (Fibre.frameCurve cached.targetFrame)
      (Specification.secondDerivativeSpecification (parameter + offset) coordinate)
      (((cached.jet.second coordinate).integral.model stage).cells) path.path) (cached.cycle_at stage))
    ((cached.jet.second coordinate).certificates stage)

end StageAttempt.Requested.LocalMember

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
