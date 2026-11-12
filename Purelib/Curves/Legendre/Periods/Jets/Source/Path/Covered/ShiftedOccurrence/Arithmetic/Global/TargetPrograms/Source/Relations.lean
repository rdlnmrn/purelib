module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms.Source
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip.Increment
import Purelib.Curves.Legendre.Periods.Jets.Source.Attachment
import Purelib.Curves.Legendre.Periods.Jets.Basic
import Purelib.Curves.Legendre.Periods.Jets.Connection
import Purelib.Curves.Legendre.Periods.Jets.PicardFuchs
import Purelib.Curves.Legendre.Periods.Jets.Specification
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Fin.Two

/-! # Retained source relation bundles and their original programme readbacks -/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Curves.Legendre.Periods.Jets.Source (Attachment)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : Riemann.Topology.PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}

namespace ValueBlocks

variable (retained : ValueBlocks (next := next))

/-- The retained original relation factory on one programme cache and completed family.

The subtype stores the complete jet and both certificates together with
its whole factory equation. No programme or completion is rebuilt.
-/
@[expose] def SourceRelations
    (completed : next.requested.request.attempt.CompletedFamily) :=
  { value : (actual : SynchronizedPeriodJet target) ×
      Connection.ConnectionCertificate actual × PicardFuchs.PicardFuchsCertificate actual //
    value = retained.sourceRelations (next := next) completed }

/-- Run the original relation factory once on the supplied retained programmes and family. -/
def retainSourceRelations
    (completed : next.requested.request.attempt.CompletedFamily) :
    retained.SourceRelations (next := next) completed :=
  let actual := retained.sourceRelations (next := next) completed
  ⟨actual, rfl⟩

/-- The retained bundle is the original single factory execution, including its whole subtype value. -/
theorem retainSourceRelations_factory
    (completed : next.requested.request.attempt.CompletedFamily) :
    retained.retainSourceRelations (next := next) completed =
      (let actual := retained.sourceRelations (next := next) completed
       ⟨actual, rfl⟩) := (rfl)

namespace SourceRelations

variable {retained} {completed : next.requested.request.attempt.CompletedFamily}
    (relations : retained.SourceRelations (next := next) completed)

/-- Read the original jet from the retained relation bundle. -/
@[expose, macro_inline] def jet : SynchronizedPeriodJet target := relations.val.1

/-- Read the original connection certificate on that same jet. -/
@[expose, macro_inline] def connection : Connection.ConnectionCertificate relations.jet := relations.val.2.1

/-- Read the original scalar residual certificate on that same jet. -/
@[expose, macro_inline] def residual : PicardFuchs.PicardFuchsCertificate relations.jet := relations.val.2.2

/-- The whole bundle is the original factory on the supplied caches. -/
theorem factory_eq : relations.val = retained.sourceRelations (next := next) completed := relations.property

/-- The retained jet is the original source-attached jet of the same programmes and family. -/
theorem jet_eq : relations.jet = retained.sourceJet (next := next) completed :=
  (congrArg (fun bundle => bundle.1) relations.factory_eq).trans
    (retained.sourceRelations_jet (next := next) completed)

/-- The retained jet uses the original target cycle. -/
theorem cycle_eq : relations.jet.cycle = constantCycle next.requested.request.chain :=
  (congrArg (fun actual : SynchronizedPeriodJet target => actual.cycle) relations.jet_eq).trans
    (retained.sourceJet_cycle (next := next) completed)

/-- Each value row is the whole original target programme. -/
theorem value_integral (coordinate : Fin 2) : (relations.jet.value coordinate).integral =
    retained.targetProgram (next := next) (Specification.Table.valueIndex coordinate) :=
  (congrArg (fun actual : SynchronizedPeriodJet target => (actual.value coordinate).integral)
    relations.jet_eq).trans (retained.sourceJet_value_integral (next := next) completed coordinate)

/-- Each first derivative row is the whole original target programme. -/
theorem first_integral (coordinate : Fin 2) : (relations.jet.first coordinate).integral =
    retained.targetProgram (next := next) (Specification.Table.firstIndex coordinate) :=
  (congrArg (fun actual : SynchronizedPeriodJet target => (actual.first coordinate).integral)
    relations.jet_eq).trans (retained.sourceJet_first_integral (next := next) completed coordinate)

/-- Each second derivative row is the whole original target programme. -/
theorem second_integral (coordinate : Fin 2) : (relations.jet.second coordinate).integral =
    retained.targetProgram (next := next) (Specification.Table.secondIndex coordinate) :=
  (congrArg (fun actual : SynchronizedPeriodJet target => (actual.second coordinate).integral)
    relations.jet_eq).trans (retained.sourceJet_second_integral (next := next) completed coordinate)

end SourceRelations

end ValueBlocks

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
