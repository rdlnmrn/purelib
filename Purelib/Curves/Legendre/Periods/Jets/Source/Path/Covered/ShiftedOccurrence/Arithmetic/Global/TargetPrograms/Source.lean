module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms.Source.Attachment
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet
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

/-! # Source attachment for the same retained shifted target programmes

The original target programme preparations determine an actual attempt
family on the identical covered spine. A genuine original Completed value for each of
those exact attempts retains its original endpoint acquisitions and Stage.
The six already certified target programmes then consume those literal
source lists directly. No alternative programme or period name is built.

All-stage Completion remains geometric input: preparation alone proves
neither readiness nor coherent first-match roots at repeated signed visits.
A different physical spine additionally needs its own signed refinement
comparison; no such identification is inferred here.
-/

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
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

namespace ValueBlocks

/-- Construct the original synchronized jet from those same target programmes and their actual source attachment. -/
def sourceJet
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next))
    (completed : next.requested.request.attempt.CompletedFamily) :
    SynchronizedPeriodJet target :=
  SynchronizedPeriodJet.ofSource (constantCycle next.requested.request.chain)
    (retained.sourceValue (next := next)) (retained.sourceFirst (next := next))
    (retained.sourceSecond (next := next)) (retained.sourceAttachment (next := next) completed)

/-- The new source jet retains the identical incoming target lifted cycle at every stage. -/
theorem sourceJet_cycle
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next))
    (completed : next.requested.request.attempt.CompletedFamily) :
    (retained.sourceJet (next := next) completed).cycle = constantCycle next.requested.request.chain := by rfl

/-- The next source value row is the whole same original incoming target integral programme. -/
theorem sourceJet_value_integral
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next))
    (completed : next.requested.request.attempt.CompletedFamily) (coordinate : Fin 2) :
    (((retained.sourceJet (next := next) completed).value coordinate).integral) =
      retained.targetProgram (next := next) (Specification.Table.valueIndex coordinate) := by
  exact retained.sourceValue_integral (next := next) coordinate

/-- The next source first row is the whole same original incoming first target integral programme. -/
theorem sourceJet_first_integral
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next))
    (completed : next.requested.request.attempt.CompletedFamily) (coordinate : Fin 2) :
    (((retained.sourceJet (next := next) completed).first coordinate).integral) =
      retained.targetProgram (next := next) (Specification.Table.firstIndex coordinate) := by
  exact retained.sourceFirst_integral (next := next) coordinate

/-- The next source second row is the whole same original incoming second target integral programme. -/
theorem sourceJet_second_integral
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next))
    (completed : next.requested.request.attempt.CompletedFamily) (coordinate : Fin 2) :
    (((retained.sourceJet (next := next) completed).second coordinate).integral) =
      retained.targetProgram (next := next) (Specification.Table.secondIndex coordinate) := by
  exact retained.sourceSecond_integral (next := next) coordinate

/-- Derive original connection and residual certificates on the same attached incoming target programmes.

The original synchronized jet is retained once before both original ofJet
operations. Each relation is paid by the actual attached source Stages,
Commons and primitive endpoint admissions, never by a desired Euler defect,
endpoint agreement, derivative realization or final sample bound input.
-/
def sourceRelations
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next))
    (completed : next.requested.request.attempt.CompletedFamily) :
    (actual : SynchronizedPeriodJet target) ×
      Connection.ConnectionCertificate actual × PicardFuchs.PicardFuchsCertificate actual :=
  let actual := retained.sourceJet (next := next) completed
  let connection := Connection.ConnectionCertificate.ofJet actual
  let residual := PicardFuchs.PicardFuchsCertificate.ofJet actual
  ⟨actual, connection, residual⟩

/-- The relation factory retains the same original source-attached incoming target jet. -/
theorem sourceRelations_jet
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next))
    (completed : next.requested.request.attempt.CompletedFamily) :
    (retained.sourceRelations (next := next) completed).1 = retained.sourceJet (next := next) completed := by rfl

end ValueBlocks

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
