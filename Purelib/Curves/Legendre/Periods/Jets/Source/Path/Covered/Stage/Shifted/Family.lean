module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Occurrences
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet.Occurrences
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Regular

/-! # Actual offset members on one fixed covered source spine

The original source request and its complete preparation factory precede
all offsets and derivative requests. Each member keeps the actual generated
Frame, shifted blocks, whole closed geometry and target request. Its same
positional family supplies every channel of one retained jet. No target
Frame is identified with a separately reconstructed canonical Frame.
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

/-- Retain one actual offset member and its single six-channel positional jet on the fixed source request.

The source accuracy is fixed independently of any derivative tolerance.
Zero offsets are allowed, but the returned generated Frame is retained as
its actual owner; it is not asserted to equal the original source Frame.
The complete old and new checking outcomes remain in the supplied source
and retained shifted Request. Independent calls are independent work.
-/
def withLocalMember (source : Requested covered chain current floor rootStage reference)
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    {root : Named} (roots : RootChain (parent :: parents) root root)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)
    (offset : Canonical) (admitted : Norm.Basic.normSq offset ≤ allocation.bound)
    {Result : Type u}
    (consume :
      (target : Paths.Frame (parameter + offset)) →
      target = ranges.targetFrame offset (admitted.trans allocation.bound_le_regularBound) →
      (member : Shifted (parameter := parameter) (increment := offset) (frame := frame)
        (basis := basis) (target := target) (count := count) (parent := parent) (parents := parents)
        (covered := covered) (chain := chain) (current := current) (floor := floor)
        (rootStage := rootStage) (accuracy := reference) source ranges allocation admitted widths roots
        targetCurrent targetFloor targetRootStage) →
      (completed : member.requested.request.attempt.OccurrenceFamily) →
      (actual : (jet : SynchronizedPeriodJet target) ×
        Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet) →
      actual.1 = OccurrenceCompletion.jet (parameter := parameter + offset) (frame := target)
        (basis := basis) (count := count) (floor := targetFloor) (rootStage := targetRootStage)
        member.requested.request.covered member.requested.request.chain
        (fun stage => (completed stage).val) → Result) : Result :=
  let target := ranges.targetFrame offset (admitted.trans allocation.bound_le_regularBound)
  let member := source.shifted (parameter := parameter) (increment := offset) (frame := frame)
    (basis := basis) (target := target) (count := count) (parent := parent) (parents := parents)
    (covered := covered) (chain := chain) (current := current) (floor := floor)
    (rootStage := rootStage) (accuracy := reference) ranges allocation admitted widths roots
    targetCurrent targetFloor targetRootStage
  let completed := ShiftedGeometry.Request.occurrenceFamily (parameter := parameter) (increment := offset)
    (target := target) (basis := basis) (count := count) (geometry := member.geometry)
    (index := member.requested.selected.stage) (floor := targetFloor) (rootStage := targetRootStage)
    member.requested.request
  let actual := OccurrenceCompletion.build (parameter := parameter + offset) (frame := target)
    (basis := basis) (count := count) (floor := targetFloor) (rootStage := targetRootStage)
    member.requested.request.covered member.requested.request.chain (fun stage => (completed stage).val)
  consume target rfl member completed actual
    (OccurrenceCompletion.build_jet (parameter := parameter + offset) (frame := target)
      (basis := basis) (count := count) (floor := targetFloor) (rootStage := targetRootStage)
      member.requested.request.covered member.requested.request.chain (fun stage => (completed stage).val))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

end
