module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Increment
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms.Comparison

/-! # Whole programme-cache views at an exactly equal increment and frame

The original shifted request and its ValueBlocks move only by equality
elimination. All six original RefinementPrograms stay whole equal values;
no new models, samples, restrictions or integral certificates are built.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

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
    {source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest firstIncrement firstNonzero))}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {firstAdmitted : Norm.Basic.normSq firstIncrement ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastIncrement ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {next : StageAttempt.Requested.Shifted (target := firstTarget) source ranges allocation firstAdmitted widths roots
      targetCurrent targetFloor targetRootStage}

namespace ValueBlocks

/-- The exact original ValueBlocks family on the same increment/frame-transported shifted tuple. -/
@[expose] def AtIncrement (_retained : ValueBlocks (next := next))
    (equal : firstIncrement = lastIncrement)
    (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget) : Type _ :=
  ValueBlocks (spatial := spatial) (nonzero := lastNonzero)
    (next := next.castIncrement (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted) equal frameEqual)

variable (retained : ValueBlocks (next := next))

/-- Carry the same complete original four-row block cache along exact increment and whole-frame equality.

The operation is equality elimination on the actual ValueBlocks. All
positions, Alignments, restriction banks, Sample callbacks and original
integral certificates remain the retained input values.
-/
@[expose] def castIncrement (equal : firstIncrement = lastIncrement)
    (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget) :
    AtIncrement (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted) retained equal frameEqual := by
  cases equal
  change firstTarget = lastTarget at frameEqual
  cases frameEqual
  exact retained

/-- Exact endpoint transport preserves the whole original block product and every retained factory equation. -/
theorem castIncrement_heq (equal : firstIncrement = lastIncrement)
    (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget) :
    HEq (retained.castIncrement (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted) equal frameEqual)
      retained := by
  cases equal
  change firstTarget = lastTarget at frameEqual
  cases frameEqual
  rfl

/-- Every whole original target programme is unchanged by the exact endpoint cache view.

This retains all stages, allowances, tail comparisons and sample-center
bounds. It does not use withModels or replace approximate Euler readings
by synthetic polynomial cells.
-/
theorem castIncrement_targetProgram (equal : firstIncrement = lastIncrement)
    (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget)
    (channel : Fin 6) :
    ((retained.castIncrement (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
      equal frameEqual).targetProgram channel) = retained.targetProgram channel := by
  cases equal
  change firstTarget = lastTarget at frameEqual
  cases frameEqual
  rfl

end ValueBlocks

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
