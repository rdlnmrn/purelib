module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Transport
public import Purelib.Curves.Legendre.Paths.Frame

/-! # Exact increment and frame views of one retained shifted request

Equality elimination reindexes the original source accuracy and complete
shifted tuple together. Every block, Step, target selection, Request,
preparation and checking cache remains the same original retained value.
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

/-- The original shifted family at an equal increment and target frame, on the same transported source.

Only the exact positive request index changes its display. The source is
the original castAccuracy value, never an independently selected attempt.
-/
@[expose] def AtIncrement (_retained : Shifted (target := firstTarget) source ranges allocation firstAdmitted widths
    roots targetCurrent targetFloor targetRootStage) (equal : firstIncrement = lastIncrement) : Type _ :=
  Shifted (target := lastTarget)
    (source.castAccuracy (last := spatial.minimum (Sampling.incrementRequest lastIncrement lastNonzero))
      (by cases equal; rfl)) ranges allocation lastAdmitted widths roots
      targetCurrent targetFloor targetRootStage

/-- Retain the whole original shifted tuple at its exactly equal increment and complete target-frame owner.

The frame equality concerns the original whole frame, not its coordinate
or labels. Equality elimination executes no source, selection, geometry,
root, checking or programme factory.
-/
@[expose] def castIncrement (equal : firstIncrement = lastIncrement)
    (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget) :
    AtIncrement (lastNonzero := lastNonzero) (lastTarget := lastTarget) (lastAdmitted := lastAdmitted)
      retained equal := by
  cases equal
  change firstTarget = lastTarget at frameEqual
  cases frameEqual
  exact retained

/-- Exact increment/frame transport retains the entire original shifted cache and all whole factory fields. -/
theorem castIncrement_heq (equal : firstIncrement = lastIncrement)
    (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget) :
    HEq (retained.castIncrement (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
      equal frameEqual) retained := by
  cases equal
  change firstTarget = lastTarget at frameEqual
  cases frameEqual
  rfl

/-- The complete original target Requested cache, including its selection and Request, remains retained. -/
theorem castIncrement_requested (equal : firstIncrement = lastIncrement)
    (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget) :
    HEq (retained.castIncrement (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
      equal frameEqual).requested
      retained.requested := by
  cases equal
  change firstTarget = lastTarget at frameEqual
  cases frameEqual
  rfl

/-- The whole original selected target preparation product is unchanged by exact increment/frame transport. -/
theorem castIncrement_prepared (equal : firstIncrement = lastIncrement)
    (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget) :
    HEq (retained.castIncrement (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
      equal frameEqual).requested.prepared
      retained.requested.prepared := by
  cases equal
  change firstTarget = lastTarget at frameEqual
  cases frameEqual
  rfl

/-- The original selected target stage remains the same natural index. -/
theorem castIncrement_stage (equal : firstIncrement = lastIncrement)
    (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget) :
    (retained.castIncrement (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
      equal frameEqual).requested.selected.stage =
      retained.requested.selected.stage := by
  cases equal
  change firstTarget = lastTarget at frameEqual
  cases frameEqual
  rfl

/-- The original completed-family type at the same increment and whole-frame endpoint view.

The named fibre retains the exact cast Request and its attempt. Producers
and joint cache consumers share this type without expanding the selected
Request's cover, shape and chain to compare the same family twice.
-/
@[expose] def CompletedFamilyAtIncrement (equal : firstIncrement = lastIncrement)
    (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget) : Type _ :=
  (retained.castIncrement (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
    equal frameEqual).requested.request.attempt.CompletedFamily

/-- Carry the same original completed family with its retained Request, without invoking any family member. -/
def castIncrementFamily (equal : firstIncrement = lastIncrement)
    (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget)
    (family : retained.requested.request.attempt.CompletedFamily) :
    retained.CompletedFamilyAtIncrement (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
      equal frameEqual := by
  cases equal
  change firstTarget = lastTarget at frameEqual
  cases frameEqual
  exact family

/-- The transported completed-family callback is the entire same original callback, not recomputed stages. -/
theorem castIncrementFamily_heq (equal : firstIncrement = lastIncrement)
    (frameEqual : firstTarget.castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) = lastTarget)
    (family : retained.requested.request.attempt.CompletedFamily) :
    HEq (retained.castIncrementFamily (lastNonzero := lastNonzero) (lastAdmitted := lastAdmitted)
      equal frameEqual family) family := by
  cases equal
  change firstTarget = lastTarget at frameEqual
  cases frameEqual
  rfl

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
