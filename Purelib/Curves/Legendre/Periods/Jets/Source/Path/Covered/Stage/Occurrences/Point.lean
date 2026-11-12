module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain

/-! # Original occurrence completion at the SAME full lifted basepoint

An actual nonempty parent list and its closed centered chain identify the
first-parent lifted point. Equality transports the entire existing attempt/
completion product and its whole execution factory, preserving all given
Targets, preparations, root comparisons, stopping outcomes and Stage
sources together.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.OccurrenceCompletion

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}

/-- The original certified attempt/completion product transported as a whole to its GIVEN full lifted basepoint.

Only the actual parent-list constructor and chain.start_eq select this
exact Type view. It retains the GIVEN root chain, original ofPrepared
attempt factory and whole completeOccurrences outcome/factory; no owner
record, desired source equality or final numerical bound is introduced.
-/
@[expose] def AtPoint {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) {point : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := point) (finish := point))
    (precision floor rootStage : Nat) (targets : CellEndpoints.Targets chain.path precision)
    (computed : targets = CellEndpoints.Targets.build chain.path precision)
    (prepared : PreparedParents covered floor targets)
    {root : Named} (roots : RootChain parents root root) (nonempty : parents ≠ []) : Type 2 := by
  cases parents with
  | nil => exact False.elim (nonempty rfl)
  | cons parent remaining =>
      have same : PreparedParent.startPoint parent = point := chain.start_eq
      cases same
      exact
        (_keptRoots : {value : RootChain (parent :: remaining) root root // value = roots}) ×
        (attempt : {value : StageAttempt covered chain precision floor rootStage //
          value = StageAttempt.ofPrepared covered chain targets computed prepared rootStage}) ×
        {value : (actual : StageAttempt covered chain precision floor rootStage) ×
            {_completed : OccurrenceCompletion actual // actual = attempt.val} //
          value = attempt.val.completeOccurrences _keptRoots.val}

/-- Build the same original first-based attempt and retain its actual root-chain occurrence completion once. -/
private def prepareHead {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (precision floor rootStage : Nat) (targets : CellEndpoints.Targets chain.path precision)
    (computed : targets = CellEndpoints.Targets.build chain.path precision)
    (prepared : PreparedParents covered floor targets) {root : Named}
    (roots : RootChain (parent :: parents) root root) :
    (_keptRoots : {value : RootChain (parent :: parents) root root // value = roots}) ×
    (attempt : {value : StageAttempt covered chain precision floor rootStage //
      value = StageAttempt.ofPrepared covered chain targets computed prepared rootStage}) ×
    {value : (actual : StageAttempt covered chain precision floor rootStage) ×
        {_completed : OccurrenceCompletion actual // actual = attempt.val} //
      value = attempt.val.completeOccurrences _keptRoots.val} :=
  let keptRoots : {value : RootChain (parent :: parents) root root // value = roots} := ⟨roots, rfl⟩
  let original : {value : StageAttempt covered chain precision floor rootStage //
    value = StageAttempt.ofPrepared covered chain targets computed prepared rootStage} :=
    ⟨StageAttempt.ofPrepared covered chain targets computed prepared rootStage, rfl⟩
  let completed : {value : (actual : StageAttempt covered chain precision floor rootStage) ×
      {_completed : OccurrenceCompletion actual // actual = original.val} //
    value = original.val.completeOccurrences keptRoots.val} :=
    ⟨original.val.completeOccurrences keptRoots.val, rfl⟩
  ⟨keptRoots, original, completed⟩

/-- Complete the SAME supplied nonempty covered source bank without retagging its Targets or rebuilding its roots.

The actual list gives the first parent. Its full lifted start equality
transports ALL dependent inputs together before the shared first-based
worker runs. The only new work is the original endpoint-bank/check and
RootBranch occurrence comparisons; source/Point/query/geometry/root
preparation caches remain the supplied actual data.
-/
def ofPrepared {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) {point : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := point) (finish := point))
    (precision floor rootStage : Nat) (targets : CellEndpoints.Targets chain.path precision)
    (computed : targets = CellEndpoints.Targets.build chain.path precision)
    (prepared : PreparedParents covered floor targets) {root : Named}
    (roots : RootChain parents root root) (nonempty : parents ≠ []) :
    AtPoint covered chain precision floor rootStage targets computed prepared roots nonempty := by
  cases parents with
  | nil => exact False.elim (nonempty rfl)
  | cons parent remaining =>
      have same : PreparedParent.startPoint parent = point := chain.start_eq
      cases same
      exact prepareHead covered chain precision floor rootStage targets computed prepared roots

namespace AtPoint

variable {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
variable {covered : CoveredParents count parents} {point : LiftedPoint 2}
variable {chain : CenteredPathChain parents (start := point) (finish := point)}
variable {precision floor rootStage : Nat} {targets : CellEndpoints.Targets chain.path precision}
variable {computed : targets = CellEndpoints.Targets.build chain.path precision}
variable {prepared : PreparedParents covered floor targets} {root : Named} {roots : RootChain parents root root}
variable {nonempty : parents ≠ []}
variable (retained : AtPoint covered chain precision floor rootStage targets computed prepared roots nonempty)

/-- Read the actual original constructed Stage at the GIVEN same full lifted point and actual precision. -/
def stage : Stage parameter ⟨point, chain.path⟩ precision := by
  cases parents with
  | nil => exact False.elim (nonempty rfl)
  | cons parent remaining =>
      have same : PreparedParent.startPoint parent = point := chain.start_eq
      cases same
      exact retained.2.2.val.2.val.stage

/-- The actual transported Stage retains exactly the SAME supplied source preparations and chain. -/
theorem stage_sources : retained.stage.sources = sources covered prepared chain := by
  unfold stage
  cases parents with
  | nil => exact False.elim (nonempty rfl)
  | cons parent remaining =>
      have same : PreparedParent.startPoint parent = point := chain.start_eq
      cases same
      let attempt : StageAttempt covered chain precision floor rootStage := retained.2.2.val.1
      have original := retained.2.2.val.2.val.stage_sources
      have attemptFactory : attempt = StageAttempt.ofPrepared covered chain targets computed prepared rootStage :=
        retained.2.2.val.2.property.trans retained.2.1.property
      have retainedSources : sources covered attempt.preparations chain =
          sources covered (StageAttempt.ofPrepared covered chain targets computed prepared rootStage).preparations
            chain :=
        congrArg (fun actual : StageAttempt covered chain precision floor rootStage =>
          sources covered actual.preparations chain) attemptFactory
      have supplied := congrArg (fun values => sources covered values chain)
        (StageAttempt.ofPrepared_preparations covered chain targets computed prepared rootStage)
      exact original.trans (attempt.preparations_sources.symm.trans
        (retainedSources.trans (supplied.trans (sources_castTargets covered prepared computed chain))))

/-- The actual completed Stage reads each SAME supplied original channel list in unchanged order. -/
theorem stage_cells (channel : Fin 6) :
    retained.stage.sources.cells channel = (sources covered prepared chain).cells channel :=
  congrArg (fun actual : Path parameter chain.path => actual.cells channel) retained.stage_sources

end AtPoint

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.OccurrenceCompletion

end
