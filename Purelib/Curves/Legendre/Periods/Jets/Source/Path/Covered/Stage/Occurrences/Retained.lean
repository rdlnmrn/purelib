module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

/-! # Occurrence-completed families retaining the actual selected attempt

The selected branch retains the entire given occurrence completion. Other
stages consume the original attemptFamily and perform their own positional
endpoint comparisons. Original point-only checks, both StageResult outcomes
and unresolved Commons remain stored in each actual StageAttempt.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent)}
    {index floor rootStage : Nat} (attempt : StageAttempt covered chain index floor rootStage)

/-- Every member retains its whole original attempt and positional completion at its exact original stage. -/
@[expose] def OccurrenceFamily : Type _ :=
  (stage : Nat) →
    { retained : (current : StageAttempt (parameter := parameter) (frame := frame)
        covered chain stage floor rootStage) × OccurrenceCompletion current //
      retained.1 = attempt.attemptFamily stage }

namespace OccurrenceCompletion

variable {attempt}

/-- Extend the supplied actual positional completion while retaining its entire selected cache.

Only different stages run the genuine attemptFamily and new per-endpoint
Common comparisons. The same original closed RootChain supplies their
signed incidence; no Ready, Distinct or final sample bound is assumed.
-/
def family (completed : OccurrenceCompletion attempt) {root : Named}
    (roots : RootChain (parent :: parents) root root) :
    attempt.OccurrenceFamily :=
  fun stage =>
    if equal : stage = index then
      ⟨Eq.mpr (congrArg (fun selected =>
          (current : StageAttempt (parameter := parameter) (frame := frame)
            covered chain selected floor rootStage) × OccurrenceCompletion current) equal)
        (⟨attempt, completed⟩ : (current : StageAttempt covered chain index floor rootStage) ×
          OccurrenceCompletion current), by
        cases equal
        exact attempt.attemptFamily_at.symm⟩
    else
      let current := attempt.attemptFamily stage
      let actual := current.completeOccurrences roots
      ⟨⟨actual.1, actual.2.val⟩, actual.2.property⟩

/-- The selected branch stores the same complete original attempt and supplied occurrence completion. -/
private theorem packaged_family_at (completed : OccurrenceCompletion attempt) {root : Named}
    (roots : RootChain (parent :: parents) root root) :
    (completed.family (attempt := attempt) roots index).val =
      (⟨attempt, completed⟩ : (current : StageAttempt covered chain index floor rootStage) ×
        OccurrenceCompletion current) := by
  unfold family
  rewrite [dif_pos rfl]
  rfl

/-- The selected branch retains the entire given completion without another completion execution. -/
theorem family_at (completed : OccurrenceCompletion attempt) {root : Named}
    (roots : RootChain (parent :: parents) root root) :
    (completed.family (attempt := attempt) roots index).val =
      (⟨attempt, completed⟩ : (current : StageAttempt covered chain index floor rootStage) ×
        OccurrenceCompletion current) :=
  packaged_family_at (attempt := attempt) completed roots

end OccurrenceCompletion

namespace OccurrenceFamily

variable {attempt}

/-- A retained completed member consumes the exact preparation-family sources at the same original stage. -/
theorem stage_sources (retained : attempt.OccurrenceFamily) (stage : Nat) :
    (retained stage).val.2.stage.sources = sources covered (attempt.preparationFamily stage) chain :=
  ((retained stage).val.2.stage_sources.trans (retained stage).val.1.preparations_sources.symm).trans
    ((congrArg (fun current : StageAttempt covered chain stage floor rootStage =>
      sources covered current.preparations chain) (retained stage).property).trans
        (attempt.attemptFamily_sources stage))

/-- The member at the selected stage retains the original whole attempt, including failed and inconclusive checks. -/
theorem attempt_at (retained : attempt.OccurrenceFamily) :
    (retained index).val.1 = attempt :=
  (retained index).property.trans attempt.attemptFamily_at

end OccurrenceFamily

/-- Complete the actual selected attempt once, then retain that same completion throughout its original stage family.

The equality returned by completeOccurrences transports only the family
owner. The supplied original attempt and actual completed data are kept;
no equivalent replacement is constructed and no old failed branch is
reclassified as a successful point-only check.
-/
def completeOccurrenceFamily {root : Named} (roots : RootChain (parent :: parents) root root) :
    attempt.OccurrenceFamily :=
  let actual := attempt.completeOccurrences roots
  let retained := OccurrenceCompletion.family (attempt := actual.1) actual.2.val roots
  Eq.mp (congrArg (fun current : StageAttempt covered chain index floor rootStage => current.OccurrenceFamily)
    actual.2.property) retained

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt

end
