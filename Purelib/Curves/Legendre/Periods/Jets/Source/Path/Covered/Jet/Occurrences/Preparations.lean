module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet.Occurrences
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Integration.Path.Primitive.Cells.Targets

/-! # Positional jet completion from the original closed preparation family

The original nonempty centered spine and complete per-stage preparations
supply the actual attempts and occurrence completion. All six channels use
that same completion family and its original root closure. The whole
factory and lifted-cycle readbacks retain the original construction.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.OccurrenceCompletion

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)

/-- Complete the same supplied preparations on an actual nonempty closed centered spine.

The original chain identifies its first lifted point, including its sheet.
Equality elimination reindexes the whole chain and preparation family at
that point. Each callback then constructs one original bank/check attempt
and its positional completion. Separate callbacks remain separate work.
-/
def ofPreparations {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count floor : Nat} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {point : LiftedPoint 2} (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := point) (finish := point))
    (prepared : (index : Nat) →
      PreparedParents covered floor (CellEndpoints.Targets.build chain.path index))
    (rootStage : Nat) {root : Named} (roots : RootChain parents root root) (nonempty : parents ≠ []) :
    (actual : SynchronizedPeriodJet frame) ×
      Connection.ConnectionCertificate actual × PicardFuchs.PicardFuchsCertificate actual := by
  cases parents with
  | nil => exact False.elim (nonempty rfl)
  | cons parent parents =>
    have same : PreparedParent.startPoint parent = point := chain.start_eq
    cases same
    exact ofAttempts (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (floor := floor) (rootStage := rootStage) covered chain
      (fun index => StageAttempt.ofPrepared (parameter := parameter) (frame := frame) (basis := basis)
        (count := count) covered chain (CellEndpoints.Targets.build chain.path index) rfl
        (prepared index) rootStage) roots

/-- The nonempty constructor retains the exact original attempt and completion callback at the first physical point. -/
private theorem packaged_ofPreparations_cons_factory
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count floor : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (prepared : (index : Nat) →
      PreparedParents covered floor (CellEndpoints.Targets.build chain.path index))
    (rootStage : Nat) {root : Named} (roots : RootChain (parent :: parents) root root)
    (nonempty : parent :: parents ≠ []) :
    ofPreparations covered chain prepared rootStage roots nonempty =
      let attempts := fun index => StageAttempt.ofPrepared (parameter := parameter) (frame := frame)
        (basis := basis) (count := count) covered chain (CellEndpoints.Targets.build chain.path index) rfl
        (prepared index) rootStage
      let completed : (index : Nat) →
          (attempt : StageAttempt covered chain index floor rootStage) × OccurrenceCompletion attempt := fun index =>
        let actual := (attempts index).completeOccurrences roots
        ⟨actual.1, actual.2.val⟩
      build covered chain completed := by
  unfold ofPreparations
  exact ofAttempts_factory (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) (rootStage := rootStage) covered chain
    (fun index => StageAttempt.ofPrepared (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) covered chain (CellEndpoints.Targets.build chain.path index) rfl
      (prepared index) rootStage) roots

/-- The nonempty constructor retains the exact original attempt and completion callback at the first physical point. -/
theorem ofPreparations_cons_factory
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count floor : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (prepared : (index : Nat) →
      PreparedParents covered floor (CellEndpoints.Targets.build chain.path index))
    (rootStage : Nat) {root : Named} (roots : RootChain (parent :: parents) root root)
    (nonempty : parent :: parents ≠ []) :
    ofPreparations covered chain prepared rootStage roots nonempty =
      let attempts := fun index => StageAttempt.ofPrepared (parameter := parameter) (frame := frame)
        (basis := basis) (count := count) covered chain (CellEndpoints.Targets.build chain.path index) rfl
        (prepared index) rootStage
      let completed : (index : Nat) →
          (attempt : StageAttempt covered chain index floor rootStage) × OccurrenceCompletion attempt := fun index =>
        let actual := (attempts index).completeOccurrences roots
        ⟨actual.1, actual.2.val⟩
      build covered chain completed :=
  packaged_ofPreparations_cons_factory covered chain prepared rootStage roots nonempty

/-- The complete six-channel construction retains the same original lifted cycle after exact first-point reindexing. -/
private theorem packaged_ofPreparations_cycle
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count floor : Nat} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {point : LiftedPoint 2} (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := point) (finish := point))
    (prepared : (index : Nat) →
      PreparedParents covered floor (CellEndpoints.Targets.build chain.path index))
    (rootStage : Nat) {root : Named} (roots : RootChain parents root root) (nonempty : parents ≠ []) :
    (ofPreparations covered chain prepared rootStage roots nonempty).1.cycle = constantCycle chain := by
  cases parents with
  | nil => exact False.elim (nonempty rfl)
  | cons parent parents =>
    have same : PreparedParent.startPoint parent = point := chain.start_eq
    cases same
    rewrite [ofPreparations_cons_factory]
    exact (congrArg (fun actual : SynchronizedPeriodJet frame => actual.cycle)
      (build_jet (parameter := parameter) (frame := frame) (basis := basis)
        (count := count) (floor := floor) (rootStage := rootStage) covered chain _)).trans
      (jet_cycle (parameter := parameter) (frame := frame) (basis := basis)
        (count := count) (floor := floor) (rootStage := rootStage) covered chain _)

/-- The complete six-channel construction retains the same original lifted cycle after exact first-point reindexing. -/
theorem ofPreparations_cycle
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count floor : Nat} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {point : LiftedPoint 2} (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := point) (finish := point))
    (prepared : (index : Nat) →
      PreparedParents covered floor (CellEndpoints.Targets.build chain.path index))
    (rootStage : Nat) {root : Named} (roots : RootChain parents root root) (nonempty : parents ≠ []) :
    (ofPreparations covered chain prepared rootStage roots nonempty).1.cycle = constantCycle chain :=
  packaged_ofPreparations_cycle covered chain prepared rootStage roots nonempty

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.OccurrenceCompletion

end
