module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Checked.Transport
import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices.Bank
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Entries
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Data.List.DependentProduct
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

/-! # Canonical stage completion retaining the selected original acquisition product

The old actual request and each new actual retained-preparation request
supply their whole original factory equations. Original product readbacks
identify each cached parent check. The same ordered original bank vertices
permit exact per-parent completion transport without another root payment.
The selected old completion remains a genuine geometric input.
-/

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

namespace Acquisitions

/-- Materialize new completions in the same original occurrence order while retaining old whole acquisition caches. -/
private def ofCanonical
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} (covered : CoveredParents count parents)
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstPath : LiftedPath 2 firstStart firstFinish} {lastPath : LiftedPath 2 lastStart lastFinish}
    {firstIndex lastIndex firstFloor lastFloor rootStage : Nat}
    (firstTargets : CellEndpoints.Targets firstPath firstIndex)
    (lastTargets : CellEndpoints.Targets lastPath lastIndex)
    (firstPrepared : PreparedParents covered firstFloor firstTargets)
    (lastPrepared : PreparedParents covered lastFloor lastTargets)
    (firstCanonical : firstPrepared = prepareCovered covered firstFloor firstTargets)
    (lastCanonical : lastPrepared = prepareCovered covered lastFloor lastTargets)
    (firstBank : Vertex.Bank parameter firstTargets.endpoint)
    (lastBank : Vertex.Bank parameter lastTargets.endpoint)
    (origins : firstBank.map (fun entry =>
        (⟨entry.point, entry.original⟩ : Σ point : LiftedPoint 2, Vertex parameter point)) =
      lastBank.map (fun entry =>
        (⟨entry.point, entry.original⟩ : Σ point : LiftedPoint 2, Vertex parameter point)))
    (firstChecks : Checks covered firstPrepared firstBank rootStage)
    (lastChecks : Checks covered lastPrepared lastBank rootStage)
    (firstFactory : firstChecks = checkParents covered firstPrepared firstBank rootStage)
    (lastFactory : lastChecks = checkParents covered lastPrepared lastBank rootStage)
    (retained : Acquisitions covered firstPrepared firstChecks) :
    Acquisitions covered lastPrepared lastChecks :=
  DependentProduct.ofFn parents (fun index =>
    let entry := covered.entry index
    let first := firstPrepared.entry index
    let last := lastPrepared.entry index
    let firstCheck := DependentProduct.get parents firstChecks index
    let lastCheck := DependentProduct.get parents lastChecks index
    let completed := DependentProduct.get parents retained index
    have firstPreparedFactory := (congrArg
      (fun prepared : PreparedParents covered firstFloor firstTargets => prepared.entry index)
      firstCanonical).trans (prepareCovered_entry covered firstFloor firstTargets index)
    have lastPreparedFactory := (congrArg
      (fun prepared : PreparedParents covered lastFloor lastTargets => prepared.entry index)
      lastCanonical).trans (prepareCovered_entry covered lastFloor lastTargets index)
    have firstCheckFactory := (congrArg
      (fun checked : Checks covered firstPrepared firstBank rootStage => DependentProduct.get parents checked index)
      firstFactory).trans (checkParents_entry covered firstPrepared firstBank rootStage index)
    have lastCheckFactory := (congrArg
      (fun checked : Checks covered lastPrepared lastBank rootStage => DependentProduct.get parents checked index)
      lastFactory).trans (checkParents_entry covered lastPrepared lastBank rootStage index)
    PreparedParent.Checked.Completion.ofCanonical (frame := frame) (basis := basis)
      entry.1 count entry.2 firstFloor lastFloor rootStage firstTargets lastTargets first last
      firstPreparedFactory lastPreparedFactory firstBank lastBank origins firstCheck lastCheck
      firstCheckFactory lastCheckFactory completed)

end Acquisitions

namespace StageAttempt

/-- An actual canonical retained-preparation factory identifies its complete source product at its own Targets. -/
private theorem canonical_of_prepared_factory
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    {index floor rootStage : Nat} (attempt : StageAttempt covered chain index floor rootStage)
    (factory : attempt = ofPrepared covered chain (CellEndpoints.Targets.build chain.path index) rfl
      (prepareCovered covered floor (CellEndpoints.Targets.build chain.path index)) rootStage) :
    attempt.2.1 = prepareCovered covered floor attempt.1.val := by
  cases factory
  exact ofPrepared_canonical covered chain (CellEndpoints.Targets.build chain.path index) rfl
    (prepareCovered covered floor (CellEndpoints.Targets.build chain.path index)) rfl rootStage

/-- An actual retained-preparation factory identifies its whole checking cache without executing a check. -/
private theorem checks_of_prepared_factory
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    {index floor rootStage : Nat} (attempt : StageAttempt covered chain index floor rootStage)
    (factory : attempt = ofPrepared covered chain (CellEndpoints.Targets.build chain.path index) rfl
      (prepareCovered covered floor (CellEndpoints.Targets.build chain.path index)) rootStage) :
    attempt.2.2.2.2.1 = checkParents covered attempt.2.1 attempt.2.2.1.val rootStage := by
  cases factory
  exact ofPrepared_checks covered chain (CellEndpoints.Targets.build chain.path index) rfl
    (prepareCovered covered floor (CellEndpoints.Targets.build chain.path index)) rootStage

namespace Completion

/-- Complete a genuinely new canonical request by transporting the same selected original completion geometry.

The old actual covered-stage and new retained-preparation factory equations
supply every source and check identity internally. Ordered original bank
vertices are derived from those same preparations and bank factories.
A successful new StageResult is consumed unchanged. Otherwise only new
numerical admissions and their original Stage are built, retaining every
old unpaid acquisition and every new actual ready Common. The original
selected completion remains a required genuine geometric payment.
-/
public def ofCanonical
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    {firstIndex lastIndex firstFloor lastFloor rootStage : Nat}
    (first : StageAttempt covered chain firstIndex firstFloor rootStage)
    (last : StageAttempt covered chain lastIndex lastFloor rootStage)
    (firstFactory : first = fromCovered covered chain firstIndex firstFloor rootStage)
    (lastFactory : last = ofPrepared covered chain (CellEndpoints.Targets.build chain.path lastIndex) rfl
      (prepareCovered covered lastFloor (CellEndpoints.Targets.build chain.path lastIndex)) rootStage)
    (completed : Completion first) : Completion last :=
  @dite (Completion last) last.Ready last.2.2.2.2.2.1
    (fun paid => last.completeReady paid)
    (fun _ => by
      have firstCanonical := prepared_of_factory covered chain first firstFactory
      have lastCanonical := canonical_of_prepared_factory covered chain last lastFactory
      have firstChecks := checks_of_factory covered chain first firstFactory
      have lastChecks := checks_of_prepared_factory covered chain last lastFactory
      have firstBank := congrArg
        (fun bank : Vertex.Bank parameter first.1.val.endpoint => bank.map (fun entry =>
          (⟨entry.point, entry.original⟩ : Σ point : LiftedPoint 2, Vertex parameter point)))
        first.2.2.1.property
      have lastBank := congrArg
        (fun bank : Vertex.Bank parameter last.1.val.endpoint => bank.map (fun entry =>
          (⟨entry.point, entry.original⟩ : Σ point : LiftedPoint 2, Vertex parameter point)))
        last.2.2.1.property
      have firstPrepared := congrArg
        (fun prepared : PreparedParents covered firstFloor first.1.val =>
          (requestBank (frame := frame) (targets := first.1.val) covered prepared).map (fun entry =>
            (⟨entry.point, entry.original⟩ : Σ point : LiftedPoint 2, Vertex parameter point))) firstCanonical
      have lastPrepared := congrArg
        (fun prepared : PreparedParents covered lastFloor last.1.val =>
          (requestBank (frame := frame) (targets := last.1.val) covered prepared).map (fun entry =>
            (⟨entry.point, entry.original⟩ : Σ point : LiftedPoint 2, Vertex parameter point))) lastCanonical
      have origins := firstBank.trans (firstPrepared.trans
        ((requestBank_prepareCovered_origins (frame := frame) (basis := basis)
          firstFloor lastFloor first.1.val last.1.val covered).trans (lastPrepared.symm.trans lastBank.symm)))
      let acquired := Acquisitions.ofCanonical covered first.1.val last.1.val first.2.1 last.2.1
        firstCanonical lastCanonical first.2.2.1.val last.2.2.1.val origins
        first.2.2.2.2.1 last.2.2.2.2.1 firstChecks lastChecks completed.1
      let result := Acquisitions.stage covered chain last.1.val last.1.property last.2.1 last.2.2.1.val
        last.2.2.2.1 last.2.2.2.2.1 acquired
      exact ⟨acquired, ⟨result, rfl⟩⟩)

end Completion

end StageAttempt

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents
