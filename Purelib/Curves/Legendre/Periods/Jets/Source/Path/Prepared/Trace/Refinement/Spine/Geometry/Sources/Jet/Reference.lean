module

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Jet.Comparison
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences.Programs
public import Purelib.Data.Vector.Dependent
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

/-! # One old Requested reference on the SAME actual child cover and lifted chain

The given adaptive child-bank jet and full relation bundle are unchanged.
The original nonempty-list and full chain.start_eq transports bind one old
Requested source, its actual occurrence family and whole jet factory on
that SAME covered cycle before numerical accuracy. Six original model
comparisons are derived from both real preparation rules and readbacks.
-/

public section

universe u

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (Equivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Vector (DependentVector)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}

/-- One original request, its SAME signed-root completion family and whole jet bundle compare to the given actual jet.

The selected attempt preserves all its original failure and inconclusive
outcomes. The raw completion factory and actual cached-zero rule factory
remain distinct; the latter retains every original per-stage subtype law.
The reference bundle consumes that rule, so both relation constructors
share its finite Stage-zero completion. Comparison indices concern
actual programme models, not output names.
-/
@[expose] def Reference {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    {root : Named} (roots : RootChain (parent :: parents) root root) (actual : SynchronizedPeriodJet frame)
    (current floor rootStage : Nat) (accuracy : AccuracyRequest) : Type _ :=
  (requested : {value : Requested covered chain current floor rootStage accuracy //
    value = Requested.build (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) covered chain current floor rootStage accuracy}) ×
  (original : {value : requested.val.attempt.OccurrenceFamily //
    value = requested.val.attempt.completeOccurrenceFamily roots}) ×
  (completed : {value : requested.val.attempt.OccurrenceFamily //
    value = (let zero := original.val 0
      fun index => Nat.casesOn index zero (fun previous => original.val (previous + 1)))}) ×
  (reference : {value : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet //
    value = OccurrenceCompletion.build (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (floor := floor) (rootStage := rootStage)
      covered chain (fun index => (completed.val index).val)}) ×
  DependentVector (fun channel : Fin 6 =>
    Equivalent (actual.programme channel).approximation (reference.val.1.programme channel).approximation)

namespace Reference

/-- The same complete request/reference product transported jointly to the GIVEN full lifted basepoint.

The original list constructor selects the head. Only chain.start_eq
transports the cover, chain, signed roots, numerical preparations and
whole reference payload together. No point identity follows from scalar
coordinates, and an empty parent word is excluded by its real certificate.
-/
@[expose] def AtPoint {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) {point : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := point) (finish := point))
    {root : Named} (roots : RootChain parents root root) (nonempty : parents ≠ [])
    (actual : SynchronizedPeriodJet frame) (current floor rootStage : Nat) (accuracy : AccuracyRequest) : Type _ := by
  cases parents with
  | nil => exact False.elim (nonempty rfl)
  | cons parent remaining =>
      have same : PreparedParent.startPoint parent = point := chain.start_eq
      cases same
      exact Reference covered chain roots actual current floor rootStage accuracy

/-- Construct the original head-based reference once from its same-cover model comparison.

The raw family and cached zero precede the original jet bundle. The six
operators retain its actual model readbacks and independent source owners.
-/
private def prepareHead {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    {root : Named} (roots : RootChain (parent :: parents) root root) (actual : SynchronizedPeriodJet frame)
    (current floor rootStage : Nat) (accuracy : AccuracyRequest)
    (compare : (prepared : (index : Nat) →
      PreparedParents covered floor (CellEndpoints.Targets.build chain.path index)) → (channel : Fin 6) →
      Equivalent (actual.programme channel).approximation
        (programAtPrecision covered chain (fun index => index)
          (fun index => ⟨CellEndpoints.Targets.build chain.path index, rfl⟩) prepared
          (fun index => Nat.le_refl index) channel).approximation) :
    Reference covered chain roots actual current floor rootStage accuracy :=
  let requested : {value : Requested covered chain current floor rootStage accuracy //
      value = Requested.build (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) covered chain current floor rootStage accuracy} :=
    ⟨Requested.build (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) covered chain current floor rootStage accuracy, rfl⟩
  let original : {value : requested.val.attempt.OccurrenceFamily //
      value = requested.val.attempt.completeOccurrenceFamily roots} :=
    ⟨requested.val.attempt.completeOccurrenceFamily roots, rfl⟩
  let zero := original.val 0
  let completed : {value : requested.val.attempt.OccurrenceFamily //
      value = (let zero := original.val 0
        fun index => Nat.casesOn index zero (fun previous => original.val (previous + 1)))} :=
    ⟨(fun index => Nat.casesOn index zero (fun previous => original.val (previous + 1))), rfl⟩
  let reference : {value : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet //
      value = OccurrenceCompletion.build (parameter := parameter) (frame := frame) (basis := basis)
        (count := count) (floor := floor) (rootStage := rootStage)
        covered chain (fun index => (completed.val index).val)} :=
    ⟨OccurrenceCompletion.build (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (floor := floor) (rootStage := rootStage)
      covered chain (fun index => (completed.val index).val), rfl⟩
  have referenceFactory : reference.val.1 = OccurrenceCompletion.jet
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (floor := floor) (rootStage := rootStage) covered chain (fun index => (completed.val index).val) :=
    (congrArg (fun value : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet => value.1)
      reference.property).trans (OccurrenceCompletion.build_jet (parameter := parameter) (frame := frame)
        (basis := basis) (count := count) (floor := floor) (rootStage := rootStage)
        covered chain (fun index => (completed.val index).val))
  let compared : DependentVector (fun channel : Fin 6 =>
      Equivalent (actual.programme channel).approximation (reference.val.1.programme channel).approximation) :=
    DependentVector.ofFn (fun channel : Fin 6 =>
      let comparison : Equivalent (actual.programme channel).approximation
          (programAtPrecision covered chain (fun selected => selected)
            (fun selected => ⟨CellEndpoints.Targets.build chain.path selected, rfl⟩)
            requested.val.attempt.preparationFamily (fun selected => Nat.le_refl selected) channel).approximation :=
        compare requested.val.attempt.preparationFamily channel
      comparison.withSamples (actual.programme channel).approximation (reference.val.1.programme channel).approximation
        (fun _index => rfl)
        (by
          intro index
          have stored := OccurrenceFamily.programme_model
            (parameter := parameter) (frame := frame) (basis := basis) (count := count)
            (covered := covered) (chain := chain) (index := requested.val.selected.stage)
            (floor := floor) (rootStage := rootStage) (attempt := requested.val.attempt)
            completed.val reference.val.1 referenceFactory channel index
          have identity : model covered chain requested.val.attempt.preparationFamily channel index =
              modelAtPrecision covered chain (fun selected => selected)
                (fun selected => ⟨CellEndpoints.Targets.build chain.path selected, rfl⟩)
                requested.val.attempt.preparationFamily channel index := by rfl
          have selected := programAtPrecision_model covered chain (fun selected => selected)
            (fun selected => ⟨CellEndpoints.Targets.build chain.path selected, rfl⟩)
            requested.val.attempt.preparationFamily (fun selected => Nat.le_refl selected) channel index
          have models := stored.trans (identity.trans selected.symm)
          exact ((reference.val.1.programme channel).certifiedView_sample index).trans
            ((congrArg PathModel.integralSample models).trans
              ((programAtPrecision covered chain (fun selected => selected)
                (fun selected => ⟨CellEndpoints.Targets.build chain.path selected, rfl⟩)
                requested.val.attempt.preparationFamily (fun selected => Nat.le_refl selected)
                channel).certifiedView_sample index).symm)))
  ⟨requested, original, completed, reference, compared⟩

/-- Transport the whole nonempty covered chain before running the one head-based reference worker.

The free parent list and full lifted startpoint move together, including
the actual root chain and original preparation-comparison rule.
-/
private def prepareAtPoint {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) {point : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := point) (finish := point))
    {root : Named} (roots : RootChain parents root root) (nonempty : parents ≠ [])
    (actual : SynchronizedPeriodJet frame) (current floor rootStage : Nat) (accuracy : AccuracyRequest)
    (compare : (prepared : (index : Nat) →
      PreparedParents covered floor (CellEndpoints.Targets.build chain.path index)) → (channel : Fin 6) →
      Equivalent (actual.programme channel).approximation
        (programAtPrecision covered chain (fun index => index)
          (fun index => ⟨CellEndpoints.Targets.build chain.path index, rfl⟩) prepared
          (fun index => Nat.le_refl index) channel).approximation) :
    AtPoint covered chain roots nonempty actual current floor rootStage accuracy := by
  cases parents with
  | nil => exact False.elim (nonempty rfl)
  | cons parent remaining =>
      have same : PreparedParent.startPoint parent = point := chain.start_eq
      cases same
      exact prepareHead covered chain roots actual current floor rootStage accuracy compare

end Reference

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner ownerName)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count floor : Nat} {sheet : Fin 2} {ambient : Purelib.Geometry.Rational.Box}
variable {grid : ClearGrid (Paths.polynomial parameter) ambient} {base : Canonical}
variable (owner : Owner ((Paths.polynomial parameter).eval base)) (closed : RootClosedWalk grid base owner)
variable {inputCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) closed.traced.lineage}
variable {materialized : OwnerPath (Paths.polynomial parameter) base owner base
  (PreparedPathGluing.finishOwner closed.traced.prepared)}
variable {factory : materialized = closed.traced.lineage.ownerPath} {diameter : Rational} {positive : 0 < diameter}
variable (retained : Materialized.Geometry (count := count)
  diameter positive closed.traced.lineage inputCenters materialized factory)
variable (childChain : CenteredPathChain retained.parents (start := (⟨base, sheet⟩ : LiftedPoint 2))
  (finish := (⟨base, sheet⟩ : LiftedPoint 2)))

namespace Geometry.Sources

variable (precision : Nat → Nat)
variable (requested : (index : Nat) → { value : CellEndpoints.Targets childChain.path (precision index) //
  value = CellEndpoints.Targets.build childChain.path (precision index) })
variable (sourceBanks : (index : Nat) → Sources (count := count) (floor := floor)
  (original := childChain.path) (stage := precision index) (targets := (requested index).val) retained)
variable {rootStage : Nat} {walkPositive : 0 < closed.walk.edgeCount}
variable (completed : (index : Nat) → Occurrences (count := count) (floor := floor)
  owner closed retained childChain (precision index) rootStage
    (requested index).val (requested index).property (sourceBanks index) walkPositive)

/-- Retain the GIVEN full adaptive source bundle beside one genuine old Requested reference on its SAME child cycle.

Both source geometries and signed-root owners are the supplied original
caches. Walk positivity derives nonemptiness. The private original-head
worker jointly transports the full lifted point, cover and chain, then
binds one old Requested.build, one raw occurrence family, its finite
Stage-zero completion and actual cached-zero rule, then one whole
jet/relation bundle. The six model comparisons come from the original
same-cover operation and occurrence readbacks, with no desired
model/path equality or final derivative bound as an input.

This operation belongs before epsilon. The given rules remain executable
functions; independent later rule invocations are not asserted memoized.
The reference request preserves its original failed and inconclusive
branches, and the given adaptive source bundle is forwarded unchanged.
-/
def withReference (precisionPaid : ∀ index, index ≤ precision index)
    (rooted : {value : RootChain retained.parents (ownerName owner) (ownerName owner) //
      value = Geometry.closedRoots owner closed retained})
    (actual : (jet : SynchronizedPeriodJet frame) ×
      Connection.ConnectionCertificate jet × PicardFuchs.PicardFuchsCertificate jet)
    (actualFactory : actual.1 =
      jet owner closed retained childChain precision requested sourceBanks completed precisionPaid)
    (referenceCurrent referenceFloor referenceRootStage : Nat) (referenceAccuracy : AccuracyRequest)
    {Result : Type u}
    (consume :
      (given : {value : (jet : SynchronizedPeriodJet frame) ×
        Connection.ConnectionCertificate jet × PicardFuchs.PicardFuchsCertificate jet // value = actual}) →
      StageAttempt.Requested.Reference.AtPoint (parameter := parameter) (frame := frame) (basis := basis)
        (count := count) (root := ownerName owner) retained.covered childChain rooted.val
        (Geometry.parents_nonempty_of_walk owner closed retained walkPositive) given.val.1
        referenceCurrent referenceFloor referenceRootStage referenceAccuracy → Result) : Result :=
  let given : {value : (jet : SynchronizedPeriodJet frame) ×
      Connection.ConnectionCertificate jet × PicardFuchs.PicardFuchsCertificate jet // value = actual} := ⟨actual, rfl⟩
  have givenFactory : given.val.1 =
      jet owner closed retained childChain precision requested sourceBanks completed precisionPaid :=
    (congrArg (fun value : (jet : SynchronizedPeriodJet frame) ×
      Connection.ConnectionCertificate jet × PicardFuchs.PicardFuchsCertificate jet => value.1)
      given.property).trans actualFactory
  let reference : StageAttempt.Requested.Reference.AtPoint
      (parameter := parameter) (frame := frame) (basis := basis) (count := count) (root := ownerName owner)
      retained.covered childChain rooted.val (Geometry.parents_nonempty_of_walk owner closed retained walkPositive)
      given.val.1 referenceCurrent referenceFloor referenceRootStage referenceAccuracy :=
    StageAttempt.Requested.Reference.prepareAtPoint
    (parameter := parameter) (frame := frame) (basis := basis) (count := count) (root := ownerName owner)
    retained.covered childChain rooted.val (Geometry.parents_nonempty_of_walk owner closed retained walkPositive)
    given.val.1 referenceCurrent referenceFloor referenceRootStage referenceAccuracy
    (fun referencePrepared channel => jet_programmes_equivalent
      (parameter := parameter) (frame := frame) (basis := basis) (count := count) (floor := floor)
      owner closed retained childChain precision requested sourceBanks completed precisionPaid given.val.1 givenFactory
      (referenceFloor := referenceFloor) (fun index => index)
      (fun index => ⟨CellEndpoints.Targets.build childChain.path index, rfl⟩)
      referencePrepared (fun index => Nat.le_refl index) channel)
  consume given reference

end Geometry.Sources

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

end
