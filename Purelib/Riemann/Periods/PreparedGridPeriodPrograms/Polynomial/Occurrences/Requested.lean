module

public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Occurrences.Values
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences.Retained
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences.Programs
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Riemann.Integration.PreparedCoveredParentLists
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Integration.Program.Comparison
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Primitive.Comparison
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

/-! # Original source requests and value attachments on a retained canonical spine

Only the actual parent-list and first lifted-point indices are transported.
The canonical cover, closed root chain, selected source request, preparation
stream and independently constructed occurrence jets remain their original
owners. Sample readbacks derive their value-name comparison.
-/

public section

universe u

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (Equivalent NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell (PreparedParents)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents (StageAttempt)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt (Requested OccurrenceCompletion)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedCoveredParentLists
open Purelib.Riemann.Topology.PreparedBankRootChains (ownerName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {base : Canonical}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval base)} {source : Differential 1}
    {walk : PeriodWalk grid base owner source} (spine : PolynomialSpine walk)
    {parent : CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1))}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1)))}

/-- Reindex the SAME complete canonical cover at its actual nonempty parent decomposition. -/
@[expose] def sourceCovered (same : spine.parents = parent :: parents) : CoveredParents 1 (parent :: parents) :=
  Eq.mp (congrArg (CoveredParents 1) same) spine.covered

/-- Reindex the SAME closed chain at its first retained physical point, including its sheet. -/
@[expose] def sourceChain (same : spine.parents = parent :: parents) :
    CenteredPathChain (parent :: parents)
      (start := Jets.Source.Cell.PreparedParent.startPoint parent)
      (finish := Jets.Source.Cell.PreparedParent.startPoint parent) :=
  (spine.chain.castParents same).basedAtFirst

/-- Read the original closed root links after the exact nonempty parent-list transport. -/
def sourceRoots (same : spine.parents = parent :: parents) :
    RootChain (parent :: parents) (ownerName owner) (ownerName owner) :=
  Eq.mp (congrArg (fun kept : List (CenteredEdge (Fibre.frameCurve frame)
      (PeriodMatrix.standardDifferential (0 : Fin 1))) => RootChain kept (ownerName owner) (ownerName owner))
    same) spine.roots

/-- A genuine source request on the original canonical parents retains its whole original factory. -/
abbrev RequestedConsumer (current floor rootStage : Nat) (accuracy : AccuracyRequest) (Result : Type u) : Type _ :=
  (parent : CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1))) →
  (parents : List (CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1)))) →
  (same : spine.parents = parent :: parents) →
  (roots : RootChain (parent :: parents) (ownerName owner) (ownerName owner)) →
  roots = spine.sourceRoots same →
  (requested : Requested (spine.sourceCovered same) (spine.sourceChain same) current floor rootStage accuracy) →
  requested = Requested.build (spine.sourceCovered same) (spine.sourceChain same)
    current floor rootStage accuracy → Result

/-- Decompose an actually nonempty canonical spine and prepare its original selected source request ONCE.

The original chain's first-point readback supplies the exact lifted source
index. One actual closed-root transport is retained before the request.
Its original Targets, preparations and both finite checking outcomes stay
stored; no occurrence completion or jet is built here.
-/
def withRequested (nonempty : spine.parents ≠ []) (current floor rootStage : Nat) (accuracy : AccuracyRequest)
    {Result : Type u} (consume : spine.RequestedConsumer current floor rootStage accuracy Result) : Result :=
  match same : spine.parents with
  | [] => False.elim (nonempty same)
  | parent :: parents =>
      let covered := spine.sourceCovered same
      let chain := spine.sourceChain same
      let roots := spine.sourceRoots same
      let requested := Requested.build covered chain current floor rootStage accuracy
      consume parent parents same roots rfl requested rfl

/-- Reindex one canonical preparation stream through free original list and lifted-point indices. -/
private def originalPreparations
    {keptParents : List (CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1)))}
    {point : LiftedPoint 2} (covered : CoveredParents 1 keptParents)
    (chain : CenteredPathChain keptParents (start := point) (finish := point))
    (same : keptParents = parent :: parents) {current floor rootStage : Nat} {accuracy : AccuracyRequest}
    (requested : Requested (Eq.mp (congrArg (CoveredParents 1) same) covered)
      (chain.castParents same).basedAtFirst current floor rootStage accuracy) :
    (stage : Nat) → PreparedParents covered floor (CellEndpoints.Targets.build chain.path stage) := by
  cases same
  have first := chain.start_eq
  cases first
  exact requested.attempt.preparationFamily

/-- Read the SAME retained source preparation stream at the original canonical chain indices.

Only exact list and first-point indices move. Each callback invokes the
original preparation stream once, including its unchanged selected-cache
branch. Exact index transport returns that complete value without replaying
its callback or claiming sharing between independent programme queries.
-/
def sourcePreparations (same : spine.parents = parent :: parents) {current floor rootStage : Nat}
    {accuracy : AccuracyRequest}
    (requested : Requested (spine.sourceCovered same) (spine.sourceChain same) current floor rootStage accuracy) :
    (stage : Nat) → PreparedParents spine.covered floor (CellEndpoints.Targets.build spine.chain.path stage) :=
  originalPreparations spine.covered spine.chain same requested

/-- Exact free-index transport reads the original canonical programme's same completed scalar value. -/
private theorem original_value_sample
    {keptParents : List (CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1)))}
    {point : LiftedPoint 2} (covered : CoveredParents 1 keptParents)
    (chain : CenteredPathChain keptParents (start := point) (finish := point))
    (same : keptParents = parent :: parents) {current floor rootStage : Nat} {accuracy : AccuracyRequest}
    (requested : Requested (Eq.mp (congrArg (CoveredParents 1) same) covered)
      (chain.castParents same).basedAtFirst current floor rootStage accuracy)
    (completed : requested.attempt.OccurrenceFamily) (actual : SynchronizedPeriodJet frame)
    (factory : actual = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor) (rootStage := rootStage)
      (Eq.mp (congrArg (CoveredParents 1) same) covered) (chain.castParents same).basedAtFirst
      (fun stage => (completed stage).val)) (coordinate : Fin 2) (stage : Nat) :
    ((actual.value coordinate).integral.model stage).integralSample =
      ((PreparedParents.certified covered chain (originalPreparations covered chain same requested)
        (Jets.Specification.Table.valueIndex coordinate)).integral.model stage).integralSample := by
  cases same
  have first := chain.start_eq
  cases first
  have actualModel := completed.value_model (parameter := parameter) (frame := frame)
    (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (index := requested.selected.stage)
    (floor := floor) (rootStage := rootStage) (attempt := requested.attempt) actual factory coordinate stage
  have original := (congrArg (fun programme : RefinementProgram => (programme.model stage).integralSample)
    (PreparedParents.certified_integral covered chain requested.attempt.preparationFamily
      (Jets.Specification.Table.valueIndex coordinate))).trans
    (congrArg PathModel.integralSample (PreparedParents.program_model covered chain
      requested.attempt.preparationFamily (Jets.Specification.Table.valueIndex coordinate) stage))
  exact (congrArg PathModel.integralSample actualModel).trans original.symm

/-- Each actual completed source value reads the original canonical preparation programme's SAME scalar sample.

The supplied whole jet factory and original occurrence-family model law
identify the actual source model. Exact index transport preserves the
preparation cache; neither programme nor completion is reconstructed.
-/
theorem source_value_sample (same : spine.parents = parent :: parents) {current floor rootStage : Nat}
    {accuracy : AccuracyRequest}
    (requested : Requested (spine.sourceCovered same) (spine.sourceChain same) current floor rootStage accuracy)
    (completed : requested.attempt.OccurrenceFamily) (actual : SynchronizedPeriodJet frame)
    (factory : actual = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor) (rootStage := rootStage)
      (spine.sourceCovered same) (spine.sourceChain same) (fun stage => (completed stage).val))
    (coordinate : Fin 2) (stage : Nat) :
    ((actual.value coordinate).integral.model stage).integralSample =
      ((PreparedParents.certified spine.covered spine.chain (spine.sourcePreparations same requested)
        (Jets.Specification.Table.valueIndex coordinate)).integral.model stage).integralSample :=
  original_value_sample spine.covered spine.chain same requested completed actual factory coordinate stage

/-- Compare an independently retained canonical occurrence jet to the SAME actual completed source jet.

The original occurrence constructor's whole factory and preparation sample
readback are composed with the given source jet's actual model law. Both
programme owners remain unchanged and the generic comparison derives its
all-later numerical schedule internally.
-/
def sourceValueEquivalent (same : spine.parents = parent :: parents) {current floor rootStage : Nat}
    {accuracy : AccuracyRequest}
    (requested : Requested (spine.sourceCovered same) (spine.sourceChain same) current floor rootStage accuracy)
    (completed : requested.attempt.OccurrenceFamily) (actual : SynchronizedPeriodJet frame)
    (factory : actual = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor) (rootStage := rootStage)
      (spine.sourceCovered same) (spine.sourceChain same) (fun stage => (completed stage).val))
    (nonempty : spine.parents ≠ []) (canonical : SynchronizedPeriodJet frame)
    (canonicalFactory : canonical = (spine.occurrenceJet floor rootStage
      (spine.sourcePreparations same requested) nonempty).1) (coordinate : Fin 2) :
    NamedEquivalent (canonical.value coordinate).integral.output.name (actual.value coordinate).integral.output.name :=
  Integration.Program.Comparison.refinementProgram_output_equivalent_of_samples_eq
    (canonical.value coordinate).integral (actual.value coordinate).integral (by
      intro stage
      have retained := congrArg (fun jet : SynchronizedPeriodJet frame =>
        ((jet.value coordinate).integral.model stage).integralSample) canonicalFactory
      have original := congrArg (fun bundle : (jet : SynchronizedPeriodJet frame) ×
          Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet =>
        ((bundle.1.value coordinate).integral.model stage).integralSample)
        (spine.occurrenceJet_factory floor rootStage (spine.sourcePreparations same requested) nonempty)
      have prepared := OccurrenceCompletion.ofPreparations_value_sample
        (parameter := parameter) (frame := frame) (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
        (count := 1) (floor := floor) spine.covered spine.chain
        (spine.sourcePreparations same requested) rootStage spine.roots nonempty coordinate stage
      exact retained.trans (original.trans (prepared.trans
        (spine.source_value_sample (parameter := parameter) (frame := frame) (walk := walk)
          (parent := parent) (parents := parents) same requested completed actual factory coordinate stage).symm)))

/-- Transport the original executable period comparison along free parent and covered-cache indices. -/
private def originalPeriodEquivalent
    {keptParents : List (CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1)))}
    (same : keptParents = walk.initial.state.parents.map
      (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
    (covered : CoveredParents 1 keptParents)
    (covered_eq : Eq.mp (congrArg (CoveredParents 1) same) covered =
      CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
    (chain : CenteredPathChain keptParents
      (start := walk.initial.state.start) (finish := walk.initial.state.start))
    {sourceFloor : Nat}
    (prepared : (stage : Nat) → PreparedParents covered sourceFloor (CellEndpoints.Targets.build chain.path stage))
    (actual : RefinementProgram)
    (samples : ∀ stage, (actual.model stage).integralSample =
      ((PreparedParents.certified covered chain prepared 0).integral.model stage).integralSample) :
    Equivalent actual.geometric.toApproximation (walk.program 0).integral.geometric.toApproximation := by
  cases same
  let originalPrepared := fun stage => (prepared stage).castCovered covered_eq
  let original := PeriodWalk.sourcePeriodEquivalent (parameter := parameter) (frame := frame)
    walk chain originalPrepared
  refine original.withSamples actual.geometric.toApproximation
    (walk.program 0).integral.geometric.toApproximation ?_ (fun _ => rfl)
  intro stage
  change (actual.model stage).integralSample =
    ((PreparedParents.certified
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
      chain originalPrepared 0).integral.model stage).integralSample
  have left := PreparedParents.certified_cells covered chain prepared 0 stage
  have right := PreparedParents.certified_cells
    (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
    chain originalPrepared 0 stage
  have middle := congrArg (fun source : Jets.Source.Path parameter chain.path =>
    (PathModel.mk (source.cells 0)).integralSample) ((prepared stage).sources_castCovered covered_eq chain)
  exact (samples stage).trans
    ((congrArg (fun cells => (PathModel.mk cells).integralSample) left).trans
      (middle.symm.trans (congrArg (fun cells => (PathModel.mk cells).integralSample) right).symm))

/-- The given source value-zero model stream has the original walk's executable all-later period comparison.

The full jet factory and actual preparation sample readback identify its
left stream. Exact parent and covered-cache transports preserve that SAME
preparation family. The existing comparison computes both paid floors
from its original primitive request, source Selection and canonical tail
before any model readings; it does not resample an output name or identify
name indices with model indices.
-/
def sourcePeriodEquivalent (same : spine.parents = parent :: parents) {current floor rootStage : Nat}
    {accuracy : AccuracyRequest}
    (requested : Requested (spine.sourceCovered same) (spine.sourceChain same) current floor rootStage accuracy)
    (completed : requested.attempt.OccurrenceFamily) (actual : SynchronizedPeriodJet frame)
    (factory : actual = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor) (rootStage := rootStage)
      (spine.sourceCovered same) (spine.sourceChain same) (fun stage => (completed stage).val)) :
    Equivalent (actual.value 0).integral.geometric.toApproximation
      (walk.program 0).integral.geometric.toApproximation :=
  originalPeriodEquivalent (parameter := parameter) (frame := frame) (walk := walk)
    spine.parents_eq spine.covered spine.covered_factory spine.chain
    (spine.sourcePreparations same requested) (actual.value 0).integral
    (fun stage => spine.source_value_sample (parameter := parameter) (frame := frame) (walk := walk)
      (parent := parent) (parents := parents) same requested completed actual factory 0 stage)

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine

end
