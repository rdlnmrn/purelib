module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Geometry
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Endpoints.Chain
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Origin.Quotients
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Queries
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Strip
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Alignment
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query.Rooted
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Accuracy
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.RootComparison
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences.Retained
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Accuracy.Comparison
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Occurrences.Programs
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Chain
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Repeat
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step.Source
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.DependentProduct

/-! # Actual source-strip roots at the same retained member's interior queries

One original occurrence/Alignment cache is built on the GIVEN member's
same geometry. A GIVEN stage-completion value and whole factory retain its
actual source preparations and six model lists. Supplied old/new query
answers are not observed again. One actual absolute Step and one original
queryStrip comparison attach the same target Point to the original seed
section; neither a root sign nor an integral comparison is assumed.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.LocalMember

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Branches
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
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
    {source : Requested covered chain current floor rootStage reference}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat} {offset : Canonical}
    {admitted : Norm.Basic.normSq offset ≤ allocation.bound}
    (cached : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage offset admitted)

/-- The actual member's stored global occurrences and original per-block interior alignments. -/
@[expose] def StripQueryCache : Type _ :=
  ShiftedGeometry.Occurrences
    (parameter := parameter) (increment := offset) (frame := frame) (basis := basis)
    (target := cached.targetFrame) (count := count) (firstParent := parent) (remaining := parents)
    (covered := covered) (floor := floor) (original := chain.path)
    (stage := source.selected.stage) (targets := source.targets) (prepared := source.prepared)
    (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
    (whole := cached.member.geometry) (requestIndex := cached.member.requested.selected.stage)
    (globalFloor := targetFloor) (rootStage := targetRootStage)
    cached.member.blocks cached.member.requested.request ×
  DependentProduct (parent :: parents) (fun index =>
    let block := DependentProduct.get (parent :: parents) cached.member.blocks index
    Acquisition.Segment.RootComparisons.Alignment block.comparison.paths block.comparison.firstReference)

/-- Build the original occurrence map and each genuine Alignment once on the SAME given member geometry. -/
def stripQueryCache : StripQueryCache cached :=
  let locations := ShiftedGeometry.occurrences
    (parameter := parameter) (increment := offset) (frame := frame) (basis := basis) (target := cached.targetFrame)
    (count := count) (firstParent := parent) (remaining := parents) (covered := covered) (floor := floor)
    (original := chain.path) (stage := source.selected.stage) (targets := source.targets) (prepared := source.prepared)
    (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
    (oldGeometry := chain) (oldRoots := roots) (whole := cached.member.geometry)
    (requestIndex := cached.member.requested.selected.stage) (globalFloor := targetFloor)
    (rootStage := targetRootStage)
    cached.member.blocks cached.member.requested.request cached.member.geometry_eq
  let aligned := DependentProduct.ofFn (parent :: parents) (fun index =>
    (DependentProduct.get (parent :: parents) cached.member.blocks index).comparison.align)
  ⟨locations, aligned⟩

namespace StripQueryCache

variable {cached}

/-- Read the original global occurrence from the same stored map without searching or rebuilding its word table. -/
@[expose] def located (cache : StripQueryCache cached)
    (index : Fin (cached.member.requested.request.shape.val.1 ::
      cached.member.requested.request.shape.val.2).length) :
    ShiftedGeometry.Occurrence
      (parameter := parameter) (increment := offset) (frame := frame) (basis := basis)
      (target := cached.targetFrame) (count := count) (firstParent := parent) (remaining := parents)
      (covered := covered) (floor := floor) (original := chain.path)
      (stage := source.selected.stage) (targets := source.targets) (prepared := source.prepared)
      (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
      (whole := cached.member.geometry) (requestIndex := cached.member.requested.selected.stage)
      (globalFloor := targetFloor) (rootStage := targetRootStage)
      cached.member.blocks cached.member.requested.request index :=
  DependentProduct.get (cached.member.requested.request.shape.val.1 ::
    cached.member.requested.request.shape.val.2) cache.1 index

/-- Read the SAME cached original Alignment at its bounded parent occurrence. -/
@[expose] def aligned (cache : StripQueryCache cached) (index : Fin (parent :: parents).length) :
    let block := DependentProduct.get (parent :: parents) cached.member.blocks index
    Acquisition.Segment.RootComparisons.Alignment block.comparison.paths block.comparison.firstReference :=
  DependentProduct.get (parent :: parents) cache.2 index

end StripQueryCache

/-- The actual endpoint observation product and original interior query cache of this SAME given member.

The original source owns both endpoint answer slots at every occurrence.
The second field retains the actual once-built occurrence/Alignment cache
and its complete original factory. Both caches precede derivative accuracy;
no alternate source, member, Frame or copied context is introduced.
-/
@[expose] def StripData : Type _ :=
  EndpointObservations source.prepared (by decide +kernel) (by decide +kernel) ×
  { queries : StripQueryCache cached // queries = cached.stripQueryCache }

namespace StripData

variable {cached}

/-- Reuse the GIVEN whole endpoint observation product while constructing one original member query cache. -/
def ofObserved (cached : LocalMember source ranges allocation roots widths
    targetCurrent targetFloor targetRootStage offset admitted)
    (observed : EndpointObservations source.prepared (by decide +kernel) (by decide +kernel)) : StripData cached :=
  let queries := cached.stripQueryCache
  ⟨observed, ⟨queries, rfl⟩⟩

/-- Bind both original endpoint observations once, then build the SAME given member's interior alignment cache once. -/
def build (cached : LocalMember source ranges allocation roots widths
    targetCurrent targetFloor targetRootStage offset admitted) : StripData cached :=
  let observed := EndpointObservations.build source.prepared (by decide +kernel) (by decide +kernel)
  ofObserved cached observed

/-- Read the SAME original zero/unit observation product without a query or source execution. -/
@[expose] def observed (retained : StripData cached) :
    EndpointObservations source.prepared (by decide +kernel) (by decide +kernel) := retained.1

/-- Read the original cached occurrences and Alignments without rebuilding the member or geometric comparisons. -/
@[expose] def queries (retained : StripData cached) : StripQueryCache cached := retained.2.val

/-- The retained-cache constructor consumes the whole given endpoint observation product unchanged. -/
theorem ofObserved_observed
    (cached : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage offset admitted)
    (observed : EndpointObservations source.prepared (by decide +kernel) (by decide +kernel)) :
    StripData.observed (cached := cached) (ofObserved cached observed) = observed := by
  unfold ofObserved StripData.observed
  rfl

/-- The complete retained query cache is its original constructor on the SAME given member. -/
theorem queries_eq (retained : StripData cached) :
    (StripData.queries (cached := cached) retained) = cached.stripQueryCache := retained.2.property

/-- Both GIVEN time-zero endpoint sections agree with the original source samples at every literal occurrence. -/
@[expose] def EndpointOrigins (retained : StripData cached)
    (actual : StripEndpointChain cached (StripData.observed (cached := cached) retained) 0
      (by decide +kernel)) : Type _ :=
  DependentProduct (parent :: parents) (fun index =>
    let pair := DependentProduct.get (parent :: parents) actual.1 index
    NamedEquivalent pair.1.2.val.root.value.name (source.prepared.entry index).firstSample.certificate.value.name ×
      NamedEquivalent pair.2.2.val.root.value.name (source.prepared.entry index).lastSample.certificate.value.name)

/-- Derive actual time-zero source anchoring from the GIVEN sections and the scalar zero-times-offset identity. -/
def endpointOrigins (retained : StripData cached)
    (actual : StripEndpointChain cached (StripData.observed (cached := cached) retained) 0
      (by decide +kernel)) : EndpointOrigins retained actual :=
  DependentProduct.ofFn (parent :: parents) (fun index =>
    let pair := DependentProduct.get (parent :: parents) actual.1 index
    have zero : (⟨(0 : Rational), 0⟩ : Canonical) * offset = 0 := Basic.zero_mul offset
    ⟨Variation.Point.Step.sourceEquivalent_of_zero (parameter := parameter)
        (source := (source.prepared.entry index).firstSample) pair.1.2.val zero,
      Variation.Point.Step.sourceEquivalent_of_zero (parameter := parameter)
        (source := (source.prepared.entry index).lastSample) pair.2.2.val zero⟩)

end StripData

/-- The complete original stage attempt/completion value retained by this member's positional family. -/
@[expose] def StageData (stage : Nat) : Type _ :=
  (current : StageAttempt (parameter := parameter + offset) (frame := cached.targetFrame)
    (basis := basis) (count := count) cached.member.requested.request.covered
    cached.member.requested.request.chain stage targetFloor targetRootStage) ×
  OccurrenceCompletion current

/-- A GIVEN stage value's actual computed-index source preparations equal the same original preparation family.

The whole given value is bound before this readback. Its original family
factory and attemptFamily_preparations identify the whole preparation
cache; no completed family callback or source preparation is executed here.
-/
theorem stagePreparations_eq (stage : Nat) (retained : StageData cached stage)
    (factory : retained = (cached.completed stage).val) :
    retained.1.preparations = cached.member.requested.request.attempt.preparationFamily stage :=
  (congrArg (fun value : StageData cached stage => value.1.preparations) factory).trans
    ((congrArg (fun current : StageAttempt (parameter := parameter + offset) (frame := cached.targetFrame)
      (basis := basis) (count := count) cached.member.requested.request.covered
      cached.member.requested.request.chain stage targetFloor targetRootStage => current.preparations)
      (cached.completed stage).property).trans
        (cached.member.requested.request.attempt.attemptFamily_preparations stage))

/-- Every channel's model from the GIVEN stage cache is the SAME original reference programme model at that stage. -/
theorem stageModel_eq (stage : Nat) (retained : StageData cached stage)
    (factory : retained = (cached.completed stage).val) (channel : Fin 6) :
    PathModel.mk ((sources cached.member.requested.request.covered retained.1.preparations
      cached.member.requested.request.chain).cells channel) =
      (cached.member.requested.request.programme channel).model stage :=
  (congrArg (fun prepared : PreparedParents cached.member.requested.request.covered targetFloor
      (CellEndpoints.Targets.build cached.member.requested.request.chain.path stage) =>
    PathModel.mk ((sources cached.member.requested.request.covered prepared
      cached.member.requested.request.chain).cells channel))
    (cached.stagePreparations_eq stage retained factory)).trans
      (cached.member.requested.request.programme_model (parameter := parameter) (increment := offset)
        (basis := basis) (target := cached.targetFrame) (count := count) (geometry := cached.member.geometry)
        (index := cached.member.requested.selected.stage) (floor := targetFloor) (rootStage := targetRootStage)
        channel stage).symm

/-- Either actual base-row model is the SAME given stage cache's original value/first channel model. -/
theorem stageBaseModel_eq (stage : Nat) (retained : StageData cached stage)
    (factory : retained = (cached.completed stage).val) (order coordinate : Fin 2) :
    (Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((cached.jet.value coordinate).integral)
      (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((cached.jet.first coordinate).integral)
        (fun index => Fin.elim0 index)) order).model stage =
    PathModel.mk ((sources cached.member.requested.request.covered retained.1.preparations
      cached.member.requested.request.chain).cells (Specification.Table.baseIndex order coordinate)) :=
  (cached.member.requested.request.occurrence_base_model
    (parameter := parameter) (increment := offset) (basis := basis) (target := cached.targetFrame)
    (count := count) (geometry := cached.member.geometry) (index := cached.member.requested.selected.stage)
    (floor := targetFloor) (rootStage := targetRootStage)
    cached.completed cached.jet cached.jet_eq order coordinate stage).trans
      (cached.stageModel_eq stage retained factory (Specification.Table.baseIndex order coordinate)).symm

/-- Either actual slope-row model is the SAME given stage cache's original first/second channel model. -/
theorem stageSlopeModel_eq (stage : Nat) (retained : StageData cached stage)
    (factory : retained = (cached.completed stage).val) (order coordinate : Fin 2) :
    (Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((cached.jet.first coordinate).integral)
      (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((cached.jet.second coordinate).integral)
        (fun index => Fin.elim0 index)) order).model stage =
    PathModel.mk ((sources cached.member.requested.request.covered retained.1.preparations
      cached.member.requested.request.chain).cells (Specification.Table.slopeIndex order coordinate)) :=
  (cached.member.requested.request.occurrence_slope_model
    (parameter := parameter) (increment := offset) (basis := basis) (target := cached.targetFrame)
    (count := count) (geometry := cached.member.geometry) (index := cached.member.requested.selected.stage)
    (floor := targetFloor) (rootStage := targetRootStage)
    cached.completed cached.jet cached.jet_eq order coordinate stage).trans
      (cached.stageModel_eq stage retained factory (Specification.Table.slopeIndex order coordinate)).symm

/-- The exact source-to-moving-model quotient error at one pair of actual stages and one original derivative row. -/
abbrev StageQuotientAt (sourceJet : SynchronizedPeriodJet frame) (accuracy : AccuracyRequest)
    (order coordinate : Fin 2) (firstIndex lastIndex : Nat) (retained : StageData cached lastIndex) : Prop :=
    Norm.Basic.normSq
      (((PathModel.mk ((sources cached.member.requested.request.covered retained.1.preparations
          cached.member.requested.request.chain).cells
          (Specification.Table.baseIndex order coordinate))).integralSample -
        ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((sourceJet.value coordinate).integral)
          (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((sourceJet.first coordinate).integral)
            (fun index => Fin.elim0 index)) order).model firstIndex).integralSample) / offset -
        ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((sourceJet.first coordinate).integral)
          (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((sourceJet.second coordinate).integral)
            (fun index => Fin.elim0 index)) order).model firstIndex).integralSample) < accuracy.tolerance

/-- All four actual stage-model quotients satisfy the paid accuracy at every pair of sufficiently late readings. -/
@[expose] def StageQuotientBounds (sourceJet : SynchronizedPeriodJet frame) (accuracy : AccuracyRequest)
    (firstFloor lastFloor : Nat) : Prop :=
  ∀ (order coordinate : Fin 2) (firstIndex lastIndex : Nat), firstFloor ≤ firstIndex → lastFloor ≤ lastIndex →
    ∀ (retained : StageData cached lastIndex), retained = (cached.completed lastIndex).val →
      StageQuotientAt cached sourceJet accuracy order coordinate firstIndex lastIndex retained

/-- Transfer an original source/jet quotient bound to the SAME given actual moving-stage model caches.

Only stageBaseModel_eq changes the displayed target sample. The bound and
all later model indices retain their original owners; no source, stage,
query or numerical comparison is constructed by this scalar transport.
-/
theorem stageQuotient_of_source (sourceJet : SynchronizedPeriodJet frame) (accuracy : AccuracyRequest)
    (firstFloor lastFloor : Nat)
    (paid : SourceQuotientBounds (parameter := parameter) (increment := offset) (frame := frame)
      (target := cached.targetFrame) sourceJet cached.jet accuracy firstFloor lastFloor) :
    StageQuotientBounds cached sourceJet accuracy firstFloor lastFloor := by
  intro order coordinate firstIndex lastIndex firstAfter lastAfter retained factory
  have actual := paid order coordinate firstIndex lastIndex firstAfter lastAfter
  have sample := congrArg (fun value : PathModel => value.integralSample)
    (cached.stageBaseModel_eq lastIndex retained factory order coordinate)
  have scalar := congrArg (fun value : Canonical => Norm.Basic.normSq
    ((value -
      ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((sourceJet.value coordinate).integral)
        (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((sourceJet.first coordinate).integral)
          (fun index => Fin.elim0 index)) order).model firstIndex).integralSample) / offset -
      ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((sourceJet.first coordinate).integral)
        (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((sourceJet.second coordinate).integral)
          (fun index => Fin.elim0 index)) order).model firstIndex).integralSample)) sample.symm
  exact scalar.trans_lt actual

/-- The actual paid source quotient bound applies to the SAME given moving-stage model cache at every later index.

The original SourceQuotientFloors value contains the independently derived
all-four bound and actual origin/fresh selections. Only a scalar sample
readback is transported here. Source and target Frames, the nonzero offset,
all later indices and given whole stage cache/factory stay explicit.
-/
theorem stageQuotient_lt (sourceJet : SynchronizedPeriodJet frame)
    {zeroAdmitted : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound}
    (zero : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage 0 zeroAdmitted)
    (accuracy : AccuracyRequest) (nonzero : offset ≠ 0) (originStart : Nat)
    (paid : SourceQuotientFloors (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) sourceJet zero cached accuracy nonzero originStart)
    : StageQuotientBounds cached sourceJet accuracy paid.2.2.val.1 paid.2.2.val.2 := by
  exact cached.stageQuotient_of_source sourceJet accuracy paid.2.2.val.1 paid.2.2.val.2 paid.2.2.property.2

/-- The GIVEN complete stage cache and its original whole family factory. -/
@[expose] def QueryStage (stage : Nat) : Type _ :=
  { value : StageData cached stage // value = (cached.completed stage).val }

section Query

attribute [local irreducible] ShiftedGeometry.Occurrence.block PreparedParent.ShiftedAcquisition.Linked.first
  LocalMember StripQueryCache.located StripQueryCache.aligned
  Shifted.requested ShiftedGeometry.Requested.request ShiftedGeometry.Request.shape

variable (cache : StripQueryCache cached) (stage : Nat)
    (retained : QueryStage cached stage)
    (index : Fin (cached.member.requested.request.shape.val.1 ::
      cached.member.requested.request.shape.val.2).length)
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)

/-- The SAME original mapped source observation bundle with its complete query factory. -/
@[expose] def SourceObservations : Type _ :=
  let located := StripQueryCache.located (cached := cached) cache index
  let prepared : PreparedParent (parameter := parameter) (frame := frame) (basis := basis)
      (parent := (parent :: parents)[located.block.val]'located.block.isLt)
      (covered.entry located.block).val count floor (covered.entry located.block).property source.targets :=
    PreparedParents.entry (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (parents := parent :: parents) (covered := covered) (floor := floor)
      (original := chain.path) (stage := source.selected.stage) (targets := source.targets)
      source.prepared located.block
  let time := ShiftedGeometry.Occurrence.sourceInput (whole := cached.member.geometry)
    (blocks := cached.member.blocks)
    (request := cached.member.requested.request) (sourceIndex := index) located input
  let admittedTime := ShiftedGeometry.Occurrence.sourceInput_inside (whole := cached.member.geometry)
    (blocks := cached.member.blocks)
    (request := cached.member.requested.request) (sourceIndex := index) located input inside
  { value : PreparedParent.QueryObservations (parameter := parameter) (frame := frame) (basis := basis)
      (parent := (parent :: parents)[located.block.val]'located.block.isLt)
      (patch := (covered.entry located.block).val) (count := count) (floor := floor)
      (covered := (covered.entry located.block).property) (original := chain.path)
      (stage := source.selected.stage) (targets := source.targets) prepared time //
    value = prepared.preparation.query.observe frame time admittedTime.1 admittedTime.2 }

/-- The GIVEN stage cache's independent target observation bundle and whole query factory. -/
@[expose] def TargetObservations : Type _ :=
  let selected : PreparedParent (parameter := parameter + offset) (frame := cached.targetFrame) (basis := basis)
      (parent := (cached.member.requested.request.shape.val.1 ::
        cached.member.requested.request.shape.val.2)[index.val]'index.isLt)
      (cached.member.requested.request.covered.entry index).val count targetFloor
      (cached.member.requested.request.covered.entry index).property
      (CellEndpoints.Targets.build cached.member.requested.request.chain.path stage) :=
    PreparedParents.entry (parameter := parameter + offset) (frame := cached.targetFrame) (basis := basis)
      (count := count)
      (parents := cached.member.requested.request.shape.val.1 :: cached.member.requested.request.shape.val.2)
      (covered := cached.member.requested.request.covered) (floor := targetFloor)
      (original := cached.member.requested.request.chain.path) (stage := stage)
      (targets := CellEndpoints.Targets.build cached.member.requested.request.chain.path stage)
      retained.val.1.preparations index
  { value : PreparedParent.QueryObservations (parameter := parameter + offset) (frame := cached.targetFrame)
      (basis := basis) (parent := (cached.member.requested.request.shape.val.1 ::
        cached.member.requested.request.shape.val.2)[index.val]'index.isLt)
      (patch := (cached.member.requested.request.covered.entry index).val) (count := count) (floor := targetFloor)
      (covered := (cached.member.requested.request.covered.entry index).property)
      (original := cached.member.requested.request.chain.path) (stage := stage)
      (targets := CellEndpoints.Targets.build cached.member.requested.request.chain.path stage) selected input //
    value = selected.preparation.query.observe cached.targetFrame input inside.1 inside.2 }

/-- The original direct query type on this member's actual child and bounded physical input. -/
@[expose] def ChildQuery : Type _ :=
  PreparedEdge.Query ((cached.member.requested.request.shape.val.1 ::
    cached.member.requested.request.shape.val.2)[index.val]'index.isLt).edge input inside

/-- The SAME original direct child query together with its whole constructor factory. -/
@[expose] def RetainedChildQuery : Type _ :=
  { value : ChildQuery cached index input inside //
    value = PreparedEdge.Query.build ((cached.member.requested.request.shape.val.1 ::
      cached.member.requested.request.shape.val.2)[index.val]'index.isLt).edge input inside }

variable (old : SourceObservations cached cache index input inside)
    (observed : TargetObservations cached stage retained index input inside)

/-- The actual source Step, its whole advance factory and the same target Point's signed seed-section relation. -/
@[expose] def StripQuery : Type _ :=
  let located := StripQueryCache.located (cached := cached) cache index
  let prepared : PreparedParent (parameter := parameter) (frame := frame) (basis := basis)
      (parent := (parent :: parents)[located.block.val]'located.block.isLt)
      (covered.entry located.block).val count floor (covered.entry located.block).property source.targets :=
    PreparedParents.entry (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (parents := parent :: parents) (covered := covered) (floor := floor)
      (original := chain.path) (stage := source.selected.stage) (targets := source.targets)
      source.prepared located.block
  let selected : PreparedParent (parameter := parameter + offset) (frame := cached.targetFrame) (basis := basis)
      (parent := (cached.member.requested.request.shape.val.1 ::
        cached.member.requested.request.shape.val.2)[index.val]'index.isLt)
      (cached.member.requested.request.covered.entry index).val count targetFloor
      (cached.member.requested.request.covered.entry index).property
      (CellEndpoints.Targets.build cached.member.requested.request.chain.path stage) :=
    PreparedParents.entry (parameter := parameter + offset) (frame := cached.targetFrame) (basis := basis)
      (count := count)
      (parents := cached.member.requested.request.shape.val.1 :: cached.member.requested.request.shape.val.2)
      (covered := cached.member.requested.request.covered) (floor := targetFloor)
      (original := cached.member.requested.request.chain.path) (stage := stage)
      (targets := CellEndpoints.Targets.build cached.member.requested.request.chain.path stage)
      retained.val.1.preparations index
  let range := ranges.entry located.block
  let block := DependentProduct.get (parent :: parents) cached.member.blocks located.block
  let time := ShiftedGeometry.Occurrence.sourceInput (whole := cached.member.geometry)
    (blocks := cached.member.blocks)
    (request := cached.member.requested.request) (sourceIndex := index) located input
  let localInside := (ShiftedGeometry.Occurrence.sourceInput_inside (whole := cached.member.geometry)
    (blocks := cached.member.blocks)
    (request := cached.member.requested.request) (sourceIndex := index) located input inside)
  let paid := (admitted.trans (allocation.bound_le_entry located.block)).trans
    (range.stripBound_le_shiftedBound.trans range.shiftedBound_le_bound)
  (_step : PreparedParent.QueryStep (parameter := parameter) (frame := frame) (basis := basis)
    (parent := (parent :: parents)[located.block.val]'located.block.isLt)
    (patch := (covered.entry located.block).val) (count := count) (floor := floor)
    (covered := (covered.entry located.block).property) (original := chain.path)
    (stage := source.selected.stage) (targets := source.targets)
    prepared range time localInside old.val old.property offset paid) ×
  PreparedParent.ShiftedAcquisition.RootComparison.QuerySection
    (parameter := parameter) (increment := offset) (frame := frame) (basis := basis)
    (parent := (parent :: parents)[located.block.val]'located.block.isLt)
    (patch := (covered.entry located.block).val) (count := count)
    (covered := (covered.entry located.block).property) (range := range) (target := cached.targetFrame)
    (admitted := admitted.trans ((allocation.bound_le_entry located.block).trans range.stripBound_le_shiftedBound))
    (firstSample := prepared.firstSample) (firstStep := block.first) (width := widths located.block)
    (retained := block.shifted) (strip := admitted.trans (allocation.bound_le_entry located.block))
    (actual := block.actual.val) (actual_eq := block.actual.property)
    (oldFloor := floor) (oldPath := chain.path) (oldStage := source.selected.stage) (oldTargets := source.targets)
    (child := (cached.member.requested.request.shape.val.1 ::
      cached.member.requested.request.shape.val.2)[index.val]'index.isLt)
    (newPatch := (cached.member.requested.request.covered.entry index).val) (newCount := count)
    (newFloor := targetFloor) (newCovered := (cached.member.requested.request.covered.entry index).property)
    (newPath := cached.member.requested.request.chain.path) (newStage := stage)
    (newTargets := CellEndpoints.Targets.build cached.member.requested.request.chain.path stage)
    block.comparison prepared selected input inside observed.val.retained.sample

/-- Attach a GIVEN actual stage/query cache to this same member's original source-root section.

The given observations, original stage attempt, source and member are not
executed again. One advanceRetained and one original queryStrip consume the
actual old sample, located original target, SAME Alignment and retained
direct child Query. Every stage keeps its own genuine model/Targets owner.
-/
def queryStrip
    (direct : ChildQuery cached index input inside) :
    StripQuery cached cache stage retained index input inside old observed :=
  let located := StripQueryCache.located (cached := cached) cache index
  let prepared : PreparedParent (parameter := parameter) (frame := frame) (basis := basis)
      (parent := (parent :: parents)[located.block.val]'located.block.isLt)
      (covered.entry located.block).val count floor (covered.entry located.block).property source.targets :=
    PreparedParents.entry (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (parents := parent :: parents) (covered := covered) (floor := floor)
      (original := chain.path) (stage := source.selected.stage) (targets := source.targets)
      source.prepared located.block
  let selected : PreparedParent (parameter := parameter + offset) (frame := cached.targetFrame) (basis := basis)
      (parent := (cached.member.requested.request.shape.val.1 ::
        cached.member.requested.request.shape.val.2)[index.val]'index.isLt)
      (cached.member.requested.request.covered.entry index).val count targetFloor
      (cached.member.requested.request.covered.entry index).property
      (CellEndpoints.Targets.build cached.member.requested.request.chain.path stage) :=
    PreparedParents.entry (parameter := parameter + offset) (frame := cached.targetFrame) (basis := basis)
      (count := count)
      (parents := cached.member.requested.request.shape.val.1 :: cached.member.requested.request.shape.val.2)
      (covered := cached.member.requested.request.covered) (floor := targetFloor)
      (original := cached.member.requested.request.chain.path) (stage := stage)
      (targets := CellEndpoints.Targets.build cached.member.requested.request.chain.path stage)
      retained.val.1.preparations index
  let range := ranges.entry located.block
  let block := DependentProduct.get (parent :: parents) cached.member.blocks located.block
  let time := ShiftedGeometry.Occurrence.sourceInput (whole := cached.member.geometry)
    (blocks := cached.member.blocks)
    (request := cached.member.requested.request) (sourceIndex := index) located input
  let localInside := (ShiftedGeometry.Occurrence.sourceInput_inside (whole := cached.member.geometry)
    (blocks := cached.member.blocks)
    (request := cached.member.requested.request) (sourceIndex := index) located input inside)
  let paid := (admitted.trans (allocation.bound_le_entry located.block)).trans
    (range.stripBound_le_shiftedBound.trans range.shiftedBound_le_bound)
  let step := PreparedParent.QueryStep.build
    (parameter := parameter) (frame := frame) (basis := basis)
    (parent := (parent :: parents)[located.block.val]'located.block.isLt)
    (patch := (covered.entry located.block).val) (count := count) (floor := floor)
    (covered := (covered.entry located.block).property) (original := chain.path)
    (stage := source.selected.stage) (targets := source.targets)
    prepared range time localInside old.val old.property offset paid
  let compared := PreparedParent.ShiftedAcquisition.RootComparison.queryStrip
    (parameter := parameter) (increment := offset) (frame := frame) (basis := basis)
    (parent := (parent :: parents)[located.block.val]'located.block.isLt)
    (patch := (covered.entry located.block).val) (count := count)
    (covered := (covered.entry located.block).property) (range := range) (target := cached.targetFrame)
    (admitted := admitted.trans ((allocation.bound_le_entry located.block).trans range.stripBound_le_shiftedBound))
    (firstSample := prepared.firstSample) (firstStep := block.first) (width := widths located.block)
    (retained := block.shifted) (strip := admitted.trans (allocation.bound_le_entry located.block))
    (actual := block.actual.val) (actual_eq := block.actual.property)
    (oldFloor := floor) (oldPath := chain.path) (oldStage := source.selected.stage) (oldTargets := source.targets)
    (child := (cached.member.requested.request.shape.val.1 ::
      cached.member.requested.request.shape.val.2)[index.val]'index.isLt)
    (newPatch := (cached.member.requested.request.covered.entry index).val) (newCount := count)
    (newFloor := targetFloor) (newCovered := (cached.member.requested.request.covered.entry index).property)
    (newPath := cached.member.requested.request.chain.path) (newStage := stage)
    (newTargets := CellEndpoints.Targets.build cached.member.requested.request.chain.path stage)
    (sourceSample := old.val.retained.sample)
    block.comparison (StripQueryCache.aligned (cached := cached) cache located.block) prepared
    selected input inside step.val observed.val.retained.sample
    located.child located.parent_eq direct
  ⟨step, compared⟩

end Query

section QueryAcquisition

attribute [local irreducible] ShiftedGeometry.Occurrence.block PreparedParent.ShiftedAcquisition.Linked.first
  LocalMember StripQueryCache.located StripQueryCache.aligned
  Shifted.requested ShiftedGeometry.Requested.request ShiftedGeometry.Request.shape

variable (cache : StripQueryCache cached) (stage : Nat)
    (retained : QueryStage cached stage)
    (index : Fin (cached.member.requested.request.shape.val.1 ::
      cached.member.requested.request.shape.val.2).length)
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)

/-- The SAME original mapped source query and GIVEN stage query share their exact whole physical lifted key. -/
abbrev StageKeyEq : Prop :=
  let located := StripQueryCache.located (cached := cached) cache index
  (⟨(source.prepared.entry located.block).preparation.cell.models.coordinate.point
        ((ShiftedGeometry.Occurrence.sourceInput (whole := cached.member.geometry)
    (blocks := cached.member.blocks)
    (request := cached.member.requested.request) (sourceIndex := index) located input)),
    ((parent :: parents)[located.block.val]'located.block.isLt).edge.sheet⟩ : LiftedPoint 2) =
  ⟨(retained.val.1.preparations.entry index).preparation.cell.models.coordinate.point input,
    ((cached.member.requested.request.shape.val.1 ::
      cached.member.requested.request.shape.val.2)[index.val]'index.isLt).edge.sheet⟩

/-- Derive whole lifted incidence from the actual occurrence's originalPoint/sheet laws and both original coordinates.

This equality concerns geometry only. The original queryStrip comparison
independently supplies the signed root relation; no Owner identity or
signed comparison follows from equal coordinates or sheet labels alone.
-/
theorem stageKey_eq : StageKeyEq cached cache stage retained index input :=
  let located := StripQueryCache.located (cached := cached) cache index
  let selected : PreparedParent (parameter := parameter + offset) (frame := cached.targetFrame) (basis := basis)
      (parent := (cached.member.requested.request.shape.val.1 ::
        cached.member.requested.request.shape.val.2)[index.val]'index.isLt)
      (cached.member.requested.request.covered.entry index).val count targetFloor
      (cached.member.requested.request.covered.entry index).property
      (CellEndpoints.Targets.build cached.member.requested.request.chain.path stage) :=
    PreparedParents.entry (parameter := parameter + offset) (frame := cached.targetFrame) (basis := basis)
      (count := count)
      (parents := cached.member.requested.request.shape.val.1 :: cached.member.requested.request.shape.val.2)
      (covered := cached.member.requested.request.covered) (floor := targetFloor)
      (original := cached.member.requested.request.chain.path) (stage := stage)
      (targets := CellEndpoints.Targets.build cached.member.requested.request.chain.path stage)
      retained.val.1.preparations index
  let block := DependentProduct.get (parent :: parents) cached.member.blocks located.block
  have sourcePoint := ShiftedGeometry.Occurrence.sourcePoint_eq
    (parameter := parameter) (increment := offset) (frame := frame) (basis := basis) (target := cached.targetFrame)
    (count := count) (firstParent := parent) (remaining := parents) (covered := covered) (floor := floor)
    (original := chain.path) (stage := source.selected.stage) (targets := source.targets) (prepared := source.prepared)
    (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
    (blocks := cached.member.blocks) (whole := cached.member.geometry)
    (requestIndex := cached.member.requested.selected.stage) (globalFloor := targetFloor)
    (rootStage := targetRootStage) (request := cached.member.requested.request) (sourceIndex := index) located input
  have targetPoint := PreparedParent.queryPoint_eq
    (parameter := parameter + offset) (frame := cached.targetFrame) (basis := basis)
    (parent := (cached.member.requested.request.shape.val.1 ::
      cached.member.requested.request.shape.val.2)[index.val]'index.isLt)
    (patch := (cached.member.requested.request.covered.entry index).val) (count := count) (floor := targetFloor)
    (covered := (cached.member.requested.request.covered.entry index).property)
    (original := cached.member.requested.request.chain.path) (stage := stage)
    (targets := CellEndpoints.Targets.build cached.member.requested.request.chain.path stage) selected input
  have coordinateEq :
      (source.prepared.entry located.block).preparation.cell.models.coordinate.point
        ((ShiftedGeometry.Occurrence.sourceInput (whole := cached.member.geometry)
    (blocks := cached.member.blocks)
    (request := cached.member.requested.request) (sourceIndex := index) located input)) =
        selected.preparation.cell.models.coordinate.point input := sourcePoint.trans targetPoint.symm
  have sheetEq : ((parent :: parents)[located.block.val]'located.block.isLt).edge.sheet =
      ((cached.member.requested.request.shape.val.1 ::
        cached.member.requested.request.shape.val.2)[index.val]'index.isLt).edge.sheet :=
    (PreparedParent.ShiftedAcquisition.child_sheet (parameter := parameter) (increment := offset)
      (frame := frame) (basis := basis) (parent := (parent :: parents)[located.block.val]'located.block.isLt)
      (patch := (covered.entry located.block).val) (count := count)
      (covered := (covered.entry located.block).property) (range := ranges.entry located.block)
      (target := cached.targetFrame)
      (admitted := admitted.trans ((allocation.bound_le_entry located.block).trans
        (ranges.entry located.block).stripBound_le_shiftedBound))
      (firstSample := (source.prepared.entry located.block).firstSample) (firstStep := block.first)
      (width := widths located.block)
      (child := (cached.member.requested.request.shape.val.1 ::
        cached.member.requested.request.shape.val.2)[index.val]'index.isLt)
      block.shifted located.child located.parent_eq).symm
  congrArg₂ (fun coordinate sheet => (⟨coordinate, sheet⟩ : LiftedPoint 2)) coordinateEq sheetEq

/-- The complete actual old/new query answers, retained direct Query and derived same-strip comparison at one input. -/
@[expose] def StripQueryAt : Type _ :=
  (old : SourceObservations cached cache index input inside) ×
  (observed : TargetObservations cached stage retained index input inside) ×
  (_direct : RetainedChildQuery cached index input inside) ×
  { _actual : StripQuery cached cache stage retained index input inside old observed //
    StageKeyEq cached cache stage retained index input }

/-- Construct actual old/new observations and one direct child Query, then consume those SAME caches in queryStrip.

This is genuine per-query work on a GIVEN original stage value, not a
memoized query service. Each answer and direct Query retains its whole
original factory; the member, source preparations, occurrence map and
Alignments are reused. No caller assembles an observation record.
-/
def queryStripAt : StripQueryAt cached cache stage retained index input inside :=
  let located := StripQueryCache.located (cached := cached) cache index
  let prepared : PreparedParent (parameter := parameter) (frame := frame) (basis := basis)
      (parent := (parent :: parents)[located.block.val]'located.block.isLt)
      (covered.entry located.block).val count floor (covered.entry located.block).property source.targets :=
    PreparedParents.entry (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (parents := parent :: parents) (covered := covered) (floor := floor)
      (original := chain.path) (stage := source.selected.stage) (targets := source.targets)
      source.prepared located.block
  let selected : PreparedParent (parameter := parameter + offset) (frame := cached.targetFrame) (basis := basis)
      (parent := (cached.member.requested.request.shape.val.1 ::
        cached.member.requested.request.shape.val.2)[index.val]'index.isLt)
      (cached.member.requested.request.covered.entry index).val count targetFloor
      (cached.member.requested.request.covered.entry index).property
      (CellEndpoints.Targets.build cached.member.requested.request.chain.path stage) :=
    PreparedParents.entry (parameter := parameter + offset) (frame := cached.targetFrame) (basis := basis)
      (count := count)
      (parents := cached.member.requested.request.shape.val.1 :: cached.member.requested.request.shape.val.2)
      (covered := cached.member.requested.request.covered) (floor := targetFloor)
      (original := cached.member.requested.request.chain.path) (stage := stage)
      (targets := CellEndpoints.Targets.build cached.member.requested.request.chain.path stage)
      retained.val.1.preparations index
  let time := ShiftedGeometry.Occurrence.sourceInput (whole := cached.member.geometry)
    (blocks := cached.member.blocks)
    (request := cached.member.requested.request) (sourceIndex := index) located input
  let localInside := (ShiftedGeometry.Occurrence.sourceInput_inside (whole := cached.member.geometry)
    (blocks := cached.member.blocks)
    (request := cached.member.requested.request) (sourceIndex := index) located input inside)
  let old := prepared.preparation.query.observe frame
    time localInside.1 localInside.2
  let observed := selected.preparation.query.observe cached.targetFrame input inside.1 inside.2
  let direct := PreparedEdge.Query.build ((cached.member.requested.request.shape.val.1 ::
    cached.member.requested.request.shape.val.2)[index.val]'index.isLt).edge input inside
  let compared := cached.queryStrip cache stage retained index input inside ⟨old, rfl⟩ ⟨observed, rfl⟩ direct
  ⟨⟨old, rfl⟩, ⟨observed, rfl⟩, ⟨direct, rfl⟩,
    ⟨compared, cached.stageKey_eq cache stage retained index input⟩⟩

end QueryAcquisition

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.LocalMember

end
