module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Queries
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.References
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Linked
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Accuracy
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Origin.Quotients
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Endpoints.Chain
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Queries
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Strip
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step.Source
import Purelib.Curves.Legendre.Periods.Jets.Basic
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet.Occurrences
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Comparison
import Purelib.Curves.Legendre.Periods.Jets.Connection
import Purelib.Curves.Legendre.Periods.Jets.PicardFuchs
import Purelib.Data.Gaussian.RationalEmbedding.Bounds
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.List.DependentProduct
meta import Purelib.Elab.ConstructiveInjectivity

/-! # One original source and actual member family before derivative accuracy

One original endpoint observation product and one zero member are bound
before the accuracy request. The executable member rule preserves those
caches and constructs each requested nonzero member once. It is a finite
per-input algorithm, not a precomputed or memoized family of geometries.
Every requested error receives a positive quadrance radius and actual
increment-dependent floors for all later geometric model readings. The
same retained interior query/Step/reference supplies the cross-time signed
triangle, without another observation, advancement or reference factory.
-/

public section

universe u

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent)}
    {current floor rootStage : Nat} {reference : AccuracyRequest}
    {source : Requested covered chain current floor rootStage reference}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}

attribute [local irreducible] LocalMember LocalMember.StripData in
set_option genInjectivity false in
/-- One actual member and its retained query cache share the original endpoint observations.

The member is the original complete LocalMember value. Its StripData
retains that same member's query cache and the given source observations;
the named container keeps this ownership boundary intact during compilation.
-/
structure StripMember
    (roots : RootChain (parent :: parents) root root)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)
    (observed : EndpointObservations source.prepared (by decide +kernel) (by decide +kernel))
    (offset : Canonical) (admitted : Norm.Basic.normSq offset ≤ allocation.bound) : Type _ where
  /-- The same complete member, including its generated Frame, jet and connection certificates. -/
  member : LocalMember source ranges allocation roots widths
    targetCurrent targetFloor targetRootStage offset admitted
  /-- The original observations and once-built interior query cache of that same member. -/
  data : LocalMember.StripData member
  /-- The retained observations are the given original source observation product. -/
  observed_eq : LocalMember.StripData.observed (cached := member) data = observed

attribute [local irreducible] LocalMember LocalMember.StripData in
constructive_injectivity StripMember

/-- Construct one actual member once and consume the GIVEN original observations in its once-built StripData. -/
def stripMember (source : Requested covered chain current floor rootStage reference)
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    {root : Named} (roots : RootChain (parent :: parents) root root)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)
    (observed : EndpointObservations source.prepared (by decide +kernel) (by decide +kernel))
    (offset : Canonical) (admitted : Norm.Basic.normSq offset ≤ allocation.bound) :
    StripMember roots widths targetCurrent targetFloor targetRootStage observed offset admitted :=
  let member := LocalMember.build source ranges allocation roots widths
    targetCurrent targetFloor targetRootStage offset admitted
  let data := LocalMember.StripData.ofObserved member observed
  ⟨member, data, LocalMember.StripData.ofObserved_observed member observed⟩

namespace StripMember

variable {observed : EndpointObservations source.prepared (by decide +kernel) (by decide +kernel)}
    {offset : Canonical} {admitted : Norm.Basic.normSq offset ≤ allocation.bound}

/-- Exact offset-index transport preserves the whole retained member and all of its existing caches. -/
def castOffset {first last : Canonical} (same : first = last)
    {firstPaid : Norm.Basic.normSq first ≤ allocation.bound} {lastPaid : Norm.Basic.normSq last ≤ allocation.bound}
    (retained : StripMember roots widths targetCurrent targetFloor targetRootStage
        observed first firstPaid) : StripMember roots widths targetCurrent targetFloor targetRootStage
            observed last lastPaid := by
  cases same
  exact retained

/-- The original complete member/cache value survives scalar offset transport heterogeneously. -/
theorem castOffset_heq {first last : Canonical} (same : first = last)
    {firstPaid : Norm.Basic.normSq first ≤ allocation.bound} {lastPaid : Norm.Basic.normSq last ≤ allocation.bound}
    (retained : StripMember roots widths targetCurrent targetFloor targetRootStage observed first firstPaid) :
    HEq (castOffset (lastPaid := lastPaid) same retained) retained := by
  cases same
  rfl

end StripMember

/-- Fix one executable member rule with the SAME given zero value and original shared observation product.

The zero branch transports the complete retained zero member/cache along
an exact scalar index equality. Every nonzero query executes the original
LocalMember.build once and then StripData.ofObserved once; no cache across
independent calls or equality with the original source Frame is asserted.
-/
def memberFamily
    (observed : EndpointObservations source.prepared (by decide +kernel) (by decide +kernel))
    {zeroPaid : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound}
    (zero : StripMember roots widths targetCurrent targetFloor targetRootStage observed 0 zeroPaid)
    (offset : Canonical) (admitted : Norm.Basic.normSq offset ≤ allocation.bound) :
    StripMember roots widths targetCurrent targetFloor targetRootStage observed offset admitted :=
  if atZero : offset = 0 then
    StripMember.castOffset (lastPaid := admitted) atZero.symm zero
  else
    stripMember source ranges allocation roots widths targetCurrent targetFloor targetRootStage observed offset admitted

/-- The executable zero branch reuses the SAME whole zero member/cache value. -/
theorem memberFamily_zero
    (observed : EndpointObservations source.prepared (by decide +kernel) (by decide +kernel))
    {zeroPaid : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound}
    (zero : StripMember roots widths targetCurrent targetFloor targetRootStage observed 0 zeroPaid)
    (admitted : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound) :
    HEq (memberFamily observed zero 0 admitted) zero := by
  unfold memberFamily
  rewrite [dif_pos rfl]
  rfl

namespace LocalMember

/-- Rational interpolation preserves the SAME global allocation, before any actual intermediate member is requested. -/
theorem interpolated_admitted (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ allocation.bound) :
    Norm.Basic.normSq ((⟨time, 0⟩ : Canonical) * increment) ≤ allocation.bound := by
  have scalar : Norm.Basic.normSq (⟨time, 0⟩ : Canonical) ≤ 1 :=
    (Norm.Basic.normSq_eq_canonical _).trans_le
      (RationalEmbedding.Bounds.unit_parameter timeInside.1 timeInside.2)
  have paid := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct scalar (Norm.Basic.normSq_nonneg increment)
  exact (Norm.Basic.normSq_mul _ _).trans_le ((paid.trans_eq (Field.one_mul _)).trans admitted)

/-- Every original endpoint section names the corresponding actual intermediate block's signed root. -/
@[expose] def InterpolatedEndpointSigns {increment : Canonical}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    (last : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage increment admitted)
    (observed : EndpointObservations source.prepared (by decide +kernel) (by decide +kernel))
    (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1)
    {intermediatePaid : Norm.Basic.normSq ((⟨time, 0⟩ : Canonical) * increment) ≤ allocation.bound}
    (intermediate : LocalMember source ranges allocation roots widths targetCurrent targetFloor targetRootStage
      ((⟨time, 0⟩ : Canonical) * increment) intermediatePaid)
    (actual : StripEndpointChain last observed time timeInside) : Type _ :=
    DependentProduct (parent :: parents) (fun index =>
      let pair := DependentProduct.get (parent :: parents) actual.1 index
      let block := DependentProduct.get (parent :: parents) intermediate.member.blocks index
      NamedEquivalent pair.1.2.val.root.value.name block.first.root.value.name ×
        NamedEquivalent pair.2.2.val.root.value.name block.last.root.value.name)

/-- The GIVEN time-section endpoint chain agrees at every original occurrence with the SAME actual intermediate member.

Both actual Steps start at identical retained original source Points. Their
common absolute offset and original source-root reflexivity derive every
comparison; the two member Frames and their complete caches stay distinct.
-/
def interpolatedEndpointSigns {increment : Canonical}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    (last : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage increment admitted)
    (observed : EndpointObservations source.prepared (by decide +kernel) (by decide +kernel))
    (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1)
    {intermediatePaid : Norm.Basic.normSq ((⟨time, 0⟩ : Canonical) * increment) ≤ allocation.bound}
    (intermediate : LocalMember source ranges allocation roots widths targetCurrent targetFloor targetRootStage
      ((⟨time, 0⟩ : Canonical) * increment) intermediatePaid)
    (actual : StripEndpointChain last observed time timeInside) :
    InterpolatedEndpointSigns last observed time timeInside intermediate actual :=
  DependentProduct.ofFn (parent :: parents) (fun index =>
    let pair := DependentProduct.get (parent :: parents) actual.1 index
    let block := DependentProduct.get (parent :: parents) intermediate.member.blocks index
    let first : Variation.Point.Step (source.prepared.entry index).firstSample
        ((⟨time, 0⟩ : Canonical) * increment) := pair.1.2.val
    let lastStep : Variation.Point.Step (source.prepared.entry index).lastSample
        ((⟨time, 0⟩ : Canonical) * increment) := pair.2.2.val
    let blockFirst : Variation.Point.Step (source.prepared.entry index).firstSample
        ((⟨time, 0⟩ : Canonical) * increment) := block.first
    let blockLast : Variation.Point.Step (source.prepared.entry index).lastSample
        ((⟨time, 0⟩ : Canonical) * increment) := block.last
    ⟨Variation.Point.Step.equivalent_of_source_eq (parameter := parameter)
        (increment := (⟨time, 0⟩ : Canonical) * increment)
        (firstCount := count) (lastCount := count)
        (firstPatch := (covered.entry index).val.neighborhood count)
        (lastPatch := (covered.entry index).val.neighborhood count)
        (firstSource := (source.prepared.entry index).firstSample)
        (lastSource := (source.prepared.entry index).firstSample)
        first blockFirst rfl
        (NamedEquivalent.refl (source.prepared.entry index).firstSample.certificate.value.name),
      Variation.Point.Step.equivalent_of_source_eq (parameter := parameter)
        (increment := (⟨time, 0⟩ : Canonical) * increment)
        (firstCount := count) (lastCount := count)
        (firstPatch := (covered.entry index).val.neighborhood count)
        (lastPatch := (covered.entry index).val.neighborhood count)
        (firstSource := (source.prepared.entry index).lastSample)
        (lastSource := (source.prepared.entry index).lastSample)
        lastStep blockLast rfl
        (NamedEquivalent.refl (source.prepared.entry index).lastSample.certificate.value.name)⟩)

section TimeQuery

attribute [local irreducible] LocalMember ShiftedGeometry.Occurrence.block
  PreparedParent.ShiftedAcquisition.Linked.first StripQueryCache.located StripQueryCache.aligned
  Shifted.requested ShiftedGeometry.Requested.request ShiftedGeometry.Request.shape

variable {increment : Canonical} {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    (last : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage increment admitted)
    (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1)
    {intermediatePaid : Norm.Basic.normSq ((⟨time, 0⟩ : Canonical) * increment) ≤ allocation.bound}
    (intermediate : LocalMember source ranges allocation roots widths targetCurrent targetFloor targetRootStage
      ((⟨time, 0⟩ : Canonical) * increment) intermediatePaid)
    (cache : StripQueryCache intermediate) (stage : Nat)
    (retained : { value : StageData intermediate stage // value = (intermediate.completed stage).val })
    (index : Fin (intermediate.member.requested.request.shape.val.1 ::
      intermediate.member.requested.request.shape.val.2).length)
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (query : StripQueryAt intermediate cache stage retained index input inside)

/-- The SAME actual intermediate query Step/reference form an original h,time strip section and target comparison. -/
@[expose] def InterpolatedQuerySection : Type _ :=
  let located := StripQueryCache.located (cached := intermediate) cache index
  let prepared : PreparedParent (parameter := parameter) (frame := frame) (basis := basis)
      (parent := (parent :: parents)[located.block.val]'located.block.isLt)
      (covered.entry located.block).val count floor (covered.entry located.block).property source.targets :=
    PreparedParents.entry (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (parents := parent :: parents) (covered := covered) (floor := floor)
      (original := chain.path) (stage := source.selected.stage) (targets := source.targets)
      source.prepared located.block
  let block := DependentProduct.get (parent :: parents) last.member.blocks located.block
  let old := query.1
  let localInside := located.sourceInput_inside input inside
  (sectionValue : PreparedParent.StripStep
    (parameter := parameter) (frame := frame) (basis := basis)
    (parent := (parent :: parents)[located.block.val]'located.block.isLt)
    (patch := (covered.entry located.block).val) (count := count) (floor := floor)
    (covered := (covered.entry located.block).property) (original := chain.path)
    (stage := source.selected.stage) (targets := source.targets)
    prepared (ranges.entry located.block)
    block.comparison.budget block.comparison.budget_eq (located.sourceInput input) localInside
    old.val old.property increment (admitted.trans (allocation.bound_le_entry located.block)) time timeInside) ×
  NamedEquivalent query.2.1.val.retained.sample.certificate.value.name sectionValue.1.val.root.value.name

/-- Close the actual cross-member reference triangle without recomputing a query, Step or reference Owner.

The given intermediate query uses its original block budget and actual
completed absolute Step. Both original budget factories identify the same
seedBudget. seedOwner_factory transports the SAME reference's whole factory
to the h-member budget, then compareStripReference consumes that retained
reference and Step. Exact offset indices and proof irrelevance retain its
original advance factory; no root or Frame equality is an admission.
-/
def interpolatedQuerySection : InterpolatedQuerySection last time timeInside intermediate
    cache stage retained index input inside query :=
  let located := StripQueryCache.located (cached := intermediate) cache index
  let prepared : PreparedParent (parameter := parameter) (frame := frame) (basis := basis)
      (parent := (parent :: parents)[located.block.val]'located.block.isLt)
      (covered.entry located.block).val count floor (covered.entry located.block).property source.targets :=
    PreparedParents.entry (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (parents := parent :: parents) (covered := covered) (floor := floor)
      (original := chain.path) (stage := source.selected.stage) (targets := source.targets)
      source.prepared located.block
  let range := ranges.entry located.block
  let firstBlock := DependentProduct.get (parent :: parents) intermediate.member.blocks located.block
  let lastBlock := DependentProduct.get (parent :: parents) last.member.blocks located.block
  let actual : StripQuery intermediate cache stage retained index input inside query.1 query.2.1 :=
    query.2.2.2.val
  let old := query.1
  let localInside := located.sourceInput_inside input inside
  let stripPaid := admitted.trans (allocation.bound_le_entry located.block)
  let sectionPaid := range.interpolated_admitted time timeInside increment stripPaid
  have referenceFactory := Variation.Point.Range.seedOwner_factory
    (parameter := parameter) (count := count) (patch := (covered.entry located.block).val.neighborhood count)
    (point := prepared.preparation.cell.models.coordinate.point (located.sourceInput input)) range
    firstBlock.comparison.budget lastBlock.comparison.budget
    firstBlock.comparison.budget_eq lastBlock.comparison.budget_eq
    (prepared.queryPoint_inside (located.sourceInput input) localInside)
    ((⟨time, 0⟩ : Canonical) * increment)
    (intermediatePaid.trans (allocation.bound_le_entry located.block)) sectionPaid
    actual.2.1.val actual.2.1.property
  have stepFactory : actual.1.val = PreparedParent.advanceRetained
      (parameter := parameter) (frame := frame) (basis := basis)
      (parent := (parent :: parents)[located.block.val]'located.block.isLt)
      (patch := (covered.entry located.block).val) (count := count) (floor := floor)
      (covered := (covered.entry located.block).property) (original := chain.path)
      (stage := source.selected.stage) (targets := source.targets)
      prepared range (located.sourceInput input) localInside
      old.val old.property ((⟨time, 0⟩ : Canonical) * increment)
      (sectionPaid.trans (range.stripBound_le_shiftedBound.trans range.shiftedBound_le_bound)) := actual.1.property
  let compared := PreparedParent.compareStripReference
    (parameter := parameter) (frame := frame) (basis := basis)
    (parent := (parent :: parents)[located.block.val]'located.block.isLt)
    (patch := (covered.entry located.block).val) (count := count) (floor := floor)
    (covered := (covered.entry located.block).property) (original := chain.path)
    (stage := source.selected.stage) (targets := source.targets)
    prepared range lastBlock.comparison.budget lastBlock.comparison.budget_eq
    (located.sourceInput input) localInside ((⟨time, 0⟩ : Canonical) * increment) sectionPaid
    actual.2.1.val referenceFactory old.val.retained.sample actual.1.val
  let sectionValue : PreparedParent.StripStep
      (parameter := parameter) (frame := frame) (basis := basis)
      (parent := (parent :: parents)[located.block.val]'located.block.isLt)
      (patch := (covered.entry located.block).val) (count := count) (floor := floor)
      (covered := (covered.entry located.block).property) (original := chain.path)
      (stage := source.selected.stage) (targets := source.targets) prepared range
      lastBlock.comparison.budget lastBlock.comparison.budget_eq (located.sourceInput input) localInside
      old.val old.property increment stripPaid time timeInside :=
    ⟨⟨actual.1.val, stepFactory⟩, ⟨actual.2.1.val, referenceFactory⟩, compared⟩
  ⟨sectionValue, actual.2.2.trans compared⟩

end TimeQuery

end LocalMember

section FamilyTransport

variable (observed : EndpointObservations source.prepared (by decide +kernel) (by decide +kernel))
    (members : (offset : Canonical) → (admitted : Norm.Basic.normSq offset ≤ allocation.bound) →
      StripMember roots widths targetCurrent targetFloor targetRootStage observed offset admitted)

/-- Actual whole-family endpoint transport retains both member-rule factories at every rational time. -/
@[expose] def EndpointTransport : Type _ :=
  (increment : Canonical) → (admitted : Norm.Basic.normSq increment ≤ allocation.bound) →
  (last : { value : StripMember roots widths targetCurrent targetFloor targetRootStage
      observed increment admitted // value = members increment admitted }) →
  (time : Rational) → (timeInside : 0 ≤ time ∧ time ≤ 1) →
  (intermediate : { value : StripMember roots widths targetCurrent targetFloor targetRootStage
      observed ((⟨time, 0⟩ : Canonical) * increment)
      (LocalMember.interpolated_admitted (allocation := allocation) time timeInside increment admitted) //
    value = members ((⟨time, 0⟩ : Canonical) * increment)
      (LocalMember.interpolated_admitted (allocation := allocation) time timeInside increment admitted) }) →
  (actual : LocalMember.StripEndpointChain last.val.member observed time timeInside) →
  LocalMember.InterpolatedEndpointSigns last.val.member observed time timeInside intermediate.val.member actual

/-- Derive all-time signs on GIVEN whole family values without invoking the member rule or any observation.

The actual endpoint chain retains its original next/return comparisons.
Both complete member values stay cached with their whole family-factory
identities; repeated and stationary original slots remain separate.
-/
def endpointTransport : EndpointTransport observed members :=
  fun _increment _admitted last time timeInside intermediate actual =>
    LocalMember.interpolatedEndpointSigns last.val.member observed time timeInside intermediate.val.member actual

/-- Actual whole-family interior transport uses the retained query, completed Step and reference at each time. -/
@[expose] def QueryTransport : Type _ :=
  (increment : Canonical) → (admitted : Norm.Basic.normSq increment ≤ allocation.bound) →
  (last : { value : StripMember roots widths targetCurrent targetFloor targetRootStage
      observed increment admitted // value = members increment admitted }) →
  (time : Rational) → (timeInside : 0 ≤ time ∧ time ≤ 1) →
  (intermediate : { value : StripMember roots widths targetCurrent targetFloor targetRootStage
      observed ((⟨time, 0⟩ : Canonical) * increment)
      (LocalMember.interpolated_admitted (allocation := allocation) time timeInside increment admitted) //
    value = members ((⟨time, 0⟩ : Canonical) * increment)
      (LocalMember.interpolated_admitted (allocation := allocation) time timeInside increment admitted) }) →
  (stage : Nat) →
  (retained : { value : LocalMember.StageData intermediate.val.member stage //
    value = (intermediate.val.member.completed stage).val }) →
  (index : Fin (intermediate.val.member.member.requested.request.shape.val.1 ::
    intermediate.val.member.member.requested.request.shape.val.2).length) →
  (input : Rational) → (inside : 0 ≤ input ∧ input ≤ 1) →
  (query : LocalMember.StripQueryAt intermediate.val.member
    (LocalMember.StripData.queries (cached := intermediate.val.member) intermediate.val.data)
    stage retained index input inside) →
  LocalMember.InterpolatedQuerySection last.val.member time timeInside intermediate.val.member
    (LocalMember.StripData.queries (cached := intermediate.val.member) intermediate.val.data)
    stage retained index input inside query

/-- Close the actual cross-member query/reference triangle on the SAME two supplied family caches.

The input query retains its original source and shifted observations,
completed stage factory, actual absolute Step and reference. The result
changes only the reference's budget factory to the identical original seed
and derives its comparison with that SAME completed Step.
-/
def queryTransport : QueryTransport observed members :=
  fun _increment _admitted last time timeInside intermediate stage retained index input inside query =>
    LocalMember.interpolatedQuerySection last.val.member time timeInside intermediate.val.member
      (LocalMember.StripData.queries (cached := intermediate.val.member) intermediate.val.data)
      stage retained index input inside query

end FamilyTransport

section Selection

variable (completed : source.attempt.OccurrenceFamily)
    (sourceActual : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet)
    (sourceFactory : sourceActual = OccurrenceCompletion.build (parameter := parameter) (frame := frame)
      (basis := basis) (count := count) (floor := floor) (rootStage := rootStage)
      covered chain (fun stage => (completed stage).val))
    (observed : EndpointObservations source.prepared (by decide +kernel) (by decide +kernel))
    {zeroPaid : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound}
    (zero : StripMember roots widths targetCurrent targetFloor targetRootStage observed 0 zeroPaid)
    (members : (offset : Canonical) → (admitted : Norm.Basic.normSq offset ≤ allocation.bound) →
      StripMember roots widths targetCurrent targetFloor targetRootStage observed offset admitted)

/-- One computed positive radius and its actual member/floor selections for EVERY admitted nonzero increment.

The source bundle, zero value, shared observations and executable member
rule precede accuracy. Each requested increment retains one complete
member/data value, its whole member-rule equation, the genuine origin and
fresh quotient selections, and the all-later four-row model bounds.
-/
@[expose] def FamilyAccuracy (accuracy : AccuracyRequest) (originStart : Nat) : Type _ :=
  (radius : { value : AccuracyRequest // value = LocalMember.sourceQuotientRequest
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered)
    (ranges := ranges) (allocation := allocation) accuracy }) ×
  ((increment : Canonical) → (nonzero : increment ≠ 0) →
    (admitted : Norm.Basic.normSq increment ≤ allocation.bound) →
    (given : { value : StripMember roots widths targetCurrent targetFloor targetRootStage
        observed increment admitted // value = members increment admitted }) →
    (_small : Norm.Basic.normSq increment ≤ radius.val.tolerance) →
    (retained : { value : StripMember roots widths targetCurrent targetFloor targetRootStage
        observed increment admitted // value = given.val }) ×
    { paid : LocalMember.SourceQuotientFloors
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage)
      sourceActual.1 zero.member retained.val.member accuracy nonzero originStart //
      LocalMember.StageQuotientBounds retained.val.member sourceActual.1 accuracy paid.2.2.val.1 paid.2.2.val.2 })

attribute [local irreducible] ShiftedGeometry.Occurrence.block
  PreparedParent.ShiftedAcquisition.Linked.first LocalMember.StripQueryCache.located
  LocalMember.StripQueryCache.aligned Shifted.requested ShiftedGeometry.Requested.request
  ShiftedGeometry.Request.shape

include completed sourceFactory in
/-- Choose the positive family radius and derive increment-dependent floors for every later original model reading.

The member rule is fixed before accuracy. Each invocation consumes a GIVEN
once-bound whole member/data and returns it unchanged beside the original
quotient selection. The source jet is read from the GIVEN complete build
bundle; neither member nor its connection/PF constructors run here.
-/
def selectFamily (firstStart lastStart freshStart originStart : Nat) (spatial : AccuracyRequest)
    (accuracy : AccuracyRequest) : FamilyAccuracy
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) sourceActual observed zero members accuracy originStart :=
  let radius : AccuracyRequest := LocalMember.sourceQuotientRequest
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered)
    (ranges := ranges) (allocation := allocation) accuracy
  ⟨⟨radius, rfl⟩, fun increment nonzero admitted given small =>
    let retained : StripMember (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (parent := parent) (parents := parents) (covered := covered) (chain := chain)
        (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
        (source := source) (ranges := ranges) (allocation := allocation) (root := root)
        roots widths targetCurrent targetFloor targetRootStage observed increment admitted := given.val
    have sourceJetFactory : sourceActual.1 = OccurrenceCompletion.jet
        (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (floor := floor) (rootStage := rootStage) covered chain (fun stage => (completed stage).val) :=
      (congrArg (fun value : (jet : SynchronizedPeriodJet frame) ×
        Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet => value.1)
        sourceFactory).trans (OccurrenceCompletion.build_jet
          (parameter := parameter) (frame := frame) (basis := basis) (count := count)
          (floor := floor) (rootStage := rootStage) covered chain (fun stage => (completed stage).val))
    let paid : LocalMember.SourceQuotientFloors
        (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (parent := parent) (parents := parents) (covered := covered) (chain := chain)
        (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
        (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
        (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
        (targetRootStage := targetRootStage) sourceActual.1 zero.member retained.member accuracy nonzero originStart :=
      LocalMember.sourceQuotientFloors
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage)
      completed sourceActual.1 sourceJetFactory zero.member retained.member accuracy nonzero
      (small.trans (LocalMember.sourceQuotientRequest_le_reference
        (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (parent := parent) (parents := parents) (covered := covered)
        (ranges := ranges) (allocation := allocation) accuracy))
      firstStart lastStart freshStart originStart spatial
    have accurate : LocalMember.StageQuotientBounds retained.member sourceActual.1 accuracy
        paid.2.2.val.1 paid.2.2.val.2 :=
      LocalMember.stageQuotient_lt (offset := increment) (admitted := admitted) (zeroAdmitted := zeroPaid)
        (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (parent := parent) (parents := parents) (covered := covered) (chain := chain)
        (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
        (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
        (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
        (targetRootStage := targetRootStage)
        retained.member sourceActual.1 zero.member accuracy nonzero originStart paid
    ⟨⟨retained, rfl⟩, ⟨paid, accurate⟩⟩⟩

/-- The exact family assertion with its original computed positive-radius operation kept explicit.

The actual member rule precedes accuracy. Its radius, every admitted
nonzero increment and all sufficiently late original readings stay ordered.
-/
@[expose] def FamilyBoundsWith (request : AccuracyRequest → AccuracyRequest) : Prop :=
    ∀ accuracy : AccuracyRequest,
      ∃ radius : { value : AccuracyRequest // value = request accuracy },
        0 < radius.val.tolerance ∧
        ∀ (increment : Canonical) (_nonzero : increment ≠ 0)
          (admitted : Norm.Basic.normSq increment ≤ allocation.bound)
          (given : { value : StripMember roots widths targetCurrent targetFloor targetRootStage
              observed increment admitted // value = members increment admitted }),
          Norm.Basic.normSq increment ≤ radius.val.tolerance →
          ∃ retained : StripMember roots widths targetCurrent targetFloor targetRootStage observed increment admitted,
            retained = given.val ∧
            ∃ firstFloor lastFloor : Nat,
              LocalMember.StageQuotientBounds retained.member sourceActual.1 accuracy firstFloor lastFloor

/-- The finite derivative assertion for one fixed executable member family and actual source bundle. -/
@[expose] def FamilyBounds : Prop :=
  FamilyBoundsWith
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
    (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) (sourceActual := sourceActual) (observed := observed) (members := members)
    (fun accuracy => LocalMember.sourceQuotientRequest
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered)
      (ranges := ranges) (allocation := allocation) accuracy)

include completed sourceFactory zero in
/-- One fixed actual member family has a computed positive radius and paid all-later model quotients for every epsilon.

The quantified increment is arbitrary inside that radius, not one chosen
favorable example. Its finite floors may depend on that nonzero increment.
Actual stage values retain their original whole completed-family equations;
source and generated target Frames remain independent nominal owners.
-/
theorem family_accurate (firstStart lastStart freshStart originStart : Nat) (spatial : AccuracyRequest) :
    FamilyBounds
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage)
      (sourceActual := sourceActual) (observed := observed) (members := members) := by
  intro accuracy
  let selected : FamilyAccuracy
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) sourceActual observed zero members accuracy originStart :=
    selectFamily
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
    (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) completed sourceActual sourceFactory observed zero members
    firstStart lastStart freshStart originStart spatial accuracy
  refine ⟨selected.1, selected.1.val.positive, ?_⟩
  intro increment nonzero admitted given small
  let actual := selected.2 increment nonzero admitted given small
  let paid := actual.2
  exact ⟨actual.1.val, actual.1.property, paid.val.2.2.val.1, paid.val.2.2.val.2, paid.property⟩

end Selection

section Producer

attribute [local irreducible] ShiftedGeometry.Occurrence.block
  PreparedParent.ShiftedAcquisition.Linked.first LocalMember.StripQueryCache.located
  LocalMember.StripQueryCache.aligned Shifted.requested ShiftedGeometry.Requested.request
  ShiftedGeometry.Request.shape
  stripMember memberFamily

variable (completed : source.attempt.OccurrenceFamily)
    (sourceActual : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet)
    (sourceFactory : sourceActual = OccurrenceCompletion.build (parameter := parameter) (frame := frame)
      (basis := basis) (count := count) (floor := floor) (rootStage := rootStage)
      covered chain (fun stage => (completed stage).val))
    (firstStart lastStart freshStart originStart : Nat) (spatial : AccuracyRequest)

/-- The exact dependent result on the original kept source, observations, zero and executable member rule.

All endpoint/query transport and original numerical fields stay in the
shared consumer telescope. The tail only names these four actual caches.
-/
@[expose] def FamilyTail : Type _ :=
  (keptSource : { value : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet //
    value = sourceActual }) →
  (observed : EndpointObservations source.prepared (by decide +kernel) (by decide +kernel)) →
  let zeroPaid : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound :=
    (Norm.Basic.normSq_zero).trans_le allocation.bound_positive.le
  (zero : StripMember roots widths targetCurrent targetFloor targetRootStage observed 0 zeroPaid) →
  (members : (offset : Canonical) → (admitted : Norm.Basic.normSq offset ≤ allocation.bound) →
    StripMember roots widths targetCurrent targetFloor targetRootStage observed offset admitted) →
  Type u

/-- Retain the original complete family consumer with a result on its SAME four retained cache values.

All old geometric witnesses, programme selections and derivative bounds
precede the tail; no cache or argument is replaced by a copied context.
-/
@[expose] def FamilyConsumerWith
    (Finish : FamilyTail.{u}
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
    (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) (sourceActual := sourceActual)) : Type _ :=
  (keptSource : { value : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet //
    value = sourceActual }) →
  (observed : EndpointObservations source.prepared (by decide +kernel) (by decide +kernel)) →
  let zeroPaid : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound :=
    (Norm.Basic.normSq_zero).trans_le allocation.bound_positive.le
  (zero : StripMember roots widths targetCurrent targetFloor targetRootStage observed 0 zeroPaid) →
  (members : (offset : Canonical) → (admitted : Norm.Basic.normSq offset ≤ allocation.bound) →
    StripMember roots widths targetCurrent targetFloor targetRootStage observed offset admitted) →
  (_membersFactory : members = memberFamily observed zero) →
  EndpointTransport
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
    (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) observed members →
  QueryTransport
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
    (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) observed members →
  ((accuracy : AccuracyRequest) → FamilyAccuracy
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
    (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) keptSource.val observed zero members accuracy originStart) →
  FamilyBounds
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
    (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage)
    (sourceActual := keptSource.val) (observed := observed) (members := members) →
    Finish keptSource observed zero members

/-- The original full source bundle, shared observations, one zero cache and actual pre-epsilon member rule.

The dependent continuation receives the actual values, not copied context
fields. The per-error selector consumes GIVEN once-bound family members and
returns them unchanged beside their new finite numerical selections. The
last proposition states the full radius/increment/all-later quantifiers.
-/
@[expose] def FamilyConsumer (Result : Type u) : Type _ :=
  FamilyConsumerWith.{u}
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
    (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) (sourceActual := sourceActual)
    (originStart := originStart)
    (fun _ _ _ _ => Result)

include completed sourceFactory firstStart lastStart freshStart spatial in
/-- Bind shared observations and one genuine zero member before exposing the complete actual family accuracy theorem.

The GIVEN complete source bundle is returned unchanged. LocalMember.build
and StripData.ofObserved run once for the original zero cache; every
nonzero member is constructed only when the fixed rule is invoked. The
selector never invokes that rule or either ofJet constructor: it consumes
and returns the same supplied whole member/cache for each new epsilon.
-/
def withVariationFamily {Result : Type u}
    (consume : FamilyConsumer
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage)
      (sourceActual := sourceActual) (originStart := originStart) Result) : Result :=
  let observed : EndpointObservations
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parents := parent :: parents) (covered := covered) (floor := floor)
      (path := chain.path) (stage := source.selected.stage) (targets := source.targets)
      source.prepared (by decide +kernel) (by decide +kernel) :=
    EndpointObservations.build
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parents := parent :: parents) (covered := covered) (floor := floor)
      (path := chain.path) (stage := source.selected.stage) (targets := source.targets)
      source.prepared (by decide +kernel) (by decide +kernel)
  have zeroPaid : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound :=
    (Norm.Basic.normSq_zero).trans_le allocation.bound_positive.le
  let zero : StripMember (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root)
      roots widths targetCurrent targetFloor targetRootStage observed 0 zeroPaid :=
    stripMember source ranges allocation roots widths
    targetCurrent targetFloor targetRootStage observed 0 zeroPaid
  let members : (offset : Canonical) → (admitted : Norm.Basic.normSq offset ≤ allocation.bound) →
      StripMember (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (parent := parent) (parents := parents) (covered := covered) (chain := chain)
        (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
        (source := source) (ranges := ranges) (allocation := allocation) (root := root)
        roots widths targetCurrent targetFloor targetRootStage observed offset admitted :=
    memberFamily observed zero
  let endpoints : EndpointTransport
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
    (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) observed members :=
    endpointTransport
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) observed members
  let queries : QueryTransport
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
    (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) observed members :=
    queryTransport
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) observed members
  consume ⟨sourceActual, rfl⟩ observed zero members rfl endpoints queries
    (fun accuracy => selectFamily
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) completed sourceActual sourceFactory observed zero members
      firstStart lastStart freshStart originStart spatial accuracy)
    (family_accurate
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) completed sourceActual sourceFactory observed zero members
      firstStart lastStart freshStart originStart spatial)

end Producer

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

end
