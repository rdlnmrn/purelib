module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Jets.Source
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Origin.Quotients
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Geometry
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Endpoints.Chain
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Queries
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Strip
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Geometry.Path.Gaussian.Lifted.Closed
import Purelib.Data.List.DependentProduct
import Purelib.Curves.Legendre.Periods.Jets.Source.Observations

import Purelib.Riemann.Periods.PreparedGridPeriodPrograms

/-! # Finite variation of the retained source family anchored on original A and corrected-B walks

One given original source jet and the given zero/increment members precede
accuracy. The original canonical value attachment executes once; the source
quotient producer executes once. The callback retains those whole values
and the same member's actual joined-cycle, Stage and six model certificates.

Both anchors are the actual PolynomialValues on the retained initial walk.
Value zero additionally agrees with the independently stored holomorphic
programme. No cap-period equality, raw canonical schedule realization,
fresh canonical endpoint basis or geometric monodromy is inferred.
-/

public section

universe u

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Jets (UniformPathCertificates)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell (PreparedParents PreparedParent)
open Purelib.Curves.Legendre.Periods.Jets.Source (CellModels)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents
  (ParameterRange constantCycle)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt (Requested OccurrenceCompletion)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested (LocalMember)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Geometry.Path.Gaussian.Lifted.Closed (ClosedLiftedPath)
open Purelib.Geometry.Path.Gaussian.Lifted.Refinement (LiftedCycleRefinement)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Periods
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk (PolynomialValues)
open Purelib.Riemann.Topology.PreparedBankRootChains (ownerName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

section OriginalWalk

variable {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {point : Canonical}
    {rootOwner : Owner ((Fibre.frameCurve frame).polynomial.eval point)} {source : Differential 1}
    {walk : PeriodWalk grid point rootOwner source} {valueFloor : Nat}
    (values : PolynomialValues walk valueFloor)
    {parent : CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1))}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1)))}
    (same : values.1.parents = parent :: parents) {current floor rootStage : Nat} {reference : AccuracyRequest}
    (requested : Requested (values.1.sourceCovered same) (values.1.sourceChain same) current floor rootStage reference)
    (completed : requested.attempt.OccurrenceFamily) (actual : SynchronizedPeriodJet frame)
    (factory : actual = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor) (rootStage := rootStage)
      (values.1.sourceCovered same) (values.1.sourceChain same) (fun stage => (completed stage).val))
    {ranges : ParameterRange (values.1.sourceCovered same)} {allocation : ParameterRange.StripAllocation ranges}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat} {increment : Canonical}
    {zeroAdmitted : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    (zero : LocalMember requested ranges allocation (values.1.sourceRoots same) widths
      targetCurrent targetFloor targetRootStage 0 zeroAdmitted)
    (last : LocalMember requested ranges allocation (values.1.sourceRoots same) widths
      targetCurrent targetFloor targetRootStage increment admitted)
    (retained : LocalMember.StripData last)

/-- The original base attachment and actual source quotient cache accompany the same joined-cycle model certificates.

The two members are the supplied original caches, fixed before accuracy.
The given endpoint/interior StripData precedes accuracy and is returned
unchanged. Both source and shifted cycle witnesses retain their actual
model lists and all six certificates. Actual rational-time endpoint chains,
GIVEN-chain time-one signs and fresh per-query interior comparisons consume
those same caches. The actual paid quotient certificate applies to every
later given stage model; no final accuracy or signed relation is assumed.
-/
abbrev SourceVariationTail (accuracy : AccuracyRequest) (nonzero : increment ≠ 0)
    (originStart : Nat) (Result : Type u) : Type _ :=
  (paid : LocalMember.SourceQuotientFloors (parameter := parameter) (frame := frame)
    (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1)
    (parent := parent) (parents := parents) (covered := values.1.sourceCovered same)
    (chain := values.1.sourceChain same)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := requested) (ranges := ranges) (allocation := allocation) (root := ownerName rootOwner)
    (roots := values.1.sourceRoots same) (widths := widths)
    (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
    actual zero last accuracy nonzero originStart) →
  (kept : { value : LocalMember.StripData last // value = retained }) →
  (∀ stage, actual.cycle.liftedPath stage =
    (constantCycle (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (values.1.sourceChain same)).liftedPath stage) →
  (∀ coordinate stage, UniformPathCertificates (Fibre.frameCurve frame)
    (Jets.Specification.valueSpecification parameter coordinate)
    (((actual.value coordinate).integral.model stage).cells) (values.1.sourceChain same).path) →
  (∀ coordinate stage, UniformPathCertificates (Fibre.frameCurve frame)
    (Jets.Specification.firstDerivativeSpecification parameter coordinate)
    (((actual.first coordinate).integral.model stage).cells) (values.1.sourceChain same).path) →
  (∀ coordinate stage, UniformPathCertificates (Fibre.frameCurve frame)
    (Jets.Specification.secondDerivativeSpecification parameter coordinate)
    (((actual.second coordinate).integral.model stage).cells) (values.1.sourceChain same).path) →
  (∀ stage, last.jet.cycle.liftedPath stage =
    (constantCycle (parameter := parameter + increment) (frame := last.targetFrame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) last.member.geometry.chain).liftedPath stage) →
  (∀ stage, HEq (last.jet.source.stages stage) (last.completed stage).val.2.stage) →
  (∀ coordinate stage, UniformPathCertificates (Fibre.frameCurve last.targetFrame)
    (Jets.Specification.valueSpecification (parameter + increment) coordinate)
    (((last.jet.value coordinate).integral.model stage).cells) last.member.geometry.chain.path) →
  (∀ coordinate stage, UniformPathCertificates (Fibre.frameCurve last.targetFrame)
    (Jets.Specification.firstDerivativeSpecification (parameter + increment) coordinate)
    (((last.jet.first coordinate).integral.model stage).cells) last.member.geometry.chain.path) →
  (∀ coordinate stage, UniformPathCertificates (Fibre.frameCurve last.targetFrame)
    (Jets.Specification.secondDerivativeSpecification (parameter + increment) coordinate)
    (((last.jet.second coordinate).integral.model stage).cells) last.member.geometry.chain.path) →
  ((outer : Fin (parent :: parents).length) →
    let prepared := requested.prepared.entry outer
    let linked := DependentProduct.get (parent :: parents) last.member.blocks outer
    (fraction : Rational) → (inside : 0 ≤ fraction ∧ fraction ≤ 1) →
    (observed : CellModels.Observations frame
      (PreparedParent.liftedCell ((parent :: parents)[outer.val]'outer.isLt))
      prepared.preparation.cell.models prepared.preparation.query.requests fraction) →
    (observed_eq : observed = prepared.preparation.query.observe frame fraction inside.1 inside.2) →
    (time : Rational) → (timeInside : 0 ≤ time ∧ time ≤ 1) →
    PreparedParent.StripStep (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (parent := (parent :: parents)[outer.val]'outer.isLt)
      (patch := ((values.1.sourceCovered same).entry outer).val) (count := 1) (floor := floor)
      (covered := ((values.1.sourceCovered same).entry outer).property)
      (original := (values.1.sourceChain same).path) (stage := requested.selected.stage) (targets := requested.targets)
      prepared (ranges.entry outer) linked.comparison.budget linked.comparison.budget_eq
      fraction inside observed observed_eq increment (admitted.trans (allocation.bound_le_entry outer))
      time timeInside) →
  ((time : Rational) → (timeInside : 0 ≤ time ∧ time ≤ 1) →
    LocalMember.StripEndpointChain last (LocalMember.StripData.observed (cached := last) kept.val) time timeInside) →
  ((chain : LocalMember.StripEndpointChain last
      (LocalMember.StripData.observed (cached := last) kept.val) 1 (by decide +kernel)) →
    LocalMember.StripEndpointSigns last (LocalMember.StripData.observed (cached := last) kept.val) chain.1) →
  ((chain : LocalMember.StripEndpointChain last
      (LocalMember.StripData.observed (cached := last) kept.val) 0 (by decide +kernel)) →
    LocalMember.StripData.EndpointOrigins (cached := last) kept.val chain) →
  ((stage : Nat) →
    (stageValue : { value : LocalMember.StageData last stage // value = (last.completed stage).val }) →
    (index : Fin (last.member.requested.request.shape.val.1 :: last.member.requested.request.shape.val.2).length) →
    (input : Rational) → (inside : 0 ≤ input ∧ input ≤ 1) →
    LocalMember.StripQueryAt last (LocalMember.StripData.queries (cached := last) kept.val)
      stage stageValue index input inside) →
  LocalMember.StageQuotientBounds last actual accuracy paid.2.2.val.1 paid.2.2.val.2 → Result

/-- The actual original base attachment precedes the shared finite variation callback tail. -/
abbrev SourceVariationConsumer
    (expected : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet)
    (attachment : ValueAttachment values expected) (accuracy : AccuracyRequest) (nonzero : increment ≠ 0)
    (originStart : Nat) (Result : Type u) : Type _ :=
  SourceValueAttachment values expected attachment actual →
    SourceVariationTail values same requested actual zero last retained accuracy nonzero originStart Result

include completed factory in
/-- Derive the requested variation once on the same retained members after its actual base attachment is consumed. -/
private def withVariation
    (accuracy : AccuracyRequest) (nonzero : increment ≠ 0)
    (small : Norm.Basic.normSq increment ≤
      (LocalMember.sourceQuotientRequest (parameter := parameter) (frame := frame)
        (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1)
        (covered := values.1.sourceCovered same) (allocation := allocation) accuracy).tolerance)
    (firstStart lastStart freshStart originStart : Nat) (spatial : AccuracyRequest) {Result : Type u}
    (consume : SourceVariationTail values same requested actual zero last retained
      accuracy nonzero originStart Result) : Result :=
  let paid := LocalMember.sourceQuotientFloors (parameter := parameter) (frame := frame)
    (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1)
    (parent := parent) (parents := parents) (covered := values.1.sourceCovered same)
    (chain := values.1.sourceChain same)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := requested) (ranges := ranges) (allocation := allocation) (root := ownerName rootOwner)
    (roots := values.1.sourceRoots same) (widths := widths)
    (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
    completed actual factory zero last accuracy nonzero
    (small.trans (LocalMember.sourceQuotientRequest_le_reference (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1)
      (covered := values.1.sourceCovered same) (allocation := allocation) accuracy))
    firstStart lastStart freshStart originStart spatial
  have sourceCycle : actual.cycle = constantCycle (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (values.1.sourceChain same) :=
    (congrArg (fun jet : SynchronizedPeriodJet frame => jet.cycle) factory).trans
      (OccurrenceCompletion.jet_cycle (parameter := parameter) (frame := frame)
        (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor) (rootStage := rootStage)
        (values.1.sourceCovered same) (values.1.sourceChain same) (fun stage => (completed stage).val))
  have sourceAt (stage : Nat) : actual.cycle.liftedPath stage =
      (constantCycle (parameter := parameter) (frame := frame)
        (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (values.1.sourceChain same)).liftedPath stage :=
    congrArg (fun cycle : LiftedCycleRefinement 2 => cycle.liftedPath stage) sourceCycle
  have accurate : LocalMember.StageQuotientBounds last actual accuracy paid.2.2.val.1 paid.2.2.val.2 := by
    intro order coordinate firstIndex lastIndex firstAfter lastAfter stageValue stageFactory
    exact LocalMember.stageQuotient_lt
      (parameter := parameter) (frame := frame) (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1)
      (parent := parent) (parents := parents) (covered := values.1.sourceCovered same)
      (chain := values.1.sourceChain same) (current := current) (floor := floor) (rootStage := rootStage)
      (reference := reference) (source := requested) (ranges := ranges) (allocation := allocation)
      (root := ownerName rootOwner) (roots := values.1.sourceRoots same) (widths := widths)
      (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
      last actual zero accuracy nonzero originStart paid order coordinate firstIndex lastIndex
      firstAfter lastAfter stageValue stageFactory
  consume paid ⟨retained, rfl⟩ sourceAt
    (fun coordinate stage =>
      Eq.mp (congrArg (fun path : ClosedLiftedPath 2 => UniformPathCertificates (Fibre.frameCurve frame)
        (Jets.Specification.valueSpecification parameter coordinate)
        (((actual.value coordinate).integral.model stage).cells) path.path) (sourceAt stage))
        ((actual.value coordinate).certificates stage))
    (fun coordinate stage =>
      Eq.mp (congrArg (fun path : ClosedLiftedPath 2 => UniformPathCertificates (Fibre.frameCurve frame)
        (Jets.Specification.firstDerivativeSpecification parameter coordinate)
        (((actual.first coordinate).integral.model stage).cells) path.path) (sourceAt stage))
        ((actual.first coordinate).certificates stage))
    (fun coordinate stage =>
      Eq.mp (congrArg (fun path : ClosedLiftedPath 2 => UniformPathCertificates (Fibre.frameCurve frame)
        (Jets.Specification.secondDerivativeSpecification parameter coordinate)
        (((actual.second coordinate).integral.model stage).cells) path.path) (sourceAt stage))
        ((actual.second coordinate).certificates stage))
    (fun stage => last.cycle_at stage) (fun stage => last.stage_heq stage)
    (fun coordinate stage => last.valueCertificates coordinate stage)
    (fun coordinate stage => last.firstCertificates coordinate stage)
    (fun coordinate stage => last.secondCertificates coordinate stage)
    (fun outer fraction inside observed observed_eq time timeInside =>
      let prepared := requested.prepared.entry outer
      let linked := DependentProduct.get (parent :: parents) last.member.blocks outer
      PreparedParent.advanceStripAt (parameter := parameter) (frame := frame)
        (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (parent := (parent :: parents)[outer.val]'outer.isLt)
        (patch := ((values.1.sourceCovered same).entry outer).val) (count := 1) (floor := floor)
        (covered := ((values.1.sourceCovered same).entry outer).property)
        (original := (values.1.sourceChain same).path) (stage := requested.selected.stage)
        (targets := requested.targets)
        prepared (ranges.entry outer) linked.comparison.budget linked.comparison.budget_eq
        fraction inside observed observed_eq increment (admitted.trans (allocation.bound_le_entry outer))
        time timeInside)
    (fun time timeInside =>
      last.stripEndpointChain (LocalMember.StripData.observed (cached := last) retained) time timeInside)
    (fun chain => last.stripEndpointSigns (LocalMember.StripData.observed (cached := last) retained) chain.1)
    (fun chain => LocalMember.StripData.endpointOrigins (cached := last) retained chain)
    (fun stage stageValue index input inside =>
      last.queryStripAt (LocalMember.StripData.queries (cached := last) retained) stage stageValue index input inside)
    accurate

end OriginalWalk

/-- Derive finite source-family variation anchored to both original A polynomial values and old value zero.

The given source completion/jet, zero/increment members and StripData
precede accuracy. Its named builder runs outside this operation and the
same caches can be reused for another accuracy. One original aSourceValueAttachment
and one source quotient producer execute. Requested quotient comparisons
perform fresh numerical work on the given source and member geometry. The
second value is certified x dx/y on this actual retained cycle, with no
independent reciprocal-cap or raw canonical schedule identification.
-/
def withASourceVariation {parameter : Canonical} {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher} {lifted : LiftedPuncturedGrid base}
    {bank : BasedBranchBank lifted} {sheet : Fin 2}
    {ordered : BasedBranchBank.Ordered bank sheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}
    (prepared : Prepared paired) (index : Fin 1) {valueFloor : Nat}
    (values : PolynomialValues (parameter := parameter) (frame := frame) (prepared.aWalk index) valueFloor)
    {parent : CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1))}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1)))}
    (same : values.1.parents = parent :: parents) {current floor rootStage : Nat} {reference : AccuracyRequest}
    (requested : Requested (values.1.sourceCovered same) (values.1.sourceChain same) current floor rootStage reference)
    (completed : requested.attempt.OccurrenceFamily) (actual : SynchronizedPeriodJet frame)
    (factory : actual = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor) (rootStage := rootStage)
      (values.1.sourceCovered same) (values.1.sourceChain same) (fun stage => (completed stage).val))
    (ranges : ParameterRange (values.1.sourceCovered same)) (allocation : ParameterRange.StripAllocation ranges)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    {targetCurrent targetFloor targetRootStage : Nat} {increment : Canonical}
    {zeroAdmitted : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    (zero : LocalMember requested ranges allocation (values.1.sourceRoots same) widths
      targetCurrent targetFloor targetRootStage 0 zeroAdmitted)
    (last : LocalMember requested ranges allocation (values.1.sourceRoots same) widths
      targetCurrent targetFloor targetRootStage increment admitted)
    (retained : LocalMember.StripData last)
    (accuracy : AccuracyRequest) (nonzero : increment ≠ 0)
    (small : Norm.Basic.normSq increment ≤
      (LocalMember.sourceQuotientRequest (parameter := parameter) (frame := frame)
        (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1)
        (covered := values.1.sourceCovered same) (allocation := allocation) accuracy).tolerance)
    (firstStart lastStart freshStart originStart : Nat) (spatial : AccuracyRequest) {Result : Type u}
    (consume : SourceVariationConsumer (parameter := parameter) (frame := frame) (walk := prepared.aWalk index)
      (parent := parent) (parents := parents) (current := current) (floor := floor) (rootStage := rootStage)
      (reference := reference) (ranges := ranges) (allocation := allocation) (widths := widths)
      (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
      values same requested actual zero last retained
      (prepared.aOccurrenceJet index values floor rootStage (values.1.sourcePreparations same requested))
      (prepared.aValueAttachment index values floor rootStage (values.1.sourcePreparations same requested))
      accuracy nonzero originStart Result) : Result :=
  let anchored := prepared.aSourceValueAttachment index values same requested completed actual factory
  withVariation (parameter := parameter) (frame := frame) (walk := prepared.aWalk index)
    (parent := parent) (parents := parents) (current := current) (floor := floor) (rootStage := rootStage)
    (reference := reference) (ranges := ranges) (allocation := allocation) (widths := widths)
    (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
    values same requested completed actual factory zero last retained
    accuracy nonzero small firstStart lastStart freshStart originStart spatial (consume anchored)

/-- Derive finite source-family variation anchored to both original corrected-B polynomial values and old value zero.

The given source completion/jet, zero/increment members and StripData
precede accuracy. Its named builder runs outside this operation and the
same caches can be reused for another accuracy. One original bSourceValueAttachment
and one source quotient producer execute. Requested quotient comparisons
perform fresh numerical work on the given source and member geometry. The
second value is certified x dx/y on this actual retained cycle, with no
independent reciprocal-cap or raw canonical schedule identification.
-/
def withBSourceVariation {parameter : Canonical} {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher} {lifted : LiftedPuncturedGrid base}
    {bank : BasedBranchBank lifted} {sheet : Fin 2}
    {ordered : BasedBranchBank.Ordered bank sheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}
    (prepared : Prepared paired) (index : Fin 1) {valueFloor : Nat}
    (values : PolynomialValues (parameter := parameter) (frame := frame) (prepared.bWalk index) valueFloor)
    {parent : CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1))}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1)))}
    (same : values.1.parents = parent :: parents) {current floor rootStage : Nat} {reference : AccuracyRequest}
    (requested : Requested (values.1.sourceCovered same) (values.1.sourceChain same) current floor rootStage reference)
    (completed : requested.attempt.OccurrenceFamily) (actual : SynchronizedPeriodJet frame)
    (factory : actual = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor) (rootStage := rootStage)
      (values.1.sourceCovered same) (values.1.sourceChain same) (fun stage => (completed stage).val))
    (ranges : ParameterRange (values.1.sourceCovered same)) (allocation : ParameterRange.StripAllocation ranges)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    {targetCurrent targetFloor targetRootStage : Nat} {increment : Canonical}
    {zeroAdmitted : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    (zero : LocalMember requested ranges allocation (values.1.sourceRoots same) widths
      targetCurrent targetFloor targetRootStage 0 zeroAdmitted)
    (last : LocalMember requested ranges allocation (values.1.sourceRoots same) widths
      targetCurrent targetFloor targetRootStage increment admitted)
    (retained : LocalMember.StripData last)
    (accuracy : AccuracyRequest) (nonzero : increment ≠ 0)
    (small : Norm.Basic.normSq increment ≤
      (LocalMember.sourceQuotientRequest (parameter := parameter) (frame := frame)
        (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1)
        (covered := values.1.sourceCovered same) (allocation := allocation) accuracy).tolerance)
    (firstStart lastStart freshStart originStart : Nat) (spatial : AccuracyRequest) {Result : Type u}
    (consume : SourceVariationConsumer (parameter := parameter) (frame := frame) (walk := prepared.bWalk index)
      (parent := parent) (parents := parents) (current := current) (floor := floor) (rootStage := rootStage)
      (reference := reference) (ranges := ranges) (allocation := allocation) (widths := widths)
      (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
      values same requested actual zero last retained
      (prepared.bOccurrenceJet index values floor rootStage (values.1.sourcePreparations same requested))
      (prepared.bValueAttachment index values floor rootStage (values.1.sourcePreparations same requested))
      accuracy nonzero originStart Result) : Result :=
  let anchored := prepared.bSourceValueAttachment index values same requested completed actual factory
  withVariation (parameter := parameter) (frame := frame) (walk := prepared.bWalk index)
    (parent := parent) (parents := parents) (current := current) (floor := floor) (rootStage := rootStage)
    (reference := reference) (ranges := ranges) (allocation := allocation) (widths := widths)
    (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
    values same requested completed actual factory zero last retained
    accuracy nonzero small firstStart lastStart freshStart originStart spatial (consume anchored)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

end
