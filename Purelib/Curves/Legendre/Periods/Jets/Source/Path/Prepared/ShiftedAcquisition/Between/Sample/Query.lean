module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between.Polynomial
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.RootComparison
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Two-absolute-target query caches on the same original physical fraction

One original old answer supplies both independent absolute-time Steps.
Both actual target observations and direct Queries are materialized once.
New difference-fourth root requests and arithmetic reobservations remain
separate caches. One ten-comparison bank supplies all four polynomial rows.
The existing dependent-pair containers retain every whole factory equation.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

variable {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (sourcePrepared : PreparedParent patch count floor covered targets)
    {range : Variation.Point.Range (patch.neighborhood count)}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ range.shiftedBound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ range.shiftedBound}
    {firstStrip : Norm.Basic.normSq firstOffset ≤ range.stripBound}
    {lastStrip : Norm.Basic.normSq lastOffset ≤ range.stripBound} {firstWidth lastWidth : AccuracyRequest}
    (firstLinked : Linked sourcePrepared range firstFrame firstAdmitted firstStrip firstWidth)
    (lastLinked : Linked sourcePrepared range lastFrame lastAdmitted lastStrip lastWidth)
    (firstAligned : Acquisition.Segment.RootComparisons.Alignment
      firstLinked.comparison.paths firstLinked.comparison.firstReference)
    (lastAligned : Acquisition.Segment.RootComparisons.Alignment
      lastLinked.comparison.paths lastLinked.comparison.firstReference)
    {firstChild : CenteredEdge (Fibre.frameCurve firstFrame) basis}
    {lastChild : CenteredEdge (Fibre.frameCurve lastFrame) basis}
    {firstPatch : PreparedPatch firstChild} {lastPatch : PreparedPatch lastChild}
    {firstCount lastCount firstFloor lastFloor : Nat}
    {firstCovered : (firstPatch.neighborhood firstCount).box.Contains (firstChild.edge.point 1)}
    {lastCovered : (lastPatch.neighborhood lastCount).box.Contains (lastChild.edge.point 1)}
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstPath : LiftedPath 2 firstStart firstFinish} {lastPath : LiftedPath 2 lastStart lastFinish}
    {firstStage lastStage : Nat} {firstTargets : CellEndpoints.Targets firstPath firstStage}
    {lastTargets : CellEndpoints.Targets lastPath lastStage}
    (firstPrepared : PreparedParent firstPatch firstCount firstFloor firstCovered firstTargets)
    (lastPrepared : PreparedParent lastPatch lastCount lastFloor lastCovered lastTargets)
    (firstIndex : Fin firstLinked.shifted.acquired.mesh.edges.length)
    (lastIndex : Fin lastLinked.shifted.acquired.mesh.edges.length)
    (firstChild_eq : firstChild = firstLinked.shifted.childAt (firstLinked.shifted.dyadicIndex firstIndex))
    (lastChild_eq : lastChild = lastLinked.shifted.childAt (lastLinked.shifted.dyadicIndex lastIndex))
    (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1)
    (firstInside : (firstLinked.shifted.acquired.mesh.edges[firstIndex.val]'firstIndex.isLt).left.parameter ≤ time ∧
      time ≤ (firstLinked.shifted.acquired.mesh.edges[firstIndex.val]'firstIndex.isLt).right.parameter)
    (lastInside : (lastLinked.shifted.acquired.mesh.edges[lastIndex.val]'lastIndex.isLt).left.parameter ≤ time ∧
      time ≤ (lastLinked.shifted.acquired.mesh.edges[lastIndex.val]'lastIndex.isLt).right.parameter)
    (firstInput lastInput : Rational)
    (firstInput_eq : firstInput = Data.Rat.Interval.ConvexCombination.segmentParameter
      (firstLinked.shifted.acquired.mesh.edges[firstIndex.val]'firstIndex.isLt).left.parameter
      (firstLinked.shifted.acquired.mesh.edges[firstIndex.val]'firstIndex.isLt).right.parameter time)
    (lastInput_eq : lastInput = Data.Rat.Interval.ConvexCombination.segmentParameter
      (lastLinked.shifted.acquired.mesh.edges[lastIndex.val]'lastIndex.isLt).left.parameter
      (lastLinked.shifted.acquired.mesh.edges[lastIndex.val]'lastIndex.isLt).right.parameter time)
    (firstInputInside : 0 ≤ firstInput ∧ firstInput ≤ 1) (lastInputInside : 0 ≤ lastInput ∧ lastInput ≤ 1)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1) (nonzero : lastOffset - firstOffset ≠ 0)
    (spatial : AccuracyRequest)
    (firstPaid : ∀ channel : Fin 6, (firstPrepared.preparation.cell.models.cell channel).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)).tolerance)
    (lastPaid : ∀ channel : Fin 6, (lastPrepared.preparation.cell.models.cell channel).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)).tolerance)

namespace BetweenSample

/-- The exact original old query-bundle type at the retained parent fraction. -/
@[expose] def Old :=
  CellModels.Observations frame (liftedCell parent)
    sourcePrepared.preparation.cell.models sourcePrepared.preparation.query.requests time

/-- The exact first absolute Step type on the same old bundle's retained sample. -/
@[expose] def First (old : Old (sourcePrepared := sourcePrepared) (time := time)) :=
  Variation.Point.Step old.retained.sample firstOffset

/-- The exact last absolute Step type on that same old bundle's retained sample. -/
@[expose] def Last (old : Old (sourcePrepared := sourcePrepared) (time := time)) :=
  Variation.Point.Step old.retained.sample lastOffset

/-- The exact independently observed first-target bundle type. -/
@[expose] def FirstObserved :=
  CellModels.Observations firstFrame (liftedCell firstChild)
    firstPrepared.preparation.cell.models firstPrepared.preparation.query.requests firstInput

/-- The exact independently observed last-target bundle type. -/
@[expose] def LastObserved :=
  CellModels.Observations lastFrame (liftedCell lastChild)
    lastPrepared.preparation.cell.models lastPrepared.preparation.query.requests lastInput

/-- The exact first-target direct Query type with its actual input and unit-interval proof. -/
@[expose] def FirstDirect := PreparedEdge.Query firstChild.edge firstInput firstInputInside

/-- The exact last-target direct Query type with its own input and unit-interval proof. -/
@[expose] def LastDirect := PreparedEdge.Query lastChild.edge lastInput lastInputInside

/-- The exact original local-difference request type on both independently retained Steps. -/
@[expose] def Request
    (old : Old (sourcePrepared := sourcePrepared) (time := time))
    (first : First (sourcePrepared := sourcePrepared) (time := time) (firstOffset := firstOffset) old)
    (last : Last (sourcePrepared := sourcePrepared) (time := time) (lastOffset := lastOffset) old) :=
  Variation.Point.Step.BetweenRequest first last unit nonzero spatial

/-- The exact ten-comparison bank type on the same old sample, both Steps and both target observations. -/
@[expose] def Comparisons
    (old : Old (sourcePrepared := sourcePrepared) (time := time))
    (first : First (sourcePrepared := sourcePrepared) (time := time) (firstOffset := firstOffset) old)
    (last : Last (sourcePrepared := sourcePrepared) (time := time) (lastOffset := lastOffset) old)
    (firstObserved : FirstObserved (firstFrame := firstFrame) (firstPrepared := firstPrepared) (firstInput :=
      firstInput))
    (lastObserved : LastObserved (lastFrame := lastFrame) (lastPrepared := lastPrepared) (lastInput := lastInput))
    (request : Request (sourcePrepared := sourcePrepared) (time := time)
      (firstOffset := firstOffset) (lastOffset := lastOffset)
      (unit := unit) (nonzero := nonzero) (spatial := spatial) old first last) :=
  BetweenComparisons
    (sourcePrepared := sourcePrepared) (firstPrepared := firstPrepared) (lastPrepared := lastPrepared)
    (time := time) (firstInput := firstInput) (lastInput := lastInput) (sample := old.retained.sample)
    (firstStep := first) (lastStep := last) (firstObserved := firstObserved)
    (lastObserved := lastObserved) (paid := request.paid)

/-- The exact four original polynomial-row certificate slots at the unchanged local difference. -/
abbrev Certificates :=
  Data.Vector (Data.Vector (Quadratic.Basic.Certificate (lastOffset - firstOffset)) 2) 2

/-- The exact original absoluteSteps result retains both complete independent continuation factories. -/
private def Steps
    (old : Old (sourcePrepared := sourcePrepared) (time := time))
    (old_eq : old = sourcePrepared.preparation.query.observe frame time inside.1 inside.2) :=
  { first : First (sourcePrepared := sourcePrepared) (time := time) (firstOffset := firstOffset) old //
    first = sourcePrepared.advanceRetained range time inside old old_eq firstOffset
      (firstAdmitted.trans range.shiftedBound_le_bound) } ×
  { last : Last (sourcePrepared := sourcePrepared) (time := time) (lastOffset := lastOffset) old //
    last = sourcePrepared.advanceRetained range time inside old old_eq lastOffset
      (lastAdmitted.trans range.shiftedBound_le_bound) }

end BetweenSample

/-- The exact actual old answer, two Steps, independent target queries, ten comparisons and four polynomial rows.

Existing dependent pairs retain the original factory equations for every
newly materialized cache. There is no context record, copied patch, new root
owner, assumed signed relation or infinite precache. A separate invocation
at another bounded physical fraction genuinely constructs its own work.
-/
@[expose] def BetweenSample :=
  (old : { observed : BetweenSample.Old (sourcePrepared := sourcePrepared) (time := time) //
    observed = sourcePrepared.preparation.query.observe frame time inside.1 inside.2 }) ×
  (first : { step : BetweenSample.First (sourcePrepared := sourcePrepared) (time := time)
      (firstOffset := firstOffset) old.val //
    step = sourcePrepared.advanceRetained range time inside old.val old.property firstOffset
      (firstAdmitted.trans range.shiftedBound_le_bound) }) ×
  (last : { step : BetweenSample.Last (sourcePrepared := sourcePrepared) (time := time)
      (lastOffset := lastOffset) old.val //
    step = sourcePrepared.advanceRetained range time inside old.val old.property lastOffset
      (lastAdmitted.trans range.shiftedBound_le_bound) }) ×
  (firstObserved : { observed : BetweenSample.FirstObserved
      (firstFrame := firstFrame) (firstPrepared := firstPrepared) (firstInput := firstInput) //
    observed = firstPrepared.preparation.query.observe firstFrame firstInput firstInputInside.1 firstInputInside.2 }) ×
  (lastObserved : { observed : BetweenSample.LastObserved
      (lastFrame := lastFrame) (lastPrepared := lastPrepared) (lastInput := lastInput) //
    observed = lastPrepared.preparation.query.observe lastFrame lastInput lastInputInside.1 lastInputInside.2 }) ×
  (firstDirect : { query : BetweenSample.FirstDirect
      (firstChild := firstChild) (firstInput := firstInput) (firstInputInside := firstInputInside) //
    query = PreparedEdge.Query.build firstChild.edge firstInput firstInputInside }) ×
  (lastDirect : { query : BetweenSample.LastDirect
      (lastChild := lastChild) (lastInput := lastInput) (lastInputInside := lastInputInside) //
    query = PreparedEdge.Query.build lastChild.edge lastInput lastInputInside }) ×
  (request : { value : BetweenSample.Request (sourcePrepared := sourcePrepared) (time := time)
      (firstOffset := firstOffset) (lastOffset := lastOffset)
      (unit := unit) (nonzero := nonzero) (spatial := spatial) old.val first.val last.val //
    value = Variation.Point.Step.BetweenRequest.build first.val last.val unit nonzero spatial }) ×
  (comparisons : { value : BetweenSample.Comparisons
      (sourcePrepared := sourcePrepared) (firstPrepared := firstPrepared) (lastPrepared := lastPrepared)
      (time := time) (firstInput := firstInput) (lastInput := lastInput)
      (firstOffset := firstOffset) (lastOffset := lastOffset)
      (unit := unit) (nonzero := nonzero) (spatial := spatial)
      old.val first.val last.val firstObserved.val lastObserved.val request.val //
    value = betweenComparisons sourcePrepared firstLinked lastLinked firstAligned lastAligned
      firstPrepared lastPrepared firstIndex lastIndex firstChild_eq lastChild_eq time firstInside lastInside
      firstInput lastInput firstInput_eq lastInput_eq firstInputInside lastInputInside old.val.retained.sample
      first.val last.val firstObserved.val lastObserved.val firstObserved.property lastObserved.property
      firstDirect.val lastDirect.val request.val.paid }) ×
  { certificates : BetweenSample.Certificates (firstOffset := firstOffset) (lastOffset := lastOffset) //
    certificates = betweenPolynomialRows sourcePrepared first.val last.val firstPrepared lastPrepared
      firstObserved.val lastObserved.val request.val.paid comparisons.val
      (fun channel => request.val.allowancePaid _ (firstPaid channel))
      (fun channel => request.val.allowancePaid _ (lastPaid channel)) }

/-- Construct one actual two-target query sample and every whole factory certificate in their original order.

The old query executes once before the two absolute continuations. Both
actual target bundles and direct Queries execute once; requestBetween
then makes genuinely new independently paid residual and evaluator caches.
The ten comparisons execute once and feed the four stored polynomial rows.
The supplied original Alignments are consumed without replay or rebuilding.
-/
def sampleBetween : BetweenSample sourcePrepared firstLinked lastLinked firstAligned lastAligned
    firstPrepared lastPrepared firstIndex lastIndex firstChild_eq lastChild_eq time inside firstInside lastInside
    firstInput lastInput firstInput_eq lastInput_eq firstInputInside lastInputInside unit nonzero spatial
    firstPaid lastPaid :=
  let old : BetweenSample.Old (sourcePrepared := sourcePrepared) (time := time) :=
    sourcePrepared.preparation.query.observe frame time inside.1 inside.2
  let steps : BetweenSample.Steps (sourcePrepared := sourcePrepared) (range := range)
      (time := time) (inside := inside) (firstOffset := firstOffset) (lastOffset := lastOffset)
      (firstAdmitted := firstAdmitted) (lastAdmitted := lastAdmitted) old rfl :=
    sourcePrepared.absoluteSteps range time inside old rfl firstOffset lastOffset
    (firstAdmitted.trans range.shiftedBound_le_bound) (lastAdmitted.trans range.shiftedBound_le_bound)
  let firstObserved : BetweenSample.FirstObserved (firstFrame := firstFrame) (firstPrepared := firstPrepared)
    (firstInput := firstInput) :=
    firstPrepared.preparation.query.observe firstFrame
    firstInput firstInputInside.1 firstInputInside.2
  let lastObserved : BetweenSample.LastObserved (lastFrame := lastFrame) (lastPrepared := lastPrepared) (lastInput :=
    lastInput) :=
    lastPrepared.preparation.query.observe lastFrame lastInput lastInputInside.1 lastInputInside.2
  let firstDirect : BetweenSample.FirstDirect
      (firstChild := firstChild) (firstInput := firstInput) (firstInputInside := firstInputInside) :=
    PreparedEdge.Query.build firstChild.edge firstInput firstInputInside
  let lastDirect : BetweenSample.LastDirect
      (lastChild := lastChild) (lastInput := lastInput) (lastInputInside := lastInputInside) :=
    PreparedEdge.Query.build lastChild.edge lastInput lastInputInside
  let request : BetweenSample.Request (sourcePrepared := sourcePrepared) (time := time)
      (firstOffset := firstOffset) (lastOffset := lastOffset)
      (unit := unit) (nonzero := nonzero) (spatial := spatial) old steps.1.val steps.2.val :=
    Variation.Point.Step.BetweenRequest.build steps.1.val steps.2.val unit nonzero spatial
  let comparisons : BetweenSample.Comparisons
      (sourcePrepared := sourcePrepared) (firstPrepared := firstPrepared) (lastPrepared := lastPrepared)
      (time := time) (firstInput := firstInput) (lastInput := lastInput)
      (firstOffset := firstOffset) (lastOffset := lastOffset)
      (unit := unit) (nonzero := nonzero) (spatial := spatial)
      old steps.1.val steps.2.val firstObserved lastObserved request :=
    betweenComparisons sourcePrepared firstLinked lastLinked firstAligned lastAligned
    firstPrepared lastPrepared firstIndex lastIndex firstChild_eq lastChild_eq time firstInside lastInside
    firstInput lastInput firstInput_eq lastInput_eq firstInputInside lastInputInside old.retained.sample
    steps.1.val steps.2.val firstObserved lastObserved rfl rfl firstDirect lastDirect request.paid
  let certificates : BetweenSample.Certificates (firstOffset := firstOffset) (lastOffset := lastOffset) :=
    betweenPolynomialRows sourcePrepared steps.1.val steps.2.val firstPrepared lastPrepared
    firstObserved lastObserved request.paid comparisons
    (fun channel => request.allowancePaid _ (firstPaid channel))
    (fun channel => request.allowancePaid _ (lastPaid channel))
  ⟨⟨old, rfl⟩, steps.1, steps.2, ⟨firstObserved, rfl⟩, ⟨lastObserved, rfl⟩,
    ⟨firstDirect, rfl⟩, ⟨lastDirect, rfl⟩, ⟨request, rfl⟩, ⟨comparisons, rfl⟩, ⟨certificates, rfl⟩⟩

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
