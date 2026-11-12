module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Dyadic
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Linked
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Between
public import Purelib.Curves.Legendre.Periods.Jets.Source.Observations.Channels
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query.Rooted
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Arithmetic.Taylor
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Queries
import Purelib.Approximation.Gaussian.Provenance.Power
import Purelib.Data.Vector.Dependent
import Purelib.Data.Rat.Interval.ConvexCombination

/-! # Actual two-target query attachments on one original physical fraction

One retained old query supplies two independently admitted absolute Steps.
The exact original Mesh/Parents indices normalize the two target queries to
that same old fraction. Each retained RootComparison/Alignment derives its
own signed attachment; no equality of target owners or local h-Step is used.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation (ArithmeticComparison)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Riemann.RootContinuation
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Interval.ConvexCombination
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}

/-- Continue one supplied original query answer at a newly paid increment without observing that query again.

Its whole original query equation gives the acquisition identity. Exact
queryRange transport preserves the original physical-patch range and the
same actual Cell/count owner; the returned Step belongs to THIS sample.
-/
def advanceRetained (prepared : PreparedParent patch count floor covered targets)
    (range : Variation.Point.Range (patch.neighborhood count)) (time : Rational)
    (inside : 0 ≤ time ∧ time ≤ 1)
    (observed : CellModels.Observations frame (liftedCell parent)
      prepared.preparation.cell.models prepared.preparation.query.requests time)
    (observed_eq : observed = prepared.preparation.query.observe frame time inside.1 inside.2)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.bound) :
    Variation.Point.Step observed.retained.sample increment :=
  let original := prepared.queryRange range
  let pointInside := prepared.preparation.cell.models.coordinate.point_inside
    prepared.preparation.cell.startInside prepared.preparation.cell.finishInside inside.1 inside.2
  have same : observed.retained.sample = ContinuedNeighborhood.Point.acquire prepared.preparation.cell.patch
      (prepared.preparation.cell.models.coordinate.point time) pointInside :=
    (congrArg (fun answer : CellModels.Observations frame (liftedCell parent)
      prepared.preparation.cell.models prepared.preparation.query.requests time =>
        answer.retained.sample) observed_eq).trans
      (prepared.preparation.query.observe_sample frame time inside.1 inside.2)
  original.advance observed.retained.sample pointInside same increment
    (Eq.mp (congrArg (fun bound => Norm.Basic.normSq increment ≤ bound)
      (prepared.queryRange_bound range).symm) admitted)

/-- One actual continued query Step retains its complete original advanceRetained factory.

The supplied original observation bundle and whole observer equation stay
indices. The exact subtype adds no sample, geometry, root comparison or
numerical premise; its Step belongs to that SAME retained query Point.
-/
@[expose] def QueryStep (prepared : PreparedParent patch count floor covered targets)
    (range : Variation.Point.Range (patch.neighborhood count)) (time : Rational)
    (inside : 0 ≤ time ∧ time ≤ 1)
    (observed : QueryObservations (parameter := parameter) (frame := frame) (basis := basis)
      (parent := parent) (patch := patch) (count := count) (floor := floor) (covered := covered)
      (original := original) (stage := stage) (targets := targets) prepared time)
    (observed_eq : observed = prepared.preparation.query.observe frame time inside.1 inside.2)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.bound) : Type _ :=
  { value : Variation.Point.Step (parameter := parameter)
      (count := prepared.preparation.cell.count) (patch := prepared.preparation.cell.patch)
      (point := prepared.preparation.cell.models.coordinate.point time) observed.retained.sample increment //
    value = advanceRetained (parameter := parameter) (frame := frame) (basis := basis)
      (parent := parent) (patch := patch) (count := count) (floor := floor) (covered := covered)
      (original := original) (stage := stage) (targets := targets)
      prepared range time inside observed observed_eq increment admitted }

namespace QueryStep

/-- Advance the SAME supplied query Point once and retain its original whole factory equation.

Only advanceRetained executes. The original source observation, query,
model, requests and preparation remain inputs and are not reconstructed.
-/
def build (prepared : PreparedParent patch count floor covered targets)
    (range : Variation.Point.Range (patch.neighborhood count)) (time : Rational)
    (inside : 0 ≤ time ∧ time ≤ 1)
    (observed : QueryObservations (parameter := parameter) (frame := frame) (basis := basis)
      (parent := parent) (patch := patch) (count := count) (floor := floor) (covered := covered)
      (original := original) (stage := stage) (targets := targets) prepared time)
    (observed_eq : observed = prepared.preparation.query.observe frame time inside.1 inside.2)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.bound) :
    QueryStep (parameter := parameter) (frame := frame) (basis := basis)
      (parent := parent) (patch := patch) (count := count) (floor := floor) (covered := covered)
      (original := original) (stage := stage) (targets := targets)
      prepared range time inside observed observed_eq increment admitted :=
  let value := advanceRetained (parameter := parameter) (frame := frame) (basis := basis)
    (parent := parent) (patch := patch) (count := count) (floor := floor) (covered := covered)
    (original := original) (stage := stage) (targets := targets)
    prepared range time inside observed observed_eq increment admitted
  ⟨value, rfl⟩

end QueryStep

/-- Cache both original absolute continuations once on the SAME already retained old query answer.

Both returned whole factory equations concern their independent increments.
No old answer, first Step or target observation is relabelled as the other.
-/
def absoluteSteps (prepared : PreparedParent patch count floor covered targets)
    (range : Variation.Point.Range (patch.neighborhood count)) (time : Rational)
    (inside : 0 ≤ time ∧ time ≤ 1)
    (observed : CellModels.Observations frame (liftedCell parent)
      prepared.preparation.cell.models prepared.preparation.query.requests time)
    (observed_eq : observed = prepared.preparation.query.observe frame time inside.1 inside.2)
    (firstOffset lastOffset : Canonical)
    (firstPaid : Norm.Basic.normSq firstOffset ≤ range.bound)
    (lastPaid : Norm.Basic.normSq lastOffset ≤ range.bound) :
    { first : Variation.Point.Step observed.retained.sample firstOffset //
      first = prepared.advanceRetained range time inside observed observed_eq firstOffset firstPaid } ×
    { last : Variation.Point.Step observed.retained.sample lastOffset //
      last = prepared.advanceRetained range time inside observed observed_eq lastOffset lastPaid } :=
  let first := QueryStep.build (parameter := parameter) (frame := frame) (basis := basis)
    (parent := parent) (patch := patch) (count := count) (floor := floor) (covered := covered)
    (original := original) (stage := stage) (targets := targets)
    prepared range time inside observed observed_eq firstOffset firstPaid
  let last := QueryStep.build (parameter := parameter) (frame := frame) (basis := basis)
    (parent := parent) (patch := patch) (count := count) (floor := floor) (covered := covered)
    (original := original) (stage := stage) (targets := targets)
    prepared range time inside observed observed_eq lastOffset lastPaid
  ⟨first, last⟩

namespace ShiftedAcquisition

section OneTarget

variable {offset : Canonical} {target : Paths.Frame (parameter + offset)}
    {range : Variation.Point.Range (patch.neighborhood count)}
    {admitted : Norm.Basic.normSq offset ≤ range.shiftedBound}
    {firstSample : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate}
    {firstStep : Variation.Point.Step firstSample offset} {width : AccuracyRequest}
    (retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width)

/-- Normalizing an original Mesh parameter reads EXACTLY that parameter in its actual centered child request.

This is the scalar index equality underlying dyadicPoint_eq, including both
endpoints. It supplies no root comparison and constructs no new child.
-/
theorem dyadicParameter_eq (index : Fin retained.acquired.mesh.edges.length) (time : Rational)
    (inside : (retained.acquired.mesh.edges[index.val]'index.isLt).left.parameter ≤ time ∧
      time ≤ (retained.acquired.mesh.edges[index.val]'index.isLt).right.parameter) :
    let edge := retained.acquired.mesh.edges[index.val]'index.isLt
    let child := retained.childAt (retained.dyadicIndex index)
    PreparedSheetContinuation.parameterAt child.edge.left child.edge.request
      (segmentParameter edge.left.parameter edge.right.parameter time) = time := by
  let edge := retained.acquired.mesh.edges[index.val]'index.isLt
  let child := retained.childAt (retained.dyadicIndex index)
  let fraction := segmentParameter edge.left.parameter edge.right.parameter time
  have left_eq : child.edge.left.parameter = edge.left.parameter :=
    congrArg (fun value : ClearSheetContinuation.Subdivision.ParameterEdge => value.left.parameter)
      (retained.dyadicEdge_eq index)
  have right_eq : child.edge.request.endpoint.parameter = edge.right.parameter :=
    congrArg (fun value : ClearSheetContinuation.Subdivision.ParameterEdge => value.right.parameter)
      (retained.dyadicEdge_eq index)
  exact (PreparedSheetContinuation.parameterAt_eq_affine child.edge.left child.edge.request fraction).trans
    ((congrArg₂ (fun first last : Rational => first + fraction * (last - first)) left_eq right_eq).trans
      (segmentParameter_interpolates edge.left.parameter edge.right.parameter time
        ⟨(Data.Rat.Fraction.Order.Basic.min_le_left _ _).trans inside.1,
          inside.2.trans (Data.Rat.Fraction.Order.Basic.le_max_right _ _)⟩))

/-- The same actual child input recovers its retained original physical mesh parameter. -/
private theorem dyadicParameterAt_eq
    (index : Fin retained.acquired.mesh.edges.length)
    {child : CenteredEdge (Fibre.frameCurve target) basis}
    (childEq : child = retained.childAt (retained.dyadicIndex index))
    (time : Rational)
    (inside : (retained.acquired.mesh.edges[index.val]'index.isLt).left.parameter ≤ time ∧
      time ≤ (retained.acquired.mesh.edges[index.val]'index.isLt).right.parameter)
    (input : Rational)
    (inputEq : input = segmentParameter
      (retained.acquired.mesh.edges[index.val]'index.isLt).left.parameter
      (retained.acquired.mesh.edges[index.val]'index.isLt).right.parameter time) :
    PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input = time := by
  have inputEq' := congrArg (fun fraction : Rational =>
    PreparedSheetContinuation.parameterAt child.edge.left child.edge.request fraction) inputEq
  have childEq' := congrArg (fun edge : CenteredEdge (Fibre.frameCurve target) basis =>
    PreparedSheetContinuation.parameterAt edge.edge.left edge.edge.request
      (segmentParameter (retained.acquired.mesh.edges[index.val]'index.isLt).left.parameter
        (retained.acquired.mesh.edges[index.val]'index.isLt).right.parameter time)) childEq
  exact inputEq'.trans (childEq'.trans (dyadicParameter_eq retained index time inside))

end OneTarget

section QueryAttachment

variable {offset : Canonical} {target : Paths.Frame (parameter + offset)}
    {range : Variation.Point.Range (patch.neighborhood count)}
    {admitted : Norm.Basic.normSq offset ≤ range.shiftedBound}
    {strip : Norm.Basic.normSq offset ≤ range.stripBound} {width : AccuracyRequest}
    (sourcePrepared : PreparedParent patch count floor covered targets)
    (linked : Linked sourcePrepared range target admitted strip width)
    (aligned : Acquisition.Segment.RootComparisons.Alignment linked.comparison.paths linked.comparison.firstReference)
    {child : CenteredEdge (Fibre.frameCurve target) basis}
    {newPatch : PreparedPatch child} {newCount newFloor : Nat}
    {newCovered : (newPatch.neighborhood newCount).box.Contains (child.edge.point 1)}
    {newStart newFinish : LiftedPoint 2} {newPath : LiftedPath 2 newStart newFinish}
    {newStage : Nat} {newTargets : CellEndpoints.Targets newPath newStage}
    (newPrepared : PreparedParent newPatch newCount newFloor newCovered newTargets)
    (index : Fin linked.shifted.acquired.mesh.edges.length)
    (child_eq : child = linked.shifted.childAt (linked.shifted.dyadicIndex index))
    (time : Rational)
    (inside : (linked.shifted.acquired.mesh.edges[index.val]'index.isLt).left.parameter ≤ time ∧
      time ≤ (linked.shifted.acquired.mesh.edges[index.val]'index.isLt).right.parameter)

include sourcePrepared linked newPrepared index child_eq time inside in
/-- The normalized actual target query has exactly the original old source's physical point.

Only the retained dyadic edge/parent index and normalized input equality
are used. This scalar law retains both complete prepared source owners;
no query, root or observation is constructed.
-/
theorem queryPointAtParameter_eq (input : Rational)
    (input_eq : input = segmentParameter
      (linked.shifted.acquired.mesh.edges[index.val]'index.isLt).left.parameter
      (linked.shifted.acquired.mesh.edges[index.val]'index.isLt).right.parameter time) :
    sourcePrepared.preparation.cell.models.coordinate.point time =
      newPrepared.preparation.cell.models.coordinate.point input := by
  have physical : child.edge.point input = parent.edge.point time :=
    (congrArg (fun child => child.edge.point input) child_eq).trans
      ((congrArg (fun input =>
        (linked.shifted.childAt (linked.shifted.dyadicIndex index)).edge.point input) input_eq).trans
          (linked.shifted.dyadicPoint_eq index time inside))
  exact (sourcePrepared.queryPoint_eq time).trans (physical.symm.trans (newPrepared.queryPoint_eq input).symm)

/-- The actual target query attaches to a supplied absolute Step at its SAME original normalized fraction.

The whole retained Mesh-to-Parents incidence derives the scalar parameter
equality internally. Equality elimination reindexes the SAME sample/Step;
the existing RootComparison consumes its own original trace and Alignment.
The actual target Point and direct child Query remain unchanged inputs.
-/
def queryAtParameterEquivalent
    (input : Rational)
    (input_eq : input = segmentParameter
      (linked.shifted.acquired.mesh.edges[index.val]'index.isLt).left.parameter
      (linked.shifted.acquired.mesh.edges[index.val]'index.isLt).right.parameter time)
    (inputInside : 0 ≤ input ∧ input ≤ 1)
    (sample : ContinuedNeighborhood.Point sourcePrepared.preparation.cell.patch
      (sourcePrepared.preparation.cell.models.coordinate.point time))
    (step : Variation.Point.Step sample offset)
    (next : ContinuedNeighborhood.Point newPrepared.preparation.cell.patch
      (newPrepared.preparation.cell.models.coordinate.point input))
    (direct : PreparedEdge.Query child.edge input inputInside) :
    NamedEquivalent next.certificate.value.name step.root.value.name := by
  have parameterEq : PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input = time :=
    dyadicParameterAt_eq (parameter := parameter) (frame := frame) (basis := basis)
      (parent := parent) (patch := patch) (count := count) (covered := covered)
      (offset := offset) (target := target) (range := range) (admitted := admitted)
      (firstSample := sourcePrepared.firstSample) (firstStep := linked.first) (width := width)
      linked.shifted index child_eq time inside input input_eq
  exact (Eq.rec
    (motive := fun value (_ :
        PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input = value) =>
      (retainedSample : ContinuedNeighborhood.Point sourcePrepared.preparation.cell.patch
        (sourcePrepared.preparation.cell.models.coordinate.point value)) →
      (retainedStep : Variation.Point.Step retainedSample offset) →
        NamedEquivalent next.certificate.value.name retainedStep.root.value.name)
    (fun retainedSample retainedStep =>
      linked.comparison.queryEquivalent aligned sourcePrepared newPrepared input inputInside retainedStep next
        (linked.shifted.dyadicIndex index) child_eq direct)
    parameterEq) sample step

end QueryAttachment

section TwoTargets

variable {firstOffset lastOffset : Canonical}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {range : Variation.Point.Range (patch.neighborhood count)}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ range.shiftedBound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ range.shiftedBound}
    {firstStrip : Norm.Basic.normSq firstOffset ≤ range.stripBound}
    {lastStrip : Norm.Basic.normSq lastOffset ≤ range.stripBound} {firstWidth lastWidth : AccuracyRequest}
    (sourcePrepared : PreparedParent patch count floor covered targets)
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
    (time : Rational)
    (firstInside : (firstLinked.shifted.acquired.mesh.edges[firstIndex.val]'firstIndex.isLt).left.parameter ≤ time ∧
      time ≤ (firstLinked.shifted.acquired.mesh.edges[firstIndex.val]'firstIndex.isLt).right.parameter)
    (lastInside : (lastLinked.shifted.acquired.mesh.edges[lastIndex.val]'lastIndex.isLt).left.parameter ≤ time ∧
      time ≤ (lastLinked.shifted.acquired.mesh.edges[lastIndex.val]'lastIndex.isLt).right.parameter)
    (firstInput lastInput : Rational)
    (firstInput_eq : firstInput = segmentParameter
      (firstLinked.shifted.acquired.mesh.edges[firstIndex.val]'firstIndex.isLt).left.parameter
      (firstLinked.shifted.acquired.mesh.edges[firstIndex.val]'firstIndex.isLt).right.parameter time)
    (lastInput_eq : lastInput = segmentParameter
      (lastLinked.shifted.acquired.mesh.edges[lastIndex.val]'lastIndex.isLt).left.parameter
      (lastLinked.shifted.acquired.mesh.edges[lastIndex.val]'lastIndex.isLt).right.parameter time)
    (firstInputInside : 0 ≤ firstInput ∧ firstInput ≤ 1)
    (lastInputInside : 0 ≤ lastInput ∧ lastInput ≤ 1)
    (sample : ContinuedNeighborhood.Point sourcePrepared.preparation.cell.patch
      (sourcePrepared.preparation.cell.models.coordinate.point time))
    (firstStep : Variation.Point.Step sample firstOffset) (lastStep : Variation.Point.Step sample lastOffset)
    (firstObserved : CellModels.Observations firstFrame (liftedCell firstChild)
      firstPrepared.preparation.cell.models firstPrepared.preparation.query.requests firstInput)
    (lastObserved : CellModels.Observations lastFrame (liftedCell lastChild)
      lastPrepared.preparation.cell.models lastPrepared.preparation.query.requests lastInput)
    (firstObserved_eq : firstObserved =
      firstPrepared.preparation.query.observe firstFrame firstInput firstInputInside.1 firstInputInside.2)
    (lastObserved_eq : lastObserved =
      lastPrepared.preparation.query.observe lastFrame lastInput lastInputInside.1 lastInputInside.2)
    (firstDirect : PreparedEdge.Query firstChild.edge firstInput firstInputInside)
    (lastDirect : PreparedEdge.Query lastChild.edge lastInput lastInputInside)

/-- Attach ALL six channels of both actual target observations to their own retained absolute Step roots.

Each original RootComparison/Alignment executes its comparison construction
once, before the channel view. The two direct Queries, target observations,
original global preparations/Targets and absolute Steps are supplied caches.
Exact dyadic incidence derives their common old parameter; no desired signed
relation, coordinate-based sign identification or later-patch h-admission
is an input. Original channel-root readbacks consume both whole query
factory equations, keeping the two actual observations distinct.
-/
def betweenQueryAttachments :
    ((channel : Fin 6) → NamedEquivalent
      (firstObserved.channel channel).algebraic.sheetValue.value.name firstStep.root.value.name) ×
    ((channel : Fin 6) → NamedEquivalent
      (lastObserved.channel channel).algebraic.sheetValue.value.name lastStep.root.value.name) :=
  let firstCompared := queryAtParameterEquivalent sourcePrepared firstLinked firstAligned firstPrepared
    firstIndex firstChild_eq time firstInside firstInput firstInput_eq firstInputInside
    sample firstStep firstObserved.retained.sample firstDirect
  let lastCompared := queryAtParameterEquivalent sourcePrepared lastLinked lastAligned lastPrepared
    lastIndex lastChild_eq time lastInside lastInput lastInput_eq lastInputInside
    sample lastStep lastObserved.retained.sample lastDirect
  let firstRoots := fun channel : Fin 6 => NamedEquivalent.transport
    (firstPrepared.preparation.query.channel_root_name firstFrame firstInput firstInputInside.1 firstInputInside.2
      firstObserved firstObserved_eq channel).symm rfl firstCompared
  let lastRoots := fun channel : Fin 6 => NamedEquivalent.transport
    (lastPrepared.preparation.query.channel_root_name lastFrame lastInput lastInputInside.1 lastInputInside.2
      lastObserved lastObserved_eq channel).symm rfl lastCompared
  ⟨firstRoots, lastRoots⟩

variable {unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1}
    {core : Variation.Point.Step.BetweenCore firstStep lastStep unit}
    {arithmetic : Variation.Arithmetic.Observations core} {spatial : AccuracyRequest}
    (paid : Variation.Arithmetic.Reobservations arithmetic spatial)

/-- Ten actual arithmetic comparisons on both absolute-time target query bundles and their SAME between-step bank.

The exact existing five dependent-vector containers retain two source-value,
target-value, source-first, target-first and source-second comparisons. The
source-first entries are shared by both adjacent orders. Target numerics use
only exact parameter transport; all actual root/evaluator owners stay indexed.
-/
@[expose] def BetweenComparisons :=
  let point := sourcePrepared.preparation.cell.models.coordinate.point time
  let firstRoot := firstStep.root.castParameter (Variation.Point.radicand_eq (parameter + firstOffset) point)
  let lastRoot := lastStep.root.castParameter
    (Variation.Point.Step.betweenRadicand_eq parameter point firstOffset lastOffset)
  let firstIdentity : PowerIdentity firstRoot.value 2 ((Paths.polynomial (parameter + firstOffset)).eval point) :=
    Eq.mpr (congrArg (fun value => PowerIdentity firstRoot.value 2 value)
      (Variation.Point.radicand_eq (parameter + firstOffset) point)) (PowerIdentity.ofSquare firstRoot.square)
  let lastIdentity : PowerIdentity lastRoot.value 2 ((Paths.polynomial (parameter + lastOffset)).eval point) :=
    Eq.mpr (congrArg (fun value => PowerIdentity lastRoot.value 2 value)
      (Variation.Point.Step.betweenRadicand_eq parameter point firstOffset lastOffset))
        (PowerIdentity.ofSquare lastRoot.square)
  Data.Vector.DependentVector (fun coordinate : Fin 2 =>
    ArithmeticComparison (firstObserved.channel (Specification.Table.baseIndex 0 coordinate))
      (Variation.Point.Step.betweenNumerics firstStep lastStep paid 0 coordinate).1 firstIdentity) ×
  Data.Vector.DependentVector (fun coordinate : Fin 2 =>
    ArithmeticComparison (lastObserved.channel (Specification.Table.baseIndex 0 coordinate))
      (Variation.Point.Step.betweenNumerics firstStep lastStep paid 0 coordinate).2.1 lastIdentity) ×
  Data.Vector.DependentVector (fun coordinate : Fin 2 =>
    ArithmeticComparison (firstObserved.channel (Specification.Table.slopeIndex 0 coordinate))
      (Variation.Point.Step.betweenNumerics firstStep lastStep paid 0 coordinate).2.2 firstIdentity) ×
  Data.Vector.DependentVector (fun coordinate : Fin 2 =>
    ArithmeticComparison (lastObserved.channel (Specification.Table.baseIndex 1 coordinate))
      (Variation.Point.Step.betweenNumerics firstStep lastStep paid 1 coordinate).2.1 lastIdentity) ×
  Data.Vector.DependentVector (fun coordinate : Fin 2 =>
    ArithmeticComparison (firstObserved.channel (Specification.Table.slopeIndex 1 coordinate))
      (Variation.Point.Step.betweenNumerics firstStep lastStep paid 1 coordinate).2.2 firstIdentity)

/-- Materialize the ten original numeric/query comparisons once from BOTH actual geometric attachments.

The two RootComparisons execute once before the five channel banks. Every
original observation bundle/direct Query and actual absolute Step is consumed
unchanged. No evaluator, observation, source preparation, root continuation or
allocation is replayed. The only new work is each original generic comparison
on the two genuine independently paid readings it retains.
-/
def betweenComparisons : BetweenComparisons
    (sourcePrepared := sourcePrepared) (firstPrepared := firstPrepared) (lastPrepared := lastPrepared)
    (time := time) (firstInput := firstInput) (lastInput := lastInput) (sample := sample)
    (firstStep := firstStep) (lastStep := lastStep) (firstObserved := firstObserved)
    (lastObserved := lastObserved) (paid := paid) := by
  let point := sourcePrepared.preparation.cell.models.coordinate.point time
  let firstRoot := firstStep.root.castParameter (Variation.Point.radicand_eq (parameter + firstOffset) point)
  let lastRoot := lastStep.root.castParameter
    (Variation.Point.Step.betweenRadicand_eq parameter point firstOffset lastOffset)
  let firstIdentity : PowerIdentity firstRoot.value 2 ((Paths.polynomial (parameter + firstOffset)).eval point) :=
    Eq.mpr (congrArg (fun value => PowerIdentity firstRoot.value 2 value)
      (Variation.Point.radicand_eq (parameter + firstOffset) point)) (PowerIdentity.ofSquare firstRoot.square)
  let lastIdentity : PowerIdentity lastRoot.value 2 ((Paths.polynomial (parameter + lastOffset)).eval point) :=
    Eq.mpr (congrArg (fun value => PowerIdentity lastRoot.value 2 value)
      (Variation.Point.Step.betweenRadicand_eq parameter point firstOffset lastOffset))
        (PowerIdentity.ofSquare lastRoot.square)
  have firstName : firstRoot.value.name = firstStep.root.value.name :=
    congrArg (fun value : Approximation.Gaussian.Name.Coherent.CoherentNamed => value.name)
      (firstStep.root.castParameter_value (Variation.Point.radicand_eq (parameter + firstOffset) point))
  have lastName : lastRoot.value.name = lastStep.root.value.name :=
    congrArg (fun value : Approximation.Gaussian.Name.Coherent.CoherentNamed => value.name)
      (lastStep.root.castParameter_value
        (Variation.Point.Step.betweenRadicand_eq parameter point firstOffset lastOffset))
  let attached := betweenQueryAttachments sourcePrepared firstLinked lastLinked firstAligned lastAligned
    firstPrepared lastPrepared firstIndex lastIndex firstChild_eq lastChild_eq time firstInside lastInside
    firstInput lastInput firstInput_eq lastInput_eq firstInputInside lastInputInside sample firstStep lastStep
    firstObserved lastObserved firstObserved_eq lastObserved_eq firstDirect lastDirect
  have firstPoint := queryPointAtParameter_eq sourcePrepared firstLinked firstPrepared
    firstIndex firstChild_eq time firstInside firstInput firstInput_eq
  have lastPoint := queryPointAtParameter_eq sourcePrepared lastLinked lastPrepared
    lastIndex lastChild_eq time lastInside lastInput lastInput_eq
  let sourceValue := Data.Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    let channel := Specification.Table.baseIndex 0 coordinate
    let roots := NamedEquivalent.transport firstName.symm rfl (attached.1 channel).symm
    ArithmeticComparison.build (firstObserved.channel channel)
      (Variation.Point.Step.betweenNumerics firstStep lastStep paid 0 coordinate).1 firstIdentity
      (firstPoint.trans (firstObserved.channel_point channel).symm) roots)
  let targetValue := Data.Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    let channel := Specification.Table.baseIndex 0 coordinate
    let roots := NamedEquivalent.transport lastName.symm rfl (attached.2 channel).symm
    ArithmeticComparison.build (lastObserved.channel channel)
      (Variation.Point.Step.betweenNumerics firstStep lastStep paid 0 coordinate).2.1 lastIdentity
      (lastPoint.trans (lastObserved.channel_point channel).symm) roots)
  let sourceFirst := Data.Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    let channel := Specification.Table.slopeIndex 0 coordinate
    let roots := NamedEquivalent.transport firstName.symm rfl (attached.1 channel).symm
    ArithmeticComparison.build (firstObserved.channel channel)
      (Variation.Point.Step.betweenNumerics firstStep lastStep paid 0 coordinate).2.2 firstIdentity
      (firstPoint.trans (firstObserved.channel_point channel).symm) roots)
  let targetFirst := Data.Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    let channel := Specification.Table.baseIndex 1 coordinate
    let roots := NamedEquivalent.transport lastName.symm rfl (attached.2 channel).symm
    ArithmeticComparison.build (lastObserved.channel channel)
      (Variation.Point.Step.betweenNumerics firstStep lastStep paid 1 coordinate).2.1 lastIdentity
      (lastPoint.trans (lastObserved.channel_point channel).symm) roots)
  let sourceSecond := Data.Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    let channel := Specification.Table.slopeIndex 1 coordinate
    let roots := NamedEquivalent.transport firstName.symm rfl (attached.1 channel).symm
    ArithmeticComparison.build (firstObserved.channel channel)
      (Variation.Point.Step.betweenNumerics firstStep lastStep paid 1 coordinate).2.2 firstIdentity
      (firstPoint.trans (firstObserved.channel_point channel).symm) roots)
  exact ⟨sourceValue, targetValue, sourceFirst, targetFirst, sourceSecond⟩

end TwoTargets

end ShiftedAcquisition

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
