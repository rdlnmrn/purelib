module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Queries
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip
import Purelib.Riemann.Branches.PreparedPrimitiveSheets
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Geometry.Rational.Box.Refinement

/-! # The same original seed over every rational section of a physical parameter strip

A supplied original query sample and its actual absolute Step remain
unchanged. One fixed-box reference is computed and retained at that same
point and offset, and its comparison consumes that actual reference. The
whole strip budget pays every rational interpolation time. Actual shifted
child queries then attach to this reference through their retained aligned
RootComparison; no Point, Query, Step, model or source preparation is rerun.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (prepared : PreparedParent patch count floor covered targets)
    (range : Variation.Point.Range (patch.neighborhood count))
    (budget : FixedRootBoxBudget.Budget (patch.neighborhood count).base.seed.owner)
    (budget_eq : budget = range.seedBudget)

/-- The actual query coordinate lies in the original covering box at every admitted parent fraction. -/
theorem queryPoint_inside (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    (patch.neighborhood count).box.Contains (prepared.preparation.cell.models.coordinate.point fraction) :=
  Eq.mp (congrArg (patch.neighborhood count).box.Contains (prepared.queryPoint_eq fraction).symm)
    (sample_inside (parameter := parameter) (frame := frame) (basis := basis) (parent := parent)
      (patch := patch) (count := count) (covered := covered) inside)

/-- Construct and retain one original-seed reference at the actual query point and admitted absolute offset. -/
def queryStripReference (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    (offset : Canonical) (admitted : Norm.Basic.normSq offset ≤ range.stripBound) :
    { reference : Owner ((Paths.polynomial (parameter + offset)).eval
        (prepared.preparation.cell.models.coordinate.point fraction)) //
      reference = range.seedOwner budget budget_eq (prepared.queryPoint_inside fraction inside) offset admitted } :=
  ⟨range.seedOwner budget budget_eq (prepared.queryPoint_inside fraction inside) offset admitted, rfl⟩

/-- Compare the same supplied absolute Step with a retained strip reference without recomputing either owner.

The actual Step and source query sample refine the original seed box.
The reference's whole factory law identifies that same box, so the original
root-track comparison consumes the two supplied tracks directly.
-/
def compareStripReference (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    (offset : Canonical) (admitted : Norm.Basic.normSq offset ≤ range.stripBound)
    (reference : Owner ((Paths.polynomial (parameter + offset)).eval
      (prepared.preparation.cell.models.coordinate.point fraction)))
    (reference_eq : reference = range.seedOwner budget budget_eq
      (prepared.queryPoint_inside fraction inside) offset admitted)
    (sample : ContinuedNeighborhood.Point prepared.preparation.cell.patch
      (prepared.preparation.cell.models.coordinate.point fraction))
    (step : Variation.Point.Step sample offset) :
    NamedEquivalent (ownerRootName reference.parameterNonzero reference) step.root.value.name := by
  have box := (congrArg (fun owner : Owner ((Paths.polynomial (parameter + offset)).eval
      (prepared.preparation.cell.models.coordinate.point fraction)) => owner.track.initial.box) reference_eq).trans
    (range.seedOwner_box budget budget_eq (prepared.queryPoint_inside fraction inside) offset admitted)
  have original := step.refines.trans (prepared.querySample_refines fraction sample)
  have refines := Eq.mp (congrArg (fun target => step.owner.track.initial.box.Refines target) box.symm) original
  let compared := PreparedPrimitiveSheets.rootEquivalent_of_initial_refines step.owner.parameterNonzero
    reference.track step.owner.track refines
  have name : ownerRootName step.owner.parameterNonzero step.owner = step.root.value.name := by
    rewrite [step.root_eq]
    rfl
  exact NamedEquivalent.transport rfl name compared

/-- Every rational interpolation time admits the same retained source query Step and one fixed-seed comparison.

The original whole-strip payment derives the time-scaled payment before
constructing one reference. The supplied Step is the actual continuation
already retained by a query consumer; neither it nor the source sample is
advanced or observed here. The returned comparison uses that same bound
reference and preserves its complete original seedOwner factory.
-/
def queryStripAt (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.stripBound)
    (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1)
    (sample : ContinuedNeighborhood.Point prepared.preparation.cell.patch
      (prepared.preparation.cell.models.coordinate.point fraction))
    (step : Variation.Point.Step sample ((⟨time, 0⟩ : Canonical) * increment)) :
    (reference : { value : Owner ((Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval
          (prepared.preparation.cell.models.coordinate.point fraction)) //
      value = range.seedOwner budget budget_eq (prepared.queryPoint_inside fraction inside)
        ((⟨time, 0⟩ : Canonical) * increment) (range.interpolated_admitted time timeInside increment admitted) }) ×
    NamedEquivalent (ownerRootName reference.val.parameterNonzero reference.val) step.root.value.name :=
  let paid := range.interpolated_admitted time timeInside increment admitted
  let reference := prepared.queryStripReference range budget budget_eq fraction inside
    ((⟨time, 0⟩ : Canonical) * increment) paid
  let compared := prepared.compareStripReference range budget budget_eq fraction inside
    ((⟨time, 0⟩ : Canonical) * increment) paid reference.val reference.property sample step
  ⟨reference, compared⟩

/-- An actual time-section Step and one original-seed reference retain their complete original factories. -/
@[expose] def StripStep (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    (observed : CellModels.Observations frame (liftedCell parent)
      prepared.preparation.cell.models prepared.preparation.query.requests fraction)
    (observed_eq : observed = prepared.preparation.query.observe frame fraction inside.1 inside.2)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.stripBound)
    (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1) : Type _ :=
  (step : { value : Variation.Point.Step observed.retained.sample ((⟨time, 0⟩ : Canonical) * increment) //
    value = prepared.advanceRetained range fraction inside observed observed_eq
      ((⟨time, 0⟩ : Canonical) * increment)
      ((range.interpolated_admitted time timeInside increment admitted).trans
        (range.stripBound_le_shiftedBound.trans range.shiftedBound_le_bound)) }) ×
  (reference : { value : Owner ((Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval
        (prepared.preparation.cell.models.coordinate.point fraction)) //
    value = range.seedOwner budget budget_eq (prepared.queryPoint_inside fraction inside)
      ((⟨time, 0⟩ : Canonical) * increment) (range.interpolated_admitted time timeInside increment admitted) }) ×
  NamedEquivalent (ownerRootName reference.val.parameterNonzero reference.val) step.val.root.value.name

/-- Construct an actual signed section at every rational interpolation time on the SAME retained source query.

The original observation and its factory precede the time parameter. The
whole strip budget pays the original advanceRetained constructor, which
executes once, before one queryStripAt reference/comparison is retained.
This is fresh directTransport work for that requested time, not a memoized
family or an assertion that a supplied conditional Step already exists.
-/
def advanceStripAt (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    (observed : CellModels.Observations frame (liftedCell parent)
      prepared.preparation.cell.models prepared.preparation.query.requests fraction)
    (observed_eq : observed = prepared.preparation.query.observe frame fraction inside.1 inside.2)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.stripBound)
    (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1) :
    StripStep prepared range budget budget_eq fraction inside observed observed_eq increment admitted time timeInside :=
  let paid := (range.interpolated_admitted time timeInside increment admitted).trans
    (range.stripBound_le_shiftedBound.trans range.shiftedBound_le_bound)
  let step := prepared.advanceRetained range fraction inside observed observed_eq
    ((⟨time, 0⟩ : Canonical) * increment) paid
  let compared := prepared.queryStripAt range budget budget_eq fraction inside increment admitted time timeInside
    observed.retained.sample step
  ⟨⟨step, rfl⟩, compared.1, compared.2⟩

namespace ShiftedAcquisition.RootComparison

variable {increment : Canonical} {target : Paths.Frame (parameter + increment)}
    {range : Variation.Point.Range (patch.neighborhood count)}
    {admitted : Norm.Basic.normSq increment ≤ range.shiftedBound}
    {firstSample : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate}
    {firstStep : Variation.Point.Step firstSample increment} {width : AccuracyRequest}
    {retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width}
    {child : CenteredEdge (Fibre.frameCurve target) basis}
    {strip : Norm.Basic.normSq increment ≤ range.stripBound}
    {actual : OwnerPath (Fibre.frameCurve target).polynomial (startPoint parent).coordinate firstStep.owner
      (finishPoint parent).coordinate retained.acquired.traced.finishOwner}
    {actual_eq : actual = retained.acquired.traced.trace.get}
    (comparison : RootComparison retained strip actual actual_eq)
    (aligned : Acquisition.Segment.RootComparisons.Alignment comparison.paths comparison.firstReference)
    {oldFloor : Nat} {oldStart oldFinish : LiftedPoint 2} {oldPath : LiftedPath 2 oldStart oldFinish}
    {oldStage : Nat} {oldTargets : CellEndpoints.Targets oldPath oldStage}
    (oldPrepared : PreparedParent patch count oldFloor covered oldTargets)
    {newPatch : PreparedPatch child} {newCount newFloor : Nat}
    {newCovered : (newPatch.neighborhood newCount).box.Contains (child.edge.point 1)}
    {newStart newFinish : LiftedPoint 2} {newPath : LiftedPath 2 newStart newFinish}
    {newStage : Nat} {newTargets : CellEndpoints.Targets newPath newStage}
    (newPrepared : PreparedParent newPatch newCount newFloor newCovered newTargets)
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    {sourceSample : ContinuedNeighborhood.Point oldPrepared.preparation.cell.patch
      (oldPrepared.preparation.cell.models.coordinate.point
        (PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input))}
    (step : Variation.Point.Step sourceSample increment)
    (targetSample : ContinuedNeighborhood.Point newPrepared.preparation.cell.patch
      (newPrepared.preparation.cell.models.coordinate.point input))

/-- One original query reference and signed target comparison retain the complete seed-owner factory.

The same original comparison, prepared sources, physical child fraction and
actual target Point remain indices. This exact dependent pair constructs
no reference, query, continuation or comparison and adds no premise.
-/
@[expose] def QuerySection : Type _ :=
  let fraction := PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input
  let fractionInside := PreparedSheetContinuation.parameterAt_inside child.edge.left child.edge.request
    child.edge.ordered input inside
  (reference : { value : Owner ((Paths.polynomial (parameter + increment)).eval
        (oldPrepared.preparation.cell.models.coordinate.point fraction)) //
    value = range.seedOwner comparison.budget comparison.budget_eq
      (oldPrepared.queryPoint_inside fraction fractionInside) increment strip }) ×
  NamedEquivalent targetSample.certificate.value.name
    (ownerRootName reference.val.parameterNonzero reference.val)

/-- Attach the actual shifted Point query to the same original seed section through its retained absolute Step.

The original RootComparison derives the query-to-Step relation from the
supplied alignment, exact child occurrence and direct Query. One original
seed reference is then retained and compared to that same Step. No desired
root relation, observation, Step advancement or source preparation is input.
-/
def queryStrip (index : Fin retained.parents.covered.parents.length)
    (child_eq : child = retained.parents.covered.parents[index.val]'index.isLt)
    (direct : Riemann.Integration.PreparedConstantModels.PreparedEdge.Query child.edge input inside) :
    QuerySection comparison oldPrepared newPrepared input inside targetSample :=
  let fraction := PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input
  let fractionInside := PreparedSheetContinuation.parameterAt_inside child.edge.left child.edge.request
    child.edge.ordered input inside
  let reference := oldPrepared.queryStripReference range comparison.budget comparison.budget_eq
    fraction fractionInside increment strip
  let toStep := comparison.queryEquivalent aligned oldPrepared newPrepared input inside step targetSample
    index child_eq direct
  let fromReference := oldPrepared.compareStripReference range comparison.budget comparison.budget_eq
    fraction fractionInside increment strip reference.val reference.property sourceSample step
  ⟨reference, toStep.trans fromReference.symm⟩

end ShiftedAcquisition.RootComparison

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
