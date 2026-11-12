module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Strip
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Spatial
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query.Rooted
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step.Source
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot

/-! # Actual signed strip sections at retained original query fractions

The original StripStep already stores its complete Step/reference factories.
Physical-index transport retains that SAME reference and its original seed
box. Source anchoring at time zero uses the actual old Query and retained
Step; no fresh root selector or Frame equality is introduced.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
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
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName ownerRootName_castOwnerParameter)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Owner.Transport
  (castOwnerParameter castOwnerParameter_heq castOwnerParameter_initial_box)

attribute [local irreducible] CertifiedSquareRoot.rawRoot

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (prepared : PreparedParent patch count floor covered targets)
    (range : Variation.Point.Range (patch.neighborhood count))
    (budget : FixedRootBoxBudget.Budget (patch.neighborhood count).base.seed.owner)
    (budget_eq : budget = range.seedBudget)

/-- Retain the actual full-parameter comparison path at one original prepared query fraction.

The actual coordinate cache supplies the physical point and its original
whole-box admission. The original overlapPath uses this SAME range/budget
twice; only that quantitative path is constructed, not any queried Owner.
-/
def stripParameterPath (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.stripBound) :
    {value : FixedRootBoxPath.PathData budget budget //
      value = range.overlapPath range budget budget_eq budget budget_eq
        (prepared.queryPoint_inside fraction inside) (prepared.queryPoint_inside fraction inside)
        increment admitted admitted} :=
  let value := range.overlapPath range budget budget_eq budget budget_eq
    (prepared.queryPoint_inside fraction inside) (prepared.queryPoint_inside fraction inside)
    increment admitted admitted
  ⟨value, rfl⟩

/-- Retain the actual spatial comparison path at one admitted interpolation time on the SAME original parent.

The original source patch proves both endpoint admissions. Re-clearance
preserves the parent's orientation and exact affine points; the original
whole-strip budget pays the entire spatial path, independently of any
integration, source or derivative stage.
-/
def stripSpatialPath (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.stripBound)
    (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) :
    {value : FixedRootBoxPath.PathData budget budget //
      value = range.spatialPath budget budget_eq parent.edge.localSegment
        (start_inside patch count) (finish_inside patch count covered) increment admitted time inside} :=
  let value := range.spatialPath budget budget_eq parent.edge.localSegment
    (start_inside patch count) (finish_inside patch count covered) increment admitted time inside
  ⟨value, rfl⟩

/-- The retained parameter path reads the SAME original parent at both actual section coordinates. -/
theorem stripParameterPath_point (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.stripBound) (time : Rational) :
    (prepared.stripParameterPath range budget budget_eq fraction inside increment admitted).val.point time =
      (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval (parent.edge.point fraction) := by
  unfold stripParameterPath
  exact (range.overlapPath_point range budget budget_eq budget budget_eq
    (prepared.queryPoint_inside fraction inside) (prepared.queryPoint_inside fraction inside)
    increment admitted admitted time).trans
      (congrArg (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval
        (prepared.queryPoint_eq fraction))

/-- The retained spatial path keeps the SAME parent's exact affine points and original orientation. -/
theorem stripSpatialPath_point (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.stripBound)
    (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) (fraction : Rational) :
    (stripSpatialPath (covered := covered) (range := range) (budget := budget) (budget_eq := budget_eq)
      increment admitted time inside).val.point fraction =
        (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval (parent.edge.point fraction) := by
  unfold stripSpatialPath
  exact range.spatialPath_point budget budget_eq parent.edge.localSegment (start_inside patch count)
    (finish_inside patch count covered) increment admitted time inside fraction

namespace StripStep

variable {prepared range budget budget_eq}
    {fraction : Rational} {inside : 0 ≤ fraction ∧ fraction ≤ 1}
    {observed : QueryObservations (parameter := parameter) (frame := frame) (basis := basis)
      (parent := parent) (patch := patch) (count := count) (floor := floor) (covered := covered)
      (original := original) (stage := stage) (targets := targets) prepared fraction}
    {observed_eq : observed = prepared.preparation.query.observe frame fraction inside.1 inside.2}
    {increment : Canonical} {admitted : Norm.Basic.normSq increment ≤ range.stripBound}
    {time : Rational} {timeInside : 0 ≤ time ∧ time ≤ 1}
    (kept : StripStep prepared range budget budget_eq fraction inside observed observed_eq
      increment admitted time timeInside)

/-- Read the SAME actual continued query Step and its complete original advanceRetained factory. -/
@[expose] def step : QueryStep (parameter := parameter) (frame := frame) (basis := basis)
    (parent := parent) (patch := patch) (count := count) (floor := floor) (covered := covered)
    (original := original) (stage := stage) (targets := targets)
    prepared range fraction inside observed observed_eq ((⟨time, 0⟩ : Canonical) * increment)
    ((range.interpolated_admitted time timeInside increment admitted).trans
      (range.stripBound_le_shiftedBound.trans range.shiftedBound_le_bound)) := kept.1

/-- Read the SAME retained original-seed reference with its whole actual factory. -/
@[expose] def reference :
    {value : Owner ((Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval
        (prepared.preparation.cell.models.coordinate.point fraction)) //
      value = range.seedOwner budget budget_eq (prepared.queryPoint_inside fraction inside)
        ((⟨time, 0⟩ : Canonical) * increment) (range.interpolated_admitted time timeInside increment admitted)} :=
  kept.2.1

/-- Read the original internally derived signed reference-to-Step comparison, without another comparison producer. -/
@[expose] def compared :
    NamedEquivalent (ownerRootName kept.reference.val.parameterNonzero kept.reference.val)
      kept.step.val.root.value.name :=
  kept.2.2

/-- The actual query reference retains the literal old covering seed box at every interpolation time. -/
theorem reference_box : kept.reference.val.track.initial.box =
    (patch.neighborhood count).base.seed.owner.track.initial.box :=
  (congrArg (fun owner : Owner ((Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval
    (prepared.preparation.cell.models.coordinate.point fraction)) => owner.track.initial.box)
      kept.reference.property).trans
    (range.seedOwner_box budget budget_eq (prepared.queryPoint_inside fraction inside)
      ((⟨time, 0⟩ : Canonical) * increment) (range.interpolated_admitted time timeInside increment admitted))

/-- View the SAME actual reference at the original parent's physical point through its exact scalar query readback. -/
def physicalReference :
    Owner ((Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval (parent.edge.point fraction)) :=
  castOwnerParameter
    (congrArg (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval
      (prepared.queryPoint_eq fraction)) kept.reference.val

/-- Physical-index transport keeps the entire SAME retained reference Owner heterogeneously. -/
theorem physicalReference_heq : HEq kept.physicalReference kept.reference.val := by
  unfold physicalReference
  exact castOwnerParameter_heq _ _

/-- Physical-index transport retains the actual original signed root name. -/
theorem physicalReference_name :
    ownerRootName kept.physicalReference.parameterNonzero kept.physicalReference =
      ownerRootName kept.reference.val.parameterNonzero kept.reference.val := by
  unfold physicalReference
  exact ownerRootName_castOwnerParameter _ _

/-- The physical-index view retains the SAME original signed seed box. -/
theorem physicalReference_box : kept.physicalReference.track.initial.box =
    (patch.neighborhood count).base.seed.owner.track.initial.box := by
  unfold physicalReference
  exact (castOwnerParameter_initial_box _ _).trans kept.reference_box

/-- The SAME physical-index reference derives the actual retained Step's sign at every admitted pair of fractions. -/
def physicalEquivalent :
    NamedEquivalent (ownerRootName kept.physicalReference.parameterNonzero kept.physicalReference)
      kept.step.val.root.value.name :=
  NamedEquivalent.transport kept.physicalReference_name.symm rfl kept.compared

section Paths

attribute [local irreducible] physicalReference reference step

/-- Attach the actual retained query reference to a GIVEN once-bound parameter PathData on the SAME budget.

The whole original path factory supplies its exact point identity. The
original firstRetained operation consumes this SAME reference and its own
box certificate; its genuine internal ownerAt query remains new work.
-/
def parameterEquivalent
    (path : {value : FixedRootBoxPath.PathData budget budget //
      value = range.overlapPath range budget budget_eq budget budget_eq
        (prepared.queryPoint_inside fraction inside) (prepared.queryPoint_inside fraction inside)
        increment admitted admitted}) :
    NamedEquivalent
      (ownerRootName (path.val.nonzero time timeInside) (path.val.First time timeInside))
      (ownerRootName kept.reference.val.parameterNonzero kept.reference.val) := by
  have pointEq := (congrArg (fun value : FixedRootBoxPath.PathData budget budget => value.point time)
    path.property).trans
      (range.overlapPath_point range budget budget_eq budget budget_eq
        (prepared.queryPoint_inside fraction inside) (prepared.queryPoint_inside fraction inside)
        increment admitted admitted time)
  let actual := castOwnerParameter pointEq.symm kept.reference.val
  have actualBox := (castOwnerParameter_initial_box pointEq.symm kept.reference.val).trans kept.reference_box
  have refines : actual.track.initial.box.Refines
      (patch.neighborhood count).base.seed.owner.track.initial.box := by
    rewrite [actualBox]
    exact Geometry.Rational.Box.refines_refl _
  let compared := path.val.firstRetained time timeInside actual refines
  exact NamedEquivalent.transport rfl
    (ownerRootName_castOwnerParameter pointEq.symm kept.reference.val) compared

-- Preserve dependent owner lets during the optional declaration cleanup pass.
set_option cleanup.letToHave false in
/-- Attach the SAME physical-index reference to a GIVEN once-bound spatial path on the original oriented parent.

Exact pointwise affine readback and its whole path factory reindex only the
radicand. The reference's actual signed seed-box certificate is retained;
no root, Frame, source query or integration model is replaced.
-/
def spatialEquivalent
    (path : {value : FixedRootBoxPath.PathData budget budget //
      value = range.spatialPath budget budget_eq parent.edge.localSegment
        (start_inside patch count) (finish_inside patch count covered) increment admitted time timeInside}) :
    NamedEquivalent
      (ownerRootName (path.val.nonzero fraction inside) (path.val.First fraction inside))
      (ownerRootName kept.physicalReference.parameterNonzero kept.physicalReference) := by
  have pointEq := (congrArg (fun value : FixedRootBoxPath.PathData budget budget => value.point fraction)
    path.property).trans
      (range.spatialPath_point budget budget_eq parent.edge.localSegment (start_inside patch count)
        (finish_inside patch count covered) increment admitted time timeInside fraction)
  let actual := castOwnerParameter pointEq.symm kept.physicalReference
  have retainedBox := physicalReference_box (prepared := prepared) (range := range)
    (budget := budget) (budget_eq := budget_eq) kept
  have actualBox := (castOwnerParameter_initial_box pointEq.symm kept.physicalReference).trans retainedBox
  have refines : actual.track.initial.box.Refines
      (patch.neighborhood count).base.seed.owner.track.initial.box := by
    rewrite [actualBox]
    exact Geometry.Rational.Box.refines_refl _
  let compared := path.val.firstRetained fraction inside actual refines
  exact NamedEquivalent.transport rfl
    (ownerRootName_castOwnerParameter pointEq.symm kept.physicalReference) compared

end Paths

/-- At actual time zero this signed section agrees with the SAME retained original source sample.

The scalar zero-time identity reindexes only the Step increment. Its
original source comparison and stored reference comparison derive the sign;
no source observation, Step, reference, Frame or query is reconstructed.
-/
def sourceAtZero (zero : time = 0) :
    NamedEquivalent (ownerRootName kept.physicalReference.parameterNonzero kept.physicalReference)
      observed.retained.sample.certificate.value.name :=
  kept.physicalEquivalent.trans (Variation.Point.Step.sourceEquivalent_of_zero kept.step.val
    ((congrArg (fun value : Rational => (⟨value, 0⟩ : Canonical) * increment) zero).trans
      (Basic.zero_mul increment)))

/-- The actual signed time-zero section agrees with a GIVEN original direct Query at the SAME old physical fraction. -/
def queryAtZero (zero : time = 0) (direct : PreparedEdge.Query parent.edge fraction inside) :
    NamedEquivalent (ownerRootName kept.physicalReference.parameterNonzero kept.physicalReference)
      (parent.edge.rootName fraction inside) :=
  (kept.sourceAtZero zero).trans
    (prepared.querySampleEquivalent fraction inside observed.retained.sample direct).symm

end StripStep

namespace ShiftedAcquisition.RootComparison.QuerySection

variable {increment : Canonical} {target : Paths.Frame (parameter + increment)}
    {shiftedPaid : Norm.Basic.normSq increment ≤ range.shiftedBound}
    {firstSample : ContinuedNeighborhood.Point
      (patch.neighborhood count) (startPoint parent).coordinate}
    {firstStep : Variation.Point.Step firstSample increment} {width : Approximation.AccuracyRequest}
    {retained : ShiftedAcquisition (covered := covered) range target shiftedPaid firstStep width}
    {strip : Norm.Basic.normSq increment ≤ range.stripBound}
    {actual : OwnerPath (Fibre.frameCurve target).polynomial
      (startPoint parent).coordinate firstStep.owner (finishPoint parent).coordinate
      retained.acquired.traced.finishOwner}
    {actual_eq : actual = retained.acquired.traced.trace.get}
    {child : CenteredEdge (Fibre.frameCurve target) basis}
    (comparison : RootComparison retained strip actual actual_eq)
    {newPatch : PreparedPatch child} {newCount newFloor : Nat}
    {newCovered : (newPatch.neighborhood newCount).box.Contains (child.edge.point 1)}
    {newStart newFinish : LiftedPoint 2} {newPath : LiftedPath 2 newStart newFinish}
    {newStage : Nat} {newTargets : CellEndpoints.Targets newPath newStage}
    (newPrepared : PreparedParent newPatch newCount newFloor newCovered newTargets)
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    {targetSample : ContinuedNeighborhood.Point
      newPrepared.preparation.cell.patch (newPrepared.preparation.cell.models.coordinate.point input)}
    (queried : QuerySection comparison prepared newPrepared input inside targetSample)

/-- Read the SAME actual member-query reference on its original physical source-parent fraction. -/
def physicalReference :
    Owner ((Paths.polynomial (parameter + increment)).eval
      (parent.edge.point (PreparedSheetContinuation.parameterAt
        child.edge.left child.edge.request input))) :=
  castOwnerParameter (congrArg (Paths.polynomial (parameter + increment)).eval
    (prepared.queryPoint_eq (PreparedSheetContinuation.parameterAt
      child.edge.left child.edge.request input))) queried.1.val

/-- Reindexing the original query section keeps its whole actual seed reference Owner heterogeneously. -/
theorem physicalReference_heq :
    HEq (physicalReference (prepared := prepared) (range := range)
      (comparison := comparison) (newPrepared := newPrepared)
      (input := input) (inside := inside) queried) queried.1.val := by
  unfold physicalReference
  exact castOwnerParameter_heq _ _

/-- The given query section's physical reference retains precisely its original covering seed box. -/
theorem physicalReference_box :
    (physicalReference (prepared := prepared) (range := range)
      (comparison := comparison) (newPrepared := newPrepared)
      (input := input) (inside := inside) queried).track.initial.box =
        (patch.neighborhood count).base.seed.owner.track.initial.box := by
  unfold physicalReference
  have actualBox := congrArg (fun owner : Owner ((Paths.polynomial (parameter + increment)).eval
    (prepared.preparation.cell.models.coordinate.point
      (PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input))) =>
        owner.track.initial.box) queried.1.property
  exact (castOwnerParameter_initial_box _ _).trans (actualBox.trans
    (range.seedOwner_box comparison.budget comparison.budget_eq
      (prepared.queryPoint_inside _ (PreparedSheetContinuation.parameterAt_inside
        child.edge.left child.edge.request child.edge.ordered input inside)) increment strip))

/-- The SAME given actual target query agrees with this physical-index signed section reference. -/
def physicalEquivalent :
    NamedEquivalent targetSample.certificate.value.name
      (ownerRootName
        (physicalReference (prepared := prepared) (range := range)
          (comparison := comparison) (newPrepared := newPrepared)
          (input := input) (inside := inside) queried).parameterNonzero
        (physicalReference (prepared := prepared) (range := range)
          (comparison := comparison) (newPrepared := newPrepared)
          (input := input) (inside := inside) queried)) := by
  have same := ownerRootName_castOwnerParameter
    (congrArg (Paths.polynomial (parameter + increment)).eval
      (prepared.queryPoint_eq (PreparedSheetContinuation.parameterAt
        child.edge.left child.edge.request input))) queried.1.val
  exact NamedEquivalent.transport rfl same.symm queried.2

/-- At exact zero increment the actual query section agrees with its GIVEN original source sample.

The complete QueryStep supplies the SAME old observation/advance factory.
Only the original reference comparison is requested again: neither its
reference, the Step, source/target samples, query nor preparation is built.
The zero scalar condition identifies no pair of independent Frames.
-/
def sourceAtZero
    (observed : QueryObservations (parameter := parameter) (frame := frame) (basis := basis)
      (parent := parent) (patch := patch) (count := count) (floor := floor) (covered := covered)
      (original := original) (stage := stage) (targets := targets) prepared
      (PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input))
    (observed_eq : observed = prepared.preparation.query.observe frame
      (PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input)
      (PreparedSheetContinuation.parameterAt_inside
        child.edge.left child.edge.request child.edge.ordered input inside).1
      (PreparedSheetContinuation.parameterAt_inside
        child.edge.left child.edge.request child.edge.ordered input inside).2)
    (step : QueryStep (parameter := parameter) (frame := frame) (basis := basis)
      (parent := parent) (patch := patch) (count := count) (floor := floor) (covered := covered)
      (original := original) (stage := stage) (targets := targets) prepared range
      (PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input)
      (PreparedSheetContinuation.parameterAt_inside
        child.edge.left child.edge.request child.edge.ordered input inside)
      observed observed_eq increment (strip.trans (range.stripBound_le_shiftedBound.trans range.shiftedBound_le_bound)))
    (zero : increment = 0) :
    NamedEquivalent targetSample.certificate.value.name observed.retained.sample.certificate.value.name :=
  let fromReference := prepared.compareStripReference range comparison.budget comparison.budget_eq
    (PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input)
    (PreparedSheetContinuation.parameterAt_inside
      child.edge.left child.edge.request child.edge.ordered input inside)
    increment strip queried.1.val queried.1.property observed.retained.sample step.val
  queried.2.trans (fromReference.trans (Variation.Point.Step.sourceEquivalent_of_zero step.val zero))

end ShiftedAcquisition.RootComparison.QuerySection

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
