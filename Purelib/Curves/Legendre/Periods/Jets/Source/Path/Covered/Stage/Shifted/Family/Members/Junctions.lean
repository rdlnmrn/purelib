module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Geometry
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Overlap
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point
import Purelib.Curves.Legendre.PicardFuchs.Polynomials
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Chain
import Purelib.Riemann.Branches.PreparedPrimitiveSheets
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.DependentProduct

/-! # Uniform parameter continuation at the original signed source junctions

One given zero member supplies its original budgets and actual endpoint
Steps. The unchanged source chain supplies each literal following point
and signed link. A two-box PathData then retains the full actual parameter
interval and its quantitative bounds, and the original finite continuation
propagates that derived source agreement. No member or query is replayed.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Order.Arithmetic (instZeroLEOneClass)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Owner.Transport
  (castOwnerParameter castOwnerParameter_initial_box)
open PreparedParent (startPoint finishPoint)

namespace StageAttempt.Requested.LocalMember

/-- Compare a given queried reference with a given zero Step through its actual source/target box refinements.

Only the scalar quadratic parameter is reindexed. The original cast laws
retain the complete Step Owner, its initial box and its root name. The
original winding-one comparison supplies agreement; no owner identity or
point identity is inferred from the matching scalar parameter.
-/
private def reference_zeroStep {parameter point referenceParameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    {source : ContinuedNeighborhood.Point patch point} (step : Variation.Point.Step source 0)
    (reference : Owner referenceParameter)
    (sameParameter : referenceParameter = (Paths.polynomial (parameter + 0)).eval point)
    (sameBox : reference.track.initial.box = patch.base.seed.owner.track.initial.box) :
    NamedEquivalent (ownerRootName reference.parameterNonzero reference) step.root.value.name := by
  let actual := castOwnerParameter sameParameter.symm step.owner
  have actualBox := castOwnerParameter_initial_box sameParameter.symm step.owner
  have refines : actual.track.initial.box.Refines reference.track.initial.box := by
    rewrite [actualBox, sameBox]
    exact step.refines.trans source.refines
  let compared := Riemann.Branches.PreparedPrimitiveSheets.rootEquivalent_of_initial_refines
    reference.parameterNonzero reference.track actual.track refines
  have actualName : ownerRootName actual.parameterNonzero actual = step.root.value.name :=
    (SquareRootTrackEquivalence.ownerRootName_castOwnerParameter sameParameter.symm step.owner).trans
      (congrArg (fun certificate : CertifiedSquareRoot.Certificate
          ((Paths.polynomial (parameter + 0)).eval point) => certificate.value.name) step.root_eq).symm
  exact NamedEquivalent.transport rfl actualName compared

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
    {targetCurrent targetFloor targetRootStage : Nat}
    {zeroPaid : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound}
    (zero : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage 0 zeroPaid)

/-- The original two-box PathData type at one literal source finish/following-start occurrence. -/
@[expose] def JunctionPath (roots : RootChain (parent :: parents) root root)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)
    (zero : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage 0 zeroPaid)
    (index : Fin (parent :: parents).length) : Type _ :=
  let next := followingIndex parent parents index
  let left := DependentProduct.get (parent :: parents) zero.member.blocks index
  let right := DependentProduct.get (parent :: parents) zero.member.blocks next
  FixedRootBoxPath.PathData left.comparison.budget right.comparison.budget

/-- Construct the uniform two-seed path from the GIVEN zero member's actual budget caches and source incidence.

The common physical point is the old finish coordinate. Its membership in
both original boxes follows from their actual endpoint coverage and the
closed chain's literal following-point law, including last to first.
-/
def junctionPath (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ allocation.bound)
    (index : Fin (parent :: parents).length) :
    JunctionPath roots widths targetCurrent targetFloor targetRootStage zero index :=
  let next := followingIndex parent parents index
  let left := DependentProduct.get (parent :: parents) zero.member.blocks index
  let right := DependentProduct.get (parent :: parents) zero.member.blocks next
  let first := ranges.entry index
  let last := ranges.entry next
  have samePoint := congrArg (fun point : LiftedPoint 2 => point.coordinate) (following_point chain index)
  have lastInside : ((covered.entry next).val.neighborhood count).box.Contains
      (finishPoint ((parent :: parents)[index.val]'index.isLt)).coordinate :=
    Eq.mp (congrArg ((covered.entry next).val.neighborhood count).box.Contains samePoint)
      (PreparedParent.start_inside (covered.entry next).val count)
  first.overlapPath (parameter := parameter)
    (point := (finishPoint ((parent :: parents)[index.val]'index.isLt)).coordinate)
    (firstCount := count) (lastCount := count)
    (firstPatch := (covered.entry index).val.neighborhood count)
    (lastPatch := (covered.entry next).val.neighborhood count)
    last left.comparison.budget left.comparison.budget_eq
    right.comparison.budget right.comparison.budget_eq
    (PreparedParent.finish_inside (covered.entry index).val count (covered.entry index).property) lastInside
    increment (admitted.trans (allocation.bound_le_entry index))
    (admitted.trans (allocation.bound_le_entry next))

/-- The exact original junction coordinate supplies every retained parameter-path point. -/
theorem junctionPath_point (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ allocation.bound)
    (index : Fin (parent :: parents).length) (time : Rational) :
    (zero.junctionPath (roots := roots) (widths := widths)
      (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
      increment admitted index).point time =
      (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval
        (finishPoint ((parent :: parents)[index.val]'index.isLt)).coordinate := by
  unfold junctionPath
  exact Variation.Point.Range.overlapPath_point _ _ _ _ _ _ _ _ _ _ _ time

/-- The actual increment and the literal junction's affine coefficient give the retained variation scale. -/
theorem junctionPath_scale (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ allocation.bound)
    (index : Fin (parent :: parents).length) :
    (zero.junctionPath (roots := roots) (widths := widths)
      (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
      increment admitted index).scale = Norm.Basic.normSq increment *
      Norm.Basic.normSq (Polynomials.baseValue
        (finishPoint ((parent :: parents)[index.val]'index.isLt)).coordinate) := by
  unfold junctionPath
  exact Variation.Point.Range.overlapPath_scale _ _ _ _ _ _ _ _ _ _ _

/-- One actual uniform junction path, its complete factory, both queried zero-time Owners and derived continuation.

The start certificate is derived from the original source RootChain and
the GIVEN zero member's actual Steps. The ending operational comparison
uses the original PathData finite continuation, not a new sign premise.
-/
@[expose] def JunctionContinuation (roots : RootChain (parent :: parents) root root)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)
    (zero : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage 0 zeroPaid)
    (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ allocation.bound) (index : Fin (parent :: parents).length) : Type _ :=
  (path : {value : JunctionPath roots widths targetCurrent targetFloor targetRootStage zero index //
    value = zero.junctionPath (roots := roots) (widths := widths)
      (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
      increment admitted index}) ×
  (_first : {value : Owner (path.val.point 0) //
    value = path.val.First 0 ⟨Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩}) ×
  (_last : {value : Owner (path.val.point 0) //
    value = path.val.Second 0 ⟨Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩}) ×
  (_initial : path.val.Agreement 0 ⟨Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩) ×
    path.val.Agreement 1 ⟨instZeroLEOneClass.zero_le_one, Order.Basic.le_refl 1⟩

/-- Derive the source sign from the SAME zero Steps and propagate it on the actual once-bound full parameter path.

Both root queries at time zero are retained with their original First/Second
factories. The endpoint reference comparisons use their real winding-one
boxes and the original source refinements. No Step, source observation,
budget, acquisition, integration mesh or member is produced or replayed.
The original operational continuation computes its finite comparison mesh
when a root-name accuracy is requested.
-/
def junctionContinuation (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ allocation.bound)
    (index : Fin (parent :: parents).length) :
    JunctionContinuation roots widths targetCurrent targetFloor targetRootStage zero increment admitted index := by
  let next := followingIndex parent parents index
  let left := DependentProduct.get (parent :: parents) zero.member.blocks index
  let right := DependentProduct.get (parent :: parents) zero.member.blocks next
  let path : {value : JunctionPath roots widths targetCurrent targetFloor targetRootStage zero index //
      value = zero.junctionPath (roots := roots) (widths := widths)
        (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
        increment admitted index} :=
    ⟨zero.junctionPath (roots := roots) (widths := widths)
      (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
      increment admitted index, rfl⟩
  let first : {value : Owner (path.val.point 0) //
      value = path.val.First 0 ⟨Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩} :=
    ⟨path.val.First 0 ⟨Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩, rfl⟩
  let last : {value : Owner (path.val.point 0) //
      value = path.val.Second 0 ⟨Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩} :=
    ⟨path.val.Second 0 ⟨Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩, rfl⟩
  have firstBox : first.val.track.initial.box =
      ((covered.entry index).val.neighborhood count).base.seed.owner.track.initial.box :=
    (congrArg (fun owner : Owner (path.val.point 0) => owner.track.initial.box) first.property).trans
      (path.val.first_box 0 ⟨Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩)
  have lastBox : last.val.track.initial.box =
      ((covered.entry next).val.neighborhood count).base.seed.owner.track.initial.box :=
    (congrArg (fun owner : Owner (path.val.point 0) => owner.track.initial.box) last.property).trans
      (path.val.second_box 0 ⟨Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩)
  have atZero : path.val.point 0 = (Paths.polynomial (parameter + 0)).eval
      (finishPoint ((parent :: parents)[index.val]'index.isLt)).coordinate :=
    (zero.junctionPath_point (roots := roots) (widths := widths)
      (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
      increment admitted index 0).trans
      (congrArg (fun offset : Canonical => (Paths.polynomial (parameter + offset)).eval
        (finishPoint ((parent :: parents)[index.val]'index.isLt)).coordinate) (Basic.zero_mul increment))
  have following := congrArg (fun point : LiftedPoint 2 => point.coordinate) (following_point chain index)
  have lastParameter : path.val.point 0 = (Paths.polynomial (parameter + 0)).eval
      (startPoint ((parent :: parents)[next.val]'next.isLt)).coordinate :=
    atZero.trans (congrArg (Paths.polynomial (parameter + 0)).eval following.symm)
  let firstToStep := reference_zeroStep (parameter := parameter)
    (point := (finishPoint ((parent :: parents)[index.val]'index.isLt)).coordinate) (count := count)
    (patch := (covered.entry index).val.neighborhood count) (source := (source.prepared.entry index).lastSample)
    left.last first.val atZero firstBox
  let lastToStep := reference_zeroStep (parameter := parameter)
    (point := (startPoint ((parent :: parents)[next.val]'next.isLt)).coordinate) (count := count)
    (patch := (covered.entry next).val.neighborhood count) (source := (source.prepared.entry next).firstSample)
    right.first last.val lastParameter lastBox
  let linked := ShiftedGeometry.followingSteps (parameter := parameter) (frame := frame) (basis := basis)
    (offset := (0 : Canonical)) (parent := parent) (parents := parents)
    (count := count) (floor := floor) (covered := covered) (path := chain.path)
    (stage := source.selected.stage) (targets := source.targets) (root := root)
    source.prepared chain roots index left.last right.first
  have firstName : ownerRootName first.val.parameterNonzero first.val =
      ownerRootName (path.val.nonzero 0 ⟨Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩)
        (path.val.First 0 ⟨Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩) :=
    congrArg (fun owner : Owner (path.val.point 0) => ownerRootName owner.parameterNonzero owner) first.property
  have lastName : ownerRootName last.val.parameterNonzero last.val =
      ownerRootName (path.val.nonzero 0 ⟨Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩)
        (path.val.Second 0 ⟨Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩) :=
    congrArg (fun owner : Owner (path.val.point 0) => ownerRootName owner.parameterNonzero owner) last.property
  let initial : path.val.Agreement 0 ⟨Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩ := by
    unfold FixedRootBoxPath.PathData.Agreement
    exact NamedEquivalent.transport firstName lastName (firstToStep.trans (linked.trans lastToStep.symm))
  let final := path.val.equivalent initial
  exact ⟨path, first, last, initial, final⟩

namespace JunctionContinuation

variable {zero}
variable {increment : Canonical} {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
variable {index : Fin (parent :: parents).length}
variable (continued : JunctionContinuation roots widths targetCurrent targetFloor targetRootStage
  zero increment admitted index)

/-- Read the SAME actual once-constructed two-original-budget parameter path. -/
@[expose] def path : JunctionPath roots widths targetCurrent targetFloor targetRootStage zero index := continued.1.val

/-- The full path is exactly its original given-zero-member junction factory. -/
theorem path_eq : continued.path = zero.junctionPath (roots := roots) (widths := widths)
    (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
    increment admitted index := continued.1.property

/-- Read the actual first zero-time queried Owner, retaining its track and original signed root box. -/
@[expose] def first : Owner (continued.path.point 0) := continued.2.1.val

/-- The first queried Owner is the original path's whole First factory. -/
theorem first_eq : continued.first =
    continued.path.First 0 ⟨Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩ := continued.2.1.property

/-- Read the actual independent second zero-time queried Owner without replacing either seed. -/
@[expose] def last : Owner (continued.path.point 0) := continued.2.2.1.val

/-- The second queried Owner is the original path's whole Second factory. -/
theorem last_eq : continued.last =
    continued.path.Second 0 ⟨Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩ := continued.2.2.1.property

/-- The first actual queried Owner retains the literal original left seed box. -/
theorem first_box : continued.first.track.initial.box =
    ((covered.entry index).val.neighborhood count).base.seed.owner.track.initial.box :=
  (congrArg (fun owner : Owner (continued.path.point 0) => owner.track.initial.box) continued.first_eq).trans
    (continued.path.first_box 0 ⟨Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩)

/-- The second actual queried Owner retains the independent original following seed box. -/
theorem last_box : continued.last.track.initial.box =
    ((covered.entry (followingIndex parent parents index)).val.neighborhood count).base.seed.owner.track.initial.box :=
  (congrArg (fun owner : Owner (continued.path.point 0) => owner.track.initial.box) continued.last_eq).trans
    (continued.path.second_box 0 ⟨Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩)

/-- Read the internally derived original zero-time sign between the two actual seed references. -/
def initial : continued.path.Agreement 0 ⟨Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩ :=
  continued.2.2.2.1

/-- Read the actual endpoint agreement computed by the original full-interval finite continuation. -/
def final : continued.path.Agreement 1 ⟨instZeroLEOneClass.zero_le_one, Order.Basic.le_refl 1⟩ :=
  continued.2.2.2.2

/-- Every retained path point is the genuine changed Legendre radicand at the literal old junction. -/
theorem point_eq (time : Rational) : continued.path.point time =
    (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval
      (finishPoint ((parent :: parents)[index.val]'index.isLt)).coordinate :=
  (congrArg (fun value : JunctionPath roots widths targetCurrent targetFloor targetRootStage zero index =>
    value.point time) continued.path_eq).trans
    (zero.junctionPath_point (roots := roots) (widths := widths)
      (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
      increment admitted index time)

/-- The same cached path retains the exact original scalar variation scale. -/
theorem scale_eq : continued.path.scale = Norm.Basic.normSq increment *
    Norm.Basic.normSq (Polynomials.baseValue
      (finishPoint ((parent :: parents)[index.val]'index.isLt)).coordinate) :=
  (congrArg (fun value : JunctionPath roots widths targetCurrent targetFloor targetRootStage zero index =>
    value.scale) continued.path_eq).trans
    (zero.junctionPath_scale (roots := roots) (widths := widths)
      (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
      increment admitted index)

end JunctionContinuation

/-- Retain the whole original source, zero member and root chain beside each literal junction continuation. -/
@[expose] def JunctionContinuations (roots : RootChain (parent :: parents) root root)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)
    (zero : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage 0 zeroPaid)
    (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ allocation.bound) : Type _ :=
  {value : Requested covered chain current floor rootStage reference ×
      LocalMember source ranges allocation roots widths targetCurrent targetFloor targetRootStage 0 zeroPaid ×
      RootChain (parent :: parents) root root × Canonical //
    value = (source, zero, roots, increment)} × DependentProduct (parent :: parents)
      (JunctionContinuation roots widths targetCurrent targetFloor targetRootStage zero increment admitted)

/-- Build the actual finite continuation product in original order, including the true final/first occurrence.

The given zero member and its original target Frame remain unchanged. The
nonempty original index type preserves singleton, repeated and stationary
slots. Only the actual two-box path and its two zero-time root queries are
newly constructed at each junction; derivative/integration stages are absent.
-/
def junctionContinuations (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ allocation.bound) :
    JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted :=
  ⟨⟨(source, zero, roots, increment), rfl⟩, DependentProduct.ofFn (parent :: parents)
    (fun index => zero.junctionContinuation (roots := roots) (widths := widths)
      (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
      increment admitted index)⟩

namespace JunctionContinuations

variable {zero}
variable {increment : Canonical} {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
variable (continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage
  zero increment admitted)

/-- The whole original source, zero member, signed root chain and requested increment remain actual input data. -/
theorem originals_eq : continued.1.val = (source, zero, roots, increment) := continued.1.property

/-- Read the actual retained continuation at one original bounded occurrence without preparing another junction. -/
@[expose] def entry (index : Fin (parent :: parents).length) :
    JunctionContinuation roots widths targetCurrent targetFloor targetRootStage zero increment admitted index :=
  DependentProduct.get (parent :: parents) continued.2 index

end JunctionContinuations

end StageAttempt.Requested.LocalMember

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
