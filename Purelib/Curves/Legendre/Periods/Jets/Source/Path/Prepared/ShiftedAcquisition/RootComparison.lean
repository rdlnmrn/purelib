module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.RootPath
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Riemann.Branches.PreparedPrimitiveSheets
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Norm.Basic

/-! # Signed finish comparison on the same actual shifted physical parent

The original whole-box strip payment supplies one retained Budget on the
same original seed. Every actual point of the SAME shifted acquisition
lies in that original physical box. The actual materialized OwnerPath
supplies its moving/retention Owners; one cached comparison fold therefore
compares its finish with an independently retained endpoint Point.Step.
No acquisition, continuation, endpoint query or advance is replayed, and no
shifted patch or desired finishing comparison is assumed.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

attribute [local irreducible] CertifiedSquareRoot.rawRoot

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {range : Variation.Point.Range (patch.neighborhood count)} {target : Paths.Frame (parameter + increment)}
    {admitted : Norm.Basic.normSq increment ≤ range.shiftedBound}
    {firstSample : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate}
    {firstStep : Variation.Point.Step firstSample increment} {width : AccuracyRequest}
    (retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width)
    (strip : Norm.Basic.normSq increment ≤ range.stripBound)

include strip in
/-- The SAME shifted segment satisfies the original seed's computed whole-strip movement bound. -/
theorem strip_movement
    (budget : FixedRootBoxBudget.Budget (patch.neighborhood count).base.seed.owner)
    (budget_eq : budget = range.seedBudget) (time : Rational) (inside : Inside time) :
    Norm.Basic.normSq ((Paths.polynomial parameter).eval (patch.neighborhood count).base.site.center -
      (Fibre.frameCurve target).polynomial.eval (retained.segment.pointAt time)) ≤ budget.movement := by
  have bounded := range.seed_movement_le
    (retained.segment.pointAt_contains retained.within time inside) increment strip
  rewrite [budget_eq, range.seedBudget_movement]
  exact bounded

variable (actual : OwnerPath (Fibre.frameCurve target).polynomial (startPoint parent).coordinate firstStep.owner
    (finishPoint parent).coordinate retained.acquired.traced.finishOwner)
    (actual_eq : actual = retained.acquired.traced.trace.get)

/-- One original strip Budget, initial reference and actual shifted-subdivision comparison cache.

The same materialized acquisition trace is an index. The whole factory
identities retain the original seed, actual first Point.Step, physical
endpoints, sheet occurrence and stored width-paid acquisition. Its
independent endpoint references are shared across the original requests.
-/
@[expose] def RootComparison :=
  (budget : { value : FixedRootBoxBudget.Budget (patch.neighborhood count).base.seed.owner //
    value = range.seedBudget }) ×
  (_first : { value : Owner ((Fibre.frameCurve target).polynomial.eval (startPoint parent).coordinate) //
    value = range.seedOwner budget.val budget.property (start_inside patch count) increment strip }) ×
  { paths : Acquisition.Segment.RootComparisons (Fibre.frameCurve target) basis retained.acquired
      actual actual_eq parent.edge.sheet budget.val (retained.strip_movement strip budget.val budget.property) //
    paths = Acquisition.Segment.RootComparisons.build }

namespace RootComparison

variable {retained strip actual actual_eq}

/-- Materialize one whole-strip Budget and one shared reference spine on the SAME already acquired physical parent. -/
def build : RootComparison retained strip actual actual_eq :=
  let budget := range.seedBudget
  let first := range.seedOwner budget rfl (start_inside patch count) increment strip
  let paths := Acquisition.Segment.RootComparisons.build
    (curve := Fibre.frameCurve target) (differential := basis) (retained := retained.acquired)
    (actual := actual) (actual_eq := actual_eq) (sheet := parent.edge.sheet)
    (second := budget) (movement := retained.strip_movement strip budget rfl)
  ⟨⟨budget, rfl⟩, ⟨first, rfl⟩, ⟨paths, rfl⟩⟩

variable (comparison : RootComparison retained strip actual actual_eq)

/-- Read the single cached Budget on the literal original neighborhood seed. -/
@[expose] def budget : FixedRootBoxBudget.Budget (patch.neighborhood count).base.seed.owner := comparison.1.val

/-- The complete cached Budget is the original whole-strip factory. -/
theorem budget_eq : comparison.budget = range.seedBudget := comparison.1.property

/-- Read the retained original first physical endpoint reference, without another root query or budget execution. -/
@[expose] def firstReference : Owner ((Fibre.frameCurve target).polynomial.eval (startPoint parent).coordinate) :=
  comparison.2.1.val

/-- The cached first reference is the original seed-owner factory on the same actual increment and endpoint. -/
theorem firstReference_eq : comparison.firstReference = range.seedOwner comparison.budget comparison.budget_eq
    (start_inside patch count) increment strip := comparison.2.1.property

/-- Read the same actual original-subdivision comparison cache with every retained moving and tail Owner. -/
@[expose] def paths : Acquisition.Segment.RootComparisons (Fibre.frameCurve target) basis retained.acquired
    actual actual_eq parent.edge.sheet comparison.budget
    (retained.strip_movement strip comparison.budget comparison.budget_eq) := comparison.2.2.val

/-- The complete path/reference cache is the original once-built comparison spine on these identical inputs. -/
theorem paths_eq : comparison.paths = Acquisition.Segment.RootComparisons.build := comparison.2.2.property

/-- The original strip's first reference has exactly the literal original seed box. -/
theorem firstReference_box : comparison.firstReference.track.initial.box =
    (patch.neighborhood count).base.seed.owner.track.initial.box := by
  rewrite [comparison.firstReference_eq]
  exact range.seedOwner_box comparison.budget comparison.budget_eq (start_inside patch count) increment strip

/-- Derive initial signed agreement from the actual first Step's retained source/seed refinements. -/
def startEquivalent : NamedEquivalent (ownerRootName firstStep.owner.parameterNonzero firstStep.owner)
    (ownerRootName comparison.firstReference.parameterNonzero comparison.firstReference) := by
  have sourceName : ownerRootName firstStep.owner.parameterNonzero firstStep.owner = firstStep.root.value.name := by
    rewrite [firstStep.root_eq]
    rfl
  have referenceName := congrArg (fun owner : Owner
      ((Fibre.frameCurve target).polynomial.eval (startPoint parent).coordinate) =>
      ownerRootName owner.parameterNonzero owner) comparison.firstReference_eq
  have start := range.seedOwner_stepEquivalent comparison.budget comparison.budget_eq
    (start_inside patch count) increment strip firstStep
  exact NamedEquivalent.transport sourceName.symm referenceName.symm start.symm

/-- Read the same cached finishing reference at the exact original physical target coordinate. -/
def finishReference : Owner ((Fibre.frameCurve target).polynomial.eval (finishPoint parent).coordinate) :=
  comparison.paths.finishReference comparison.firstReference

/-- The actual cached final reference has exactly the SAME original seed box, including an empty original trace. -/
theorem finishReference_box : comparison.finishReference.track.initial.box =
    (patch.neighborhood count).base.seed.owner.track.initial.box := by
  unfold finishReference
  exact comparison.paths.finishReference_box comparison.firstReference comparison.firstReference_box

/-- The same materialized shifted acquisition's actual finish agrees with its cached original-seed reference. -/
def referenceEquivalent : NamedEquivalent
    (ownerRootName retained.acquired.traced.finishOwner.parameterNonzero retained.acquired.traced.finishOwner)
    (ownerRootName comparison.finishReference.parameterNonzero comparison.finishReference) :=
  comparison.paths.finishEquivalent comparison.firstReference
    (by
      rewrite [comparison.firstReference_box]
      exact Geometry.Rational.Box.refines_refl _)
    comparison.startEquivalent

/-- Compare the actual shifted finish with an independently retained Point.Step at the SAME original endpoint.

The final independent Step retains its original source, target Owner and
root certificate. Their certified refinements place it inside the exact
box of the cached finishing reference. The existing original root-track
comparison and derived whole-parent reference comparison compose; no
finishing comparison, source query or advancement is an input.
-/
def finishEquivalent
    {lastSample : ContinuedNeighborhood.Point (patch.neighborhood count) (finishPoint parent).coordinate}
    (lastStep : Variation.Point.Step lastSample increment) :
    NamedEquivalent
      (ownerRootName retained.acquired.traced.finishOwner.parameterNonzero retained.acquired.traced.finishOwner)
      lastStep.root.value.name := by
  have refines : lastStep.owner.track.initial.box.Refines comparison.finishReference.track.initial.box := by
    rewrite [comparison.finishReference_box]
    exact lastStep.refines.trans lastSample.refines
  have compared := PreparedPrimitiveSheets.rootEquivalent_of_initial_refines lastStep.owner.parameterNonzero
    comparison.finishReference.track lastStep.owner.track refines
  have lastName : ownerRootName lastStep.owner.parameterNonzero lastStep.owner = lastStep.root.value.name := by
    rewrite [lastStep.root_eq]
    rfl
  exact comparison.referenceEquivalent.trans (NamedEquivalent.transport rfl lastName compared)

/-- The SAME covered subdivision's actual terminal root agrees with that independent original endpoint Step. -/
def coveredFinishEquivalent
    {lastSample : ContinuedNeighborhood.Point (patch.neighborhood count) (finishPoint parent).coordinate}
    (lastStep : Variation.Point.Step lastSample increment) :
    NamedEquivalent
      (ownerRootName retained.parents.covered.subdivision.terminalOwner.parameterNonzero
        retained.parents.covered.subdivision.terminalOwner) lastStep.root.value.name :=
  NamedEquivalent.transport retained.finish_name_eq rfl (comparison.finishEquivalent lastStep)

end RootComparison

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
