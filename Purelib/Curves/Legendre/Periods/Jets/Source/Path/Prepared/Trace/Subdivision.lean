module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Actual source comparisons on the same paid subdivision observation spine

Original center states, covering patches and completed source preparations
are retained together. The original subdivision drives the comparison fold.
Each actual source-stationary/moving/target-stationary triple consumes its
literal two old moving vertices and passes the unchanged third target to
the original tail. No trace, Owner, source model or observation is acquired.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint Subdivision)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates centeredEdges)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {count floor : Nat} {sheet : Fin 2}
variable {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {left right : Endpoint} {accuracy : AccuracyRequest}

namespace PreparedParent

/-- The actual retained original source target pays its cached primitive ceiling without an endpoint admission. -/
theorem bound_le_endpoint
    {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge (Fibre.frameCurve frame) basis}
    {patch : Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    (prepared : PreparedParent patch count floor covered targets) :
    prepared.preparation.cell.primitives.bound ≤ targets.endpoint := by
  have selected := prepared.preparation.cell.primitives.bound_le_selected_target
  have product := congrArg₂ (fun (displacement target : Rational) => displacement * target)
    prepared.displacement_eq prepared.target_eq
  have paid := targets.sourceTarget_payment (PreparedParent.cost parent) (PreparedParent.cost_nonnegative parent)
  exact ((selected.trans_eq product).trans paid.le).trans_eq targets.endpoint_eq.symm

end PreparedParent

namespace PreparedParents.Trace

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The selected original primitive expression's old vertex cache at an arbitrary retained subdivision Owner. -/
abbrev ObservedVertex (row : Row) (point : Canonical) (owner : Owner ((Paths.polynomial parameter).eval point)) :=
  Primitive.Vertex (row.expression parameter)
    point owner accuracy

/-- The complete original center, cover and source caches of the identical actual subdivision.

These are whole supplied objects, grouped with the original Sigma/Prod
parents. No center, covering seed, source, polynomial or endpoint request
is rebuilt by retaining this view.
-/
@[expose] def Sources {current : Endpoint}
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current owner) :=
  Σ centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision,
    Σ covered : CoveredParents count (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers),
      PreparedParents covered floor targets

/-- The SAME already observed original tail, indexed by the exact original subdivision trace factory. -/
abbrev Observations (row : Row) (budget : PreparedTraceBudget segment left right) {current : Endpoint}
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current owner)
    (fits : budget.RequestsFit current subdivision.requests)
    (first : ObservedVertex row (accuracy := accuracy) (segment.pointAt current.parameter) owner) :=
  Primitive.Tail (row.expression parameter)
    accuracy (PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath budget subdivision fits) first

/-- One exact original endpoint-comparison factory pair per actual retained moving head.

The two old moving vertices follow the source stationary handoff. Recursion
then passes the unchanged target-stationary endpoint and its retained tail.
The original subdivision and complete old observation tail remain indices.
-/
@[expose] def Cache (row : Row) (budget : PreparedTraceBudget segment left right)
    (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    {current : Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor) (sheet := sheet)
      subdivision →
    (fits : budget.RequestsFit current subdivision.requests) →
    (first : ObservedVertex row (accuracy := accuracy) (segment.pointAt current.parameter) owner) →
    Observations row budget subdivision fits first → Type 1
  | _, _, .stop _ _, _, _, _, _ => PUnit
  | _, _, .next _ _ _ _ _ _ remaining, sources, fits, _first, observed => by
      cases sources with
      | mk centers rest =>
        cases rest with
        | mk covered prepared =>
          cases covered with
          | cons _ _ covered =>
            exact PreparedParent.Comparisons row prepared.1 observed.1 observed.2.2.1 allocation ×
              Cache row budget allocation remaining ⟨centers.2, ⟨covered, prepared.2⟩⟩ fits.2.2
                observed.2.2.2.2.1 observed.2.2.2.2.2.2
termination_by structural _ _ subdivision _ _ _ _ => subdivision

namespace Cache

/-- Build each actual moving comparison once while consuming the original old triple and source-cache tails. -/
def build (row : Row) (budget : PreparedTraceBudget segment left right)
    (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    {current : Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (sources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor)
      (sheet := sheet) subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (first : ObservedVertex row (accuracy := accuracy) (segment.pointAt current.parameter) owner) →
    (observed : Observations row budget subdivision fits first) →
      Cache row (frame := frame) (basis := basis) budget allocation subdivision sources fits first observed
  | _, _, .stop _ _, _, _, _, _ => PUnit.unit
  | _, _, .next _ _ _ _ _ _ remaining, sources, fits, _first, observed => by
      cases sources with
      | mk centers rest =>
        cases rest with
        | mk covered prepared =>
          cases covered with
          | cons _ _ covered =>
            let head := PreparedParent.Comparisons.build row prepared.1 observed.1 observed.2.2.1 allocation
            let following := build row budget allocation remaining ⟨centers.2, ⟨covered,
              prepared.2⟩⟩ fits.2.2
              observed.2.2.2.2.1 observed.2.2.2.2.2.2
            exact ⟨head, following⟩
termination_by structural _ _ subdivision _ _ _ _ => subdivision

/-- Read the actual oriented old moving increments minus their SAME cached original row integrals. -/
@[expose] def errors (row : Row) (budget : PreparedTraceBudget segment left right)
    (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    {current : Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (sources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor)
      (sheet := sheet) subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (first : ObservedVertex row (accuracy := accuracy) (segment.pointAt current.parameter) owner) →
    (observed : Observations row budget subdivision fits first) →
    Cache row (frame := frame) (basis := basis) budget allocation subdivision sources fits first observed → List
      Canonical
  | _, _, .stop _ _, _, _, _, _, _ => []
  | _, _, .next _ _ _ _ _ _ remaining, sources, fits, _first, observed, retained => by
      cases sources with
      | mk centers rest =>
        cases rest with
        | mk covered prepared =>
          cases covered with
          | cons _ _ covered =>
            exact ((observed.2.2.1.value - observed.1.value) - (row.cell
              prepared.1.preparation.models).integralSample) ::
              errors row budget allocation remaining ⟨centers.2, ⟨covered, prepared.2⟩⟩ fits.2.2
                observed.2.2.2.2.1 observed.2.2.2.2.2.2 retained.2
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

/-- The ordered error list contains exactly one entry for each original actual moving request. -/
theorem errors_length (row : Row) (budget : PreparedTraceBudget segment left right)
    (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    ∀ {current : Endpoint}
      {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
      (subdivision : Subdivision segment within current owner)
      (sources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor)
        (sheet := sheet) subdivision)
      (fits : budget.RequestsFit current subdivision.requests)
      (first : ObservedVertex row (accuracy := accuracy) (segment.pointAt current.parameter) owner)
      (observed : Observations row budget subdivision fits first)
      (retained : Cache row (frame := frame) (basis := basis) budget allocation subdivision sources fits first
        observed),
      (errors row (frame := frame) (basis := basis) budget allocation subdivision sources fits first observed
        retained).length = subdivision.requests.length
  | _, _, .stop _ _, _, _, _, _, _ => rfl
  | _, _, .next _ _ _ _ _ _ remaining, sources, fits, _first, observed, retained => by
      cases sources with
      | mk centers rest =>
        cases rest with
        | mk covered prepared =>
          cases covered with
          | cons _ _ covered =>
            exact congrArg Nat.succ (errors_length row budget allocation remaining ⟨centers.2,
              covered, prepared.2⟩ fits.2.2
              observed.2.2.2.2.1 observed.2.2.2.2.2.2 retained.2)
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

/-- Every actual moving error obeys the original common endpoint allocation and cached source payment. -/
theorem errors_bounded (row : Row) (budget : PreparedTraceBudget segment left right)
    (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    ∀ {current : Endpoint}
      {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
      (subdivision : Subdivision segment within current owner)
      (sources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor)
        (sheet := sheet) subdivision)
      (fits : budget.RequestsFit current subdivision.requests)
      (first : ObservedVertex row (accuracy := accuracy) (segment.pointAt current.parameter) owner)
      (observed : Observations row budget subdivision fits first)
      (retained : Cache row (frame := frame) (basis := basis) budget allocation subdivision sources fits first
        observed),
      ∀ error ∈ errors row (frame := frame) (basis := basis) budget allocation subdivision sources fits first observed
        retained,
        Norm.Basic.normSq error ≤ 12 * targets.endpoint
  | _, _, .stop _ _, _, _, _, _, _, _, member => by cases member
  | _, _, .next _ _ _ _ _ _ remaining, sources, fits, _first, observed,
      retained, _, member => by
      cases sources with
      | mk centers rest =>
        cases rest with
        | mk covered prepared =>
          cases covered with
          | cons _ _ covered =>
            cases member with
            | head =>
                have paid := PreparedParent.increment_le (row := row) retained.1
                have source := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct prepared.1.bound_le_endpoint
                  (of_decide_eq_true rfl : (0 : Rational) ≤ 4)
                have total := Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl (8 * targets.endpoint)) source
                exact paid.trans (total.trans_eq (by ring1))
            | tail _ member =>
                exact errors_bounded row budget allocation remaining ⟨centers.2, covered,
                  prepared.2⟩ fits.2.2
                  observed.2.2.2.2.1 observed.2.2.2.2.2.2 retained.2 _ member
termination_by structural _ _ subdivision _ _ _ _ _ _ _ => subdivision

/-- The sum of the SAME actual moving errors is paid by the square of the retained original request count. -/
theorem error_sum_le (row : Row) (budget : PreparedTraceBudget segment left right)
    (allocation : targets.endpoint = 4 * accuracy.tolerance)
    {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current owner)
    (sources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor)
      (sheet := sheet) subdivision)
    (fits : budget.RequestsFit current subdivision.requests)
    (first : ObservedVertex row (accuracy := accuracy) (segment.pointAt current.parameter) owner)
    (observed : Observations row budget subdivision fits first)
    (retained : Cache row (frame := frame) (basis := basis) budget allocation subdivision sources fits first observed) :
    Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum
      (errors row (frame := frame) (basis := basis) budget allocation subdivision sources fits first observed
        retained)) ≤
        (subdivision.requests.length : Rational) *
          ((subdivision.requests.length : Rational) * (12 * targets.endpoint)) := by
  have bounded := Norm.Sum.Bounds.normSq_sum_le
    (errors row (frame := frame) (basis := basis) budget allocation subdivision sources fits first observed retained)
      (12
      * targets.endpoint)
    (errors_bounded row (frame := frame) (basis := basis) budget allocation subdivision sources fits first observed
      retained)
  rewrite [errors_length row (frame := frame) (basis := basis) budget allocation subdivision sources fits first observed
    retained] at bounded
  exact bounded

end Cache

/-- The complete retained source family and SAME old primitive spine accompany the newly computed comparisons.

Each original supplied object is stored wholesale with its exact identity.
The comparison cache consumes those literal retained objects; no field copy
or readback equality is presented as execution reuse.
-/
@[expose] def Compared (row : Row) (budget : PreparedTraceBudget segment left right)
    (allocation : targets.endpoint = 4 * accuracy.tolerance)
    {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current owner)
    (sources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor)
      (sheet := sheet) subdivision)
    (fits : budget.RequestsFit current subdivision.requests)
    (observed : Primitive.Spine
      (row.expression parameter)
      accuracy (PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath budget subdivision fits)) :=
  Σ keptSources : { retained : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor
    := floor) (sheet := sheet)
      subdivision // retained = sources },
    Σ keptObserved : { retained : Primitive.Spine
        (row.expression parameter)
        accuracy (PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath budget subdivision fits) // retained =
          observed },
      { retained : Cache row (frame := frame) (basis := basis) budget allocation subdivision keptSources.val fits
        keptObserved.val.first keptObserved.val.2 //
        retained = Cache.build row (frame := frame) (basis := basis) budget allocation subdivision keptSources.val fits
          keptObserved.val.first keptObserved.val.2 }

/-- Consume the SAME old spine and completed sources and retain all actual new original comparison factories. -/
def compare (row : Row) (budget : PreparedTraceBudget segment left right)
    (allocation : targets.endpoint = 4 * accuracy.tolerance)
    {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current owner)
    (sources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor)
      (sheet := sheet) subdivision)
    (fits : budget.RequestsFit current subdivision.requests)
    (observed : Primitive.Spine
      (row.expression parameter)
      accuracy (PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath budget subdivision fits)) : Compared row (frame
        :=
        frame) (basis := basis) budget allocation subdivision sources fits observed :=
  let cache := Cache.build row (frame := frame) (basis := basis) budget allocation subdivision sources fits
    observed.first
    observed.2
  ⟨⟨sources, rfl⟩, ⟨observed, rfl⟩, ⟨cache, rfl⟩⟩

namespace Compared

variable {row : Row}

variable {budget : PreparedTraceBudget segment left right}
variable {allocation : targets.endpoint = 4 * accuracy.tolerance} {current : Endpoint}
variable {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable {subdivision : Subdivision segment within current owner}
variable {originalSources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor :=
  floor) (sheet := sheet) subdivision}
variable {fits : budget.RequestsFit current subdivision.requests}
variable {originalObserved : Primitive.Spine
  (row.expression parameter)
  accuracy (PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath budget subdivision fits)}
variable (retained : Compared row (frame := frame) (basis := basis) budget allocation subdivision originalSources fits
  originalObserved)

/-- Read the complete original source/cover/center family retained unchanged. -/
@[expose] def sources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor :=
  floor) (sheet := sheet) subdivision :=
  retained.1.val

/-- Read the SAME entire old observation spine, including both actual stationary comparisons per original head. -/
@[expose] def observed : Primitive.Spine
    (row.expression parameter)
    accuracy (PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath budget subdivision fits) := retained.2.1.val

/-- Read the whole actual ordered comparison execution on those SAME cached inputs. -/
@[expose] def cache : Cache row (frame := frame) (basis := basis) budget allocation subdivision retained.sources fits
    retained.observed.first retained.observed.2 := retained.2.2.val

/-- The retained source-family object is the complete supplied original input. -/
theorem sources_eq : retained.sources = originalSources := retained.1.property

/-- The retained observation spine is the complete supplied old input. -/
theorem observed_eq : retained.observed = originalObserved := retained.2.1.property

/-- The complete comparison execution is the original fold on the identical retained inputs. -/
theorem cache_eq : retained.cache = Cache.build row (frame := frame) (basis := basis) budget allocation subdivision
  retained.sources fits
    retained.observed.first retained.observed.2 := retained.2.2.property

/-- Read the actual ordered moving-error values from the SAME stored source and comparison caches. -/
@[expose] def errors : List Canonical :=
  Cache.errors row (frame := frame) (basis := basis) budget allocation subdivision retained.sources fits
    retained.observed.first retained.observed.2
    retained.cache

/-- There is one original comparison pair and moving-error occurrence for each retained subdivision request. -/
theorem errors_length : retained.errors.length = subdivision.requests.length :=
  Cache.errors_length row (frame := frame) (basis := basis) budget allocation subdivision retained.sources fits
    retained.observed.first retained.observed.2
    retained.cache

/-- The original request count and source allocation pay the sum of the actual moving-error list. -/
theorem error_sum_le : Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum retained.errors) ≤
    (subdivision.requests.length : Rational) * ((subdivision.requests.length : Rational) * (12 * targets.endpoint)) :=
  Cache.error_sum_le row (frame := frame) (basis := basis) budget allocation subdivision retained.sources fits
    retained.observed.first retained.observed.2
    retained.cache

end Compared

end PreparedParents.Trace

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell

end
