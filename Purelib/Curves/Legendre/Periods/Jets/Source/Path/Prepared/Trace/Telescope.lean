module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Subdivision
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Payment
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Literal stationary and moving primitive increments on one retained subdivision

Both actual stationary handoffs and the original moving error consume the
same old vertex caches. The original subdivision and retained source family
determine the ordered source integral list. Its exact telescope preserves
all source constants through differences, and the cached comparison fold
pays every actual block without another primitive observation.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace

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

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- Two actual stationary errors and the retained source error pay one literal three-link block. -/
private theorem block_payment (first source target last integral : Canonical) (allowance localBound ceiling : Rational)
    (source_le : Norm.Basic.normSq (source - first) ≤ allowance)
    (target_le : Norm.Basic.normSq (last - target) ≤ allowance)
    (moving_le : Norm.Basic.normSq ((target - source) - integral) ≤ 8 * localBound + 4 * ceiling)
    (ceiling_le : ceiling ≤ localBound) (allocation : localBound = 4 * allowance) :
    Norm.Basic.normSq ((last - first) - integral) ≤ 26 * localBound := by
  have stationary := (Norm.Bounds.normSq_add_le_two (source - first) (last - target)).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Order.Arithmetic.add_le_add_direct source_le target_le)
      (of_decide_eq_true rfl : (0 : Rational) ≤ 2))
  have movement : Norm.Basic.normSq ((target - source) - integral) ≤ 12 * localBound := moving_le.trans
    ((Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl (8 * localBound))
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ceiling_le
        (of_decide_eq_true rfl : (0 : Rational) ≤ 4))).trans_eq (by ring1))
  have identity : (last - first) - integral =
      ((target - source) - integral) + ((source - first) + (last - target)) := by ring1
  rewrite [identity]
  have total := (Norm.Bounds.normSq_add_le_two _ _).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct movement stationary) (of_decide_eq_true rfl : (0 : Rational) ≤ 2))
  exact total.trans_eq (by rewrite [allocation]; ring1)

namespace Cache

/-- Read the actual selected original source integral once per retained moving occurrence. -/
@[expose] def integrals (row : Row) :
    {current : Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    Sources (frame := frame) (basis := basis) (targets := targets)
      (count := count) (floor := floor) (sheet := sheet) subdivision → List Canonical
  | _, _, .stop _ _, _ => []
  | _, _, .next _ _ _ _ _ _ remaining, sources => by
      cases sources with
      | mk centers rest =>
        cases rest with
        | mk covered prepared =>
          cases covered with
          | cons _ _ covered =>
            exact (row.cell prepared.1.preparation.models).integralSample ::
              integrals row remaining ⟨centers.2, ⟨covered, prepared.2⟩⟩
termination_by structural _ _ subdivision _ => subdivision

/-- The actual integral list contains one unchanged original row sample for each retained subdivision request. -/
theorem integrals_length (row : Row) : ∀ {current : Endpoint}
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current owner)
    (sources : Sources (frame := frame) (basis := basis) (targets := targets)
        (count := count) (floor := floor) (sheet := sheet) subdivision),
    (integrals row (frame := frame) (basis := basis) subdivision sources).length = subdivision.requests.length
  | _, _, .stop _ _, _ => rfl
  | _, _, .next _ _ _ _ _ _ remaining, sources => by
      cases sources with
      | mk centers rest =>
        cases rest with
        | mk covered prepared =>
          cases covered with
          | cons _ _ covered =>
            exact congrArg Nat.succ (integrals_length row remaining ⟨centers.2, ⟨covered, prepared.2⟩⟩)
termination_by structural _ _ subdivision _ => subdivision

/-- Record each actual full old three-link increment minus its SAME original source integral.

The literal source-stationary/moving/target-stationary occurrences retain
their production roles even when a moving link has coincident base points.
-/
@[expose] def blockErrors (row : Row) (budget : PreparedTraceBudget segment left right)
    (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    {current : Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (sources : Sources (frame := frame) (basis := basis) (targets := targets)
        (count := count) (floor := floor) (sheet := sheet) subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (first : ObservedVertex row (accuracy := accuracy) (segment.pointAt current.parameter) owner) →
    (observed : Observations row budget subdivision fits first) →
    Cache row (frame := frame) (basis := basis) budget allocation subdivision sources fits first observed → List
      Canonical
  | _, _, .stop _ _, _, _, _, _, _ => []
  | _, _, .next _ _ _ _ _ _ remaining, sources, fits, first, observed, retained => by
      cases sources with
      | mk centers rest =>
        cases rest with
        | mk covered prepared =>
          cases covered with
          | cons _ _ covered =>
            exact ((observed.2.2.2.2.1.value - first.value) - (row.cell prepared.1.preparation.models).integralSample)
              ::
              blockErrors row budget allocation remaining ⟨centers.2, ⟨covered, prepared.2⟩⟩ fits.2.2
                observed.2.2.2.2.1 observed.2.2.2.2.2.2 retained.2
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

/-- The actual complete-block error list has the SAME original moving-request count. -/
theorem blockErrors_length (row : Row) (budget : PreparedTraceBudget segment left right)
    (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    ∀ {current : Endpoint}
      {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
      (subdivision : Subdivision segment within current owner)
      (sources : Sources (frame := frame) (basis := basis) (targets := targets)
        (count := count) (floor := floor) (sheet := sheet) subdivision)
      (fits : budget.RequestsFit current subdivision.requests)
      (first : ObservedVertex row (accuracy := accuracy) (segment.pointAt current.parameter) owner)
      (observed : Observations row budget subdivision fits first)
      (retained : Cache row (frame := frame) (basis := basis) budget allocation subdivision sources fits first
        observed),
      (blockErrors row (frame := frame) (basis := basis)
          budget allocation subdivision sources fits first observed retained).length =
        subdivision.requests.length
  | _, _, .stop _ _, _, _, _, _, _ => rfl
  | _, _, .next _ _ _ _ _ _ remaining, sources, fits, _first, observed, retained => by
      cases sources with
      | mk centers rest =>
        cases rest with
        | mk covered prepared =>
          cases covered with
          | cons _ _ covered =>
            exact congrArg Nat.succ (blockErrors_length row budget allocation remaining
              ⟨centers.2, ⟨covered, prepared.2⟩⟩ fits.2.2
              observed.2.2.2.2.1 observed.2.2.2.2.2.2 retained.2)
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

/-- The literal stationary handoffs and existing moving comparisons pay every original complete block. -/
theorem blockErrors_bounded (row : Row) (budget : PreparedTraceBudget segment left right)
    (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    ∀ {current : Endpoint}
      {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
      (subdivision : Subdivision segment within current owner)
      (sources : Sources (frame := frame) (basis := basis) (targets := targets)
        (count := count) (floor := floor) (sheet := sheet) subdivision)
      (fits : budget.RequestsFit current subdivision.requests)
      (first : ObservedVertex row (accuracy := accuracy) (segment.pointAt current.parameter) owner)
      (observed : Observations row budget subdivision fits first)
      (retained : Cache row (frame := frame) (basis := basis) budget allocation subdivision sources fits first
        observed),
      ∀ error ∈ blockErrors row (frame := frame) (basis := basis)
          budget allocation subdivision sources fits first observed retained,
        Norm.Basic.normSq error ≤ 26 * targets.endpoint
  | _, _, .stop _ _, _, _, _, _, _, _, member => by cases member
  | _, _, .next _ _ _ _ _ _ remaining, sources, fits, first, observed,
      retained, _, member => by
      cases sources with
      | mk centers rest =>
        cases rest with
        | mk covered prepared =>
          cases covered with
          | cons _ _ covered =>
            cases member with
            | head =>
                have source := observed.2.1.jump_lt.le
                rewrite [observed.2.1.jump_eq_of_same rfl] at source
                have target := observed.2.2.2.2.2.1.jump_lt.le
                rewrite [observed.2.2.2.2.2.1.jump_eq_of_same rfl] at target
                have moving := PreparedParent.increment_le (row := row) retained.1
                have ceiling := PreparedParent.bound_le_endpoint prepared.1
                exact block_payment first.value observed.1.value observed.2.2.1.value observed.2.2.2.2.1.value
                  (row.cell prepared.1.preparation.models).integralSample accuracy.tolerance targets.endpoint
                  prepared.1.preparation.cell.primitives.bound source target moving ceiling allocation
            | tail _ member =>
                exact blockErrors_bounded row budget allocation remaining ⟨centers.2, ⟨covered, prepared.2⟩⟩ fits.2.2
                  observed.2.2.2.2.1 observed.2.2.2.2.2.2 retained.2 _ member
termination_by structural _ _ subdivision _ _ _ _ _ _ _ => subdivision

/-- The actual complete-block sum is exactly the last-minus-first old value minus the SAME retained source integrals.

Every interior old value cancels against its literal next source. Only
oriented increments of the actual source polynomials occur, so their local
additive constants are unchanged and cancel inside each original error.
-/
theorem blockErrors_sum_eq (row : Row) (budget : PreparedTraceBudget segment left right)
    (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    ∀ {current : Endpoint}
      {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
      (subdivision : Subdivision segment within current owner)
      (sources : Sources (frame := frame) (basis := basis) (targets := targets)
        (count := count) (floor := floor) (sheet := sheet) subdivision)
      (fits : budget.RequestsFit current subdivision.requests)
      (first : ObservedVertex row (accuracy := accuracy) (segment.pointAt current.parameter) owner)
      (observed : Observations row budget subdivision fits first)
      (retained : Cache row (frame := frame) (basis := basis) budget allocation subdivision sources fits first
        observed),
      Norm.Sum.Basic.gaussianSum (blockErrors row (frame := frame) (basis := basis)
          budget allocation subdivision sources fits first observed retained) =
        (Primitive.Tail.last (PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath budget
          subdivision fits) first observed).value - first.value -
          Norm.Sum.Basic.gaussianSum (integrals row (frame := frame) (basis := basis) subdivision sources)
  | _, _, .stop _ _, _, _, first, _, _ => by
      change (0 : Canonical) = first.value - first.value - 0
      ring1
  | _, _, .next _ _ _ _ _ _ remaining, sources, fits, first, observed, retained => by
      cases sources with
      | mk centers rest =>
        cases rest with
        | mk covered prepared =>
          cases covered with
          | cons _ _ covered =>
            have tail := blockErrors_sum_eq row budget allocation remaining ⟨centers.2, ⟨covered, prepared.2⟩⟩ fits.2.2
              observed.2.2.2.2.1 observed.2.2.2.2.2.2 retained.2
            change ((observed.2.2.2.2.1.value - first.value) - (row.cell
              prepared.1.preparation.models).integralSample) +
                Norm.Sum.Basic.gaussianSum (blockErrors row (frame := frame) (basis := basis) budget allocation
                  remaining
                  ⟨centers.2, ⟨covered, prepared.2⟩⟩ fits.2.2 observed.2.2.2.2.1 observed.2.2.2.2.2.2 retained.2) =
              (Primitive.Tail.last (PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath budget remaining fits.2.2)
                observed.2.2.2.2.1 observed.2.2.2.2.2.2).value - first.value -
                ((row.cell prepared.1.preparation.models).integralSample +
                  Norm.Sum.Basic.gaussianSum (integrals row (frame := frame) (basis := basis)
                    remaining ⟨centers.2, ⟨covered, prepared.2⟩⟩))
            rewrite [tail]
            ring1
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

/-- The SAME full old stationary/moving telescope has the derived count-squared source-allocation bound. -/
theorem integral_error_le (row : Row) (budget : PreparedTraceBudget segment left right)
    (allocation : targets.endpoint = 4 * accuracy.tolerance)
    {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current owner)
    (sources : Sources (frame := frame) (basis := basis) (targets := targets)
        (count := count) (floor := floor) (sheet := sheet) subdivision)
    (fits : budget.RequestsFit current subdivision.requests)
    (first : ObservedVertex row (accuracy := accuracy) (segment.pointAt current.parameter) owner)
    (observed : Observations row budget subdivision fits first)
    (retained : Cache row (frame := frame) (basis := basis) budget allocation subdivision sources fits first observed) :
    Norm.Basic.normSq ((Primitive.Tail.last (PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath budget
          subdivision fits) first observed).value - first.value -
      Norm.Sum.Basic.gaussianSum (integrals row (frame := frame) (basis := basis) subdivision sources)) ≤
        (subdivision.requests.length : Rational) *
          ((subdivision.requests.length : Rational) * (26 * targets.endpoint)) := by
  have bounded := Norm.Sum.Bounds.normSq_sum_le
    (blockErrors row (frame := frame) (basis := basis)
          budget allocation subdivision sources fits first observed retained) (26 * targets.endpoint)
    (blockErrors_bounded row (frame := frame) (basis := basis)
          budget allocation subdivision sources fits first observed retained)
  rewrite [blockErrors_length row (frame := frame) (basis := basis)
          budget allocation subdivision sources fits first observed retained,
    blockErrors_sum_eq row (frame := frame) (basis := basis)
          budget allocation subdivision sources fits first observed retained] at bounded
  exact bounded

end Cache

namespace Compared

variable {row : Row}

variable {budget : PreparedTraceBudget segment left right}
variable {allocation : targets.endpoint = 4 * accuracy.tolerance} {current : Endpoint}
variable {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable {subdivision : Subdivision segment within current owner}
variable {originalSources : Sources (frame := frame) (basis := basis) (targets := targets)
  (count := count) (floor := floor) (sheet := sheet) subdivision}
variable {fits : budget.RequestsFit current subdivision.requests}
variable {originalObserved : Primitive.Spine
  (row.expression parameter)
  accuracy (PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath budget subdivision fits)}
variable (retained : Compared row (frame := frame) (basis := basis)
  budget allocation subdivision originalSources fits originalObserved)

/-- Read the SAME original ordered source integral samples without selecting or preparing a source again. -/
@[expose] def integrals : List Canonical :=
  Cache.integrals row (frame := frame) (basis := basis) subdivision retained.sources

/-- Read the actual full-block errors from the identical retained source family, old spine and comparison fold. -/
@[expose] def blockErrors : List Canonical :=
  Cache.blockErrors row (frame := frame) (basis := basis)
    budget allocation subdivision retained.sources fits retained.observed.first retained.observed.2
    retained.cache

/-- The SAME original complete-block list retains the exact actual moving-request count. -/
theorem blockErrors_length : retained.blockErrors.length = subdivision.requests.length :=
  Cache.blockErrors_length row (frame := frame) (basis := basis) budget allocation subdivision retained.sources fits
    retained.observed.first retained.observed.2 retained.cache

/-- The complete actual block sum telescopes on the literal final and first old vertex values. -/
theorem blockErrors_sum_eq : Norm.Sum.Basic.gaussianSum retained.blockErrors =
    retained.observed.last.value - retained.observed.first.value - Norm.Sum.Basic.gaussianSum retained.integrals :=
  Cache.blockErrors_sum_eq row (frame := frame) (basis := basis) budget allocation subdivision retained.sources fits
    retained.observed.first retained.observed.2 retained.cache

/-- The original cached comparisons pay the entire actual stationary/moving source-integral increment. -/
theorem integral_error_le : Norm.Basic.normSq
    (retained.observed.last.value - retained.observed.first.value - Norm.Sum.Basic.gaussianSum retained.integrals) ≤
      (subdivision.requests.length : Rational) * ((subdivision.requests.length : Rational) * (26 * targets.endpoint)) :=
  Cache.integral_error_le row (frame := frame) (basis := basis) budget allocation subdivision retained.sources fits
    retained.observed.first retained.observed.2 retained.cache

end Compared

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace

end
