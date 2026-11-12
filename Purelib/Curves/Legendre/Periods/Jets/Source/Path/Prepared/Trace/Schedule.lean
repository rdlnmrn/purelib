module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Telescope
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Request
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Computed requests for the SAME retained subdivision's complete telescope

The exact original request count pays the finite full-block factor. One
retained original geometric selection chooses a sufficient stage before
new original source models and vertex observations are constructed. Every
selected source and comparison factory consumes the identical old geometry,
covering patches, center states and OwnerPath; earlier observations are
never declared more accurate by choosing a smaller auxiliary request.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
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
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
variable {count floor : Nat} {sheet : Fin 2} {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {left right : Endpoint}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The exact full-block count coefficient is computed from the original binary count coordinate. -/
@[expose] def telescopeScale (size : Nat) : Rational :=
  26 * Budget.Aggregate.countCoordinate size * Budget.Aggregate.countCoordinate size

/-- The binary count coefficient is the SAME two natural-number casts of the original request count. -/
theorem telescopeScale_eq (size : Nat) : telescopeScale size = (size : Rational) * ((size : Rational) * 26) := by
  unfold telescopeScale
  rewrite [Budget.Aggregate.countCoordinate_eq]
  ring1

/-- The finite full-block count coefficient is nonnegative, including an empty original subdivision. -/
theorem telescopeScale_nonnegative (size : Nat) : 0 ≤ telescopeScale size := by
  rewrite [telescopeScale_eq]
  have nonnegative : (0 : Rational) ≤ size :=
    Cast.Order.natCast_le_direct (m := 0) (n := size) (Nat.zero_le size)
  exact Order.Arithmetic.mul_nonneg_direct nonnegative
    (Order.Arithmetic.mul_nonneg_direct nonnegative (of_decide_eq_true rfl : (0 : Rational) ≤ 26))

/-- The finite full-block count and one literal closing jump determine a closed primitive allocation scale. -/
@[expose] def closedScale (size : Nat) : Rational := 2 * (telescopeScale size + 1)

/-- The original closed allocation scale is nonnegative for the actual retained finite request count. -/
theorem closedScale_nonnegative (size : Nat) : 0 ≤ closedScale size :=
  Order.Arithmetic.mul_nonneg_direct (of_decide_eq_true rfl : (0 : Rational) ≤ 2)
    (Order.Arithmetic.add_le_add_direct (telescopeScale_nonnegative size)
      (of_decide_eq_true rfl : (0 : Rational) ≤ 1))

/-- Choose and retain the original finite geometric search that pays the exact same full-block count. -/
@[expose] def select (size current : Nat) (request : AccuracyRequest) :
    Geometric.Search.Selection (telescopeScale size) current request.tolerance :=
  Geometric.Search.Selection.build (telescopeScale size) (telescopeScale_nonnegative size) current
    request.tolerance request.positive

/-- An actual source cache built at the selected stage pays its complete old stationary/moving telescope.

The source target's own decay law and the original retained search supply
the payment. No new bound on the old values or aggregate residual is an
input, and no claim is made about sources built at an earlier stage.
-/
theorem selected_error_lt {row : Row} {currentStage stage : Nat} {accuracy : AccuracyRequest}
    {targets : CellEndpoints.Targets original stage} {current : Endpoint}
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    {budget : PreparedTraceBudget segment left right}
    {subdivision : Subdivision segment within current owner}
    {sources : Sources (frame := frame) (basis := basis) (targets := targets)
      (count := count) (floor := floor) (sheet := sheet) subdivision}
    {fits : budget.RequestsFit current subdivision.requests}
    {allocation : targets.endpoint = 4 * accuracy.tolerance}
    {observed : Primitive.Spine
      (row.expression parameter)
      accuracy (PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath budget subdivision fits)}
    (retained : Compared row (frame := frame) (basis := basis)
    budget allocation subdivision sources fits observed) (request : AccuracyRequest)
    (selection : Geometric.Search.Selection (telescopeScale subdivision.requests.length)
      currentStage request.tolerance) (later : selection.stage ≤ stage) :
    Norm.Basic.normSq
      (retained.observed.last.value - retained.observed.first.value - Norm.Sum.Basic.gaussianSum retained.integrals) <
      request.tolerance := by
  have paid := targets.mul_localBound_le_quarterRadius (telescopeScale subdivision.requests.length)
    (telescopeScale_nonnegative subdivision.requests.length)
  rewrite [← targets.endpoint_eq] at paid
  have exactScale : (subdivision.requests.length : Rational) *
      ((subdivision.requests.length : Rational) * (26 * targets.endpoint)) =
        telescopeScale subdivision.requests.length * targets.endpoint := by
    rewrite [telescopeScale_eq]
    ring1
  have errorBound := retained.integral_error_le
  rewrite [exactScale] at errorBound
  exact errorBound.trans_lt (paid.trans_lt (selection.later_accurate later))

namespace Request

variable (row : Row)

variable (budget : PreparedTraceBudget segment left right)
variable {current : Endpoint}
variable {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable (subdivision : Subdivision segment within current owner)
variable (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision)
variable (covered : CoveredParents count (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers))
variable (fits : budget.RequestsFit current subdivision.requests)
variable (path : OwnerPath (Paths.polynomial parameter) (segment.pointAt current.parameter) owner
  (segment.pointAt subdivision.endpoint.parameter) subdivision.terminalOwner)
variable (path_eq : path = PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath budget subdivision fits)
variable (requestedFloor currentStage : Nat) (request : AccuracyRequest)

/-- The actual chosen search, targets, source models and old-path observation/comparison execution are retained whole.

The original geometric subdivision, center family and covering patches are
inputs. New sources use the computed stage; the actual vertex requests
then use those SAME new source targets. Every complete factory result has
its literal identity, and no old unpaid execution is replaced.
-/
@[expose] def Scheduled :=
  Σ selection : { retained : Geometric.Search.Selection (telescopeScale subdivision.requests.length)
        currentStage request.tolerance // retained = select subdivision.requests.length currentStage request },
    Σ targets : { retained : CellEndpoints.Targets original selection.val.stage //
        retained = CellEndpoints.Targets.build original selection.val.stage },
      Σ prepared : { retained : PreparedParents (frame := frame) (basis := basis) covered requestedFloor targets.val //
          retained = prepareCovered (frame := frame) (basis := basis) covered requestedFloor targets.val },
        Acquisition row (frame := frame) (basis := basis) (targets := targets.val) (count := count)
          (floor := requestedFloor) (sheet := sheet)
          budget subdivision fits path path_eq ⟨centers, covered, prepared.val⟩

/-- Compute a sufficient finite stage and construct genuinely accurate sources and old-path observations once.

The SAME original path, source Owner, subdivisions, requests, center states
and covering patches are retained. Only the new selected source and vertex
request factories run; every subsequent comparison consumes their exact
stored outputs and the existing physical geometry.
-/
def scheduled : Scheduled row (frame := frame) (basis := basis)
    (original := original) budget subdivision centers covered fits path path_eq
    requestedFloor currentStage request :=
  let selection := select subdivision.requests.length currentStage request
  let targets := CellEndpoints.Targets.build original selection.stage
  let prepared := prepareCovered (frame := frame) (basis := basis) covered requestedFloor targets
  let acquired := acquire row (frame := frame) (basis := basis) (targets := targets) (count := count)
    (floor := requestedFloor) (sheet := sheet)
    budget subdivision fits path path_eq ⟨centers, covered, prepared⟩
  ⟨⟨selection, rfl⟩, ⟨⟨targets, rfl⟩, ⟨⟨prepared, rfl⟩, acquired⟩⟩⟩

namespace Scheduled

variable {row : Row}

variable (retained : Scheduled row (frame := frame) (basis := basis)
    (original := original) budget subdivision centers covered fits path path_eq
  requestedFloor currentStage request)

/-- Read the SAME complete original finite search and all retained quotient, fuel and payment data. -/
@[expose] def selection := retained.1.val

/-- Read the actual original source targets computed at that exact selected stage. -/
@[expose] def targets : CellEndpoints.Targets original retained.selection.stage := retained.2.1.val

/-- Read every complete original source cache constructed once on the unchanged original covered parents. -/
@[expose] def prepared : PreparedParents (frame := frame) (basis := basis)
    covered requestedFloor retained.targets := retained.2.2.1.val

/-- Read the complete original observation/comparison acquisition on those identical selected source caches. -/
@[expose] def observations : Acquisition row (frame := frame) (basis := basis) (targets := retained.targets)
    (count := count)
    (floor := requestedFloor) (sheet := sheet) budget subdivision fits path path_eq
      ⟨centers, covered, retained.prepared⟩ := retained.2.2.2

/-- The retained finite selection is the original search factory on the exact original count and request. -/
theorem selection_eq : retained.selection = select subdivision.requests.length currentStage request :=
  retained.1.property

/-- The retained actual target cache is the original target factory at the exact stored stage. -/
theorem targets_eq : retained.targets = CellEndpoints.Targets.build original retained.selection.stage :=
  retained.2.1.property

/-- All stored sources use the identical original cover, request floor and selected targets. -/
theorem prepared_eq : retained.prepared = prepareCovered (frame := frame) (basis := basis)
    covered requestedFloor retained.targets :=
  retained.2.2.1.property

/-- The SAME observed path's actual stationary/moving source-integral residual strictly pays the original request. -/
theorem integral_error_lt : Norm.Basic.normSq
    (retained.observations.compared.observed.last.value - retained.observations.compared.observed.first.value -
      Norm.Sum.Basic.gaussianSum retained.observations.compared.integrals) < request.tolerance :=
  selected_error_lt retained.observations.compared request retained.selection (Nat.le_refl _)

end Scheduled

end Request

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace

end
