module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Paths.PreparedPathTrace

import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive
import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Cache
public import Purelib.Riemann.Paths.PreparedPathWinding
public import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

/-!
# Root traces attached to cached common-depth integration banks

Trace budgets are selected before preparing a path.  A common smaller root
diameter and a larger dyadic depth satisfy every segment's trace bounds.
The resulting trace consumes the retained `CertifiedDyadic` spine; it does
not construct a second integration path with unrelated terminal owners.
Generated banks may use the same interface and exact fit inequalities.
-/

namespace Purelib.Riemann.Paths.PreparedDyadicTrace.PreparedTraceBudget

open _root_.Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint)

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment polynomial ambient start finish} {left right : Endpoint}

open Purelib.Approximation.Rational in
/-- The first dyadic depth making the retained variation strictly smaller than the positive movement budget. -/
@[expose] def movementDepth (budget : PreparedTraceBudget segment left right) : Nat :=
  Geometric.Search.firstQuarterBelow budget.variation 0 budget.movementBudget

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Paths in
/-- At sufficient depth and a small enough positive diameter, every generated dyadic request fits the retained trace
budget. -/
theorem dyadicRequests_fit_of_movementDepth (budget : PreparedTraceBudget segment left right)
    (ordered : left.parameter ≤ right.parameter) (depth : Nat) (diameter : Fraction.Rational)
    (positive : 0 < diameter)
    (enough : PreparedDyadicTrace.PreparedTraceBudget.movementDepth budget ≤ depth)
    (small : diameter ≤ budget.rootDiameter) :
    budget.RequestsFit left
      (PreparedSheetContinuation.Subdivision.dyadicRequests depth left right diameter positive) := by
  have variationNonnegative : 0 ≤ budget.variation := by
    rw [budget.variation_eq]
    exact ClearSheetContinuation.variationBound_nonneg segment _ _
  have bound : Geometric.Basic.quarterRadius budget.variation depth ≤ budget.movementBudget :=
    (quarterRadius_antitone variationNonnegative enough).trans
      (Geometric.Search.firstQuarterBelow_accurate budget.variation variationNonnegative 0
        budget.movementBudget budget.movementBudget_positive).le
  exact budget.dyadicRequests_fit_of_variation ordered depth diameter positive small bound

end Purelib.Riemann.Paths.PreparedDyadicTrace.PreparedTraceBudget

namespace Purelib.Riemann.Paths.PreparedDyadicTrace.PreparedClearPathModels

open _root_.Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedClearPathModels (zeroEndpoint oneEndpoint PreparedPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- Trace budgets indexed by the exact ordered clear-path segments.

Each nonempty entry retains the head segment's endpoint budget and the recursively indexed tail budgets. -/
inductive PathTraceBudgets {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} :
    {start finish : Basic.Canonical} → Polynomial.Geometry.ClearPath polynomial ambient start finish → Type
  /-- The empty trace-budget family at one retained path point. -/ | nil (point : Basic.Canonical) : PathTraceBudgets
    (.nil point)
  /-- The head segment's budget followed by budgets for the exact remaining path. -/ | cons {start middle finish :
    Basic.Canonical} {head : Geometry.ClearPath.ClearSegment polynomial ambient start middle}
      {tail : Polynomial.Geometry.ClearPath polynomial ambient middle finish}
      (budget : PreparedTraceBudget head zeroEndpoint oneEndpoint)
      (remaining : PathTraceBudgets tail) : PathTraceBudgets (.cons head tail)

constructive_injectivity PathTraceBudgets

namespace PathTraceBudgets

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box}

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- Construct the trace budget for every original clear-path segment in order. -/
@[expose] def build : ∀ {start finish : Basic.Canonical} (path : Polynomial.Geometry.ClearPath polynomial ambient start
  finish), PathTraceBudgets path
  | _, _, .nil point => .nil point
  | _, _, .cons head tail => .cons (PreparedTraceBudget.build head zeroEndpoint oneEndpoint) (build tail)

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial
/-- The positive minimum root-diameter request across the retained path budgets, with one for an empty path. -/
@[expose] def diameter : ∀ {start finish : Basic.Canonical} {path : Polynomial.Geometry.ClearPath polynomial ambient
  start finish},
    PathTraceBudgets path → Fraction.Rational
  | _, _, _, .nil _ => 1
  | _, _, _, .cons budget remaining => min budget.rootDiameter remaining.diameter

/-- The retained path's minimum root-diameter request is strictly positive.

The empty path retains the unit diameter. Each nonempty path keeps the exact minimum of its head request and tail
request, and both retained requests are strictly positive. -/
theorem diameter_positive : ∀ {start finish : Basic.Canonical} {path : Polynomial.Geometry.ClearPath polynomial ambient
  start finish}
    (budgets : PathTraceBudgets path), 0 < budgets.diameter
  | _, _, _, .nil _ => by change (0 : Fraction.Rational) < 1; decide
  | _, _, _, .cons budget remaining => Fraction.Order.Basic.lt_min budget.rootDiameter_positive
    remaining.diameter_positive

end

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- The maximum required dyadic movement depth over the retained path budgets. -/
@[expose] def movementDepth : ∀ {start finish : Basic.Canonical} {path : Polynomial.Geometry.ClearPath polynomial
  ambient
  start finish},
    PathTraceBudgets path → Nat
  | _, _, _, .nil _ => 0
  | _, _, _, .cons budget remaining =>
      max (PreparedDyadicTrace.PreparedTraceBudget.movementDepth budget) remaining.movementDepth

end PathTraceBudgets

namespace PreparedPath

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
set_option genInjectivity false in
/-- An owner path tracing the exact prepared path with matching raw winding.

Its terminal owner is the prepared path's actual finishing owner, and the winding identity refers to the original clear
path. -/
structure Tracing {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {start finish :
  Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} {owner : Owner (polynomial.eval start)}
    (prepared : PreparedPath path owner) where
  /-- The owner trace from the original start owner to the prepared path's terminal owner. -/ trace : OwnerPath
    polynomial start owner finish (PreparedPathGluing.finishOwner prepared)
  /-- The trace polygon's raw winding equals the original clear path's raw winding. -/ winding_eq :
    Winding.Polygon.Basic.chainRaw polynomial start trace.vertices = PreparedPathWinding.ClearPath.rawWinding path

constructive_injectivity Tracing

end PreparedPath

namespace PathTraceBudgets

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box}

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
open Purelib.Data.Nat in
/-- Trace the retained dyadic preparation using its exact segment budgets.

The supplied lower depth bound and upper diameter bound certify each original request; head and tail owner traces are
appended with their winding identities preserved. -/
@[expose] def tracePrepared (depth : Nat) (diameter : Fraction.Rational) (positive : 0 < diameter) :
    ∀ {start finish : Basic.Canonical} {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
      {owner : Owner (polynomial.eval start)} (prepared : PreparedPath path owner)
      (budgets : PathTraceBudgets path), PreparedPath.AllRequestsDyadic depth diameter positive prepared →
        budgets.movementDepth ≤ depth → diameter ≤ budgets.diameter →
          PreparedDyadicTrace.PreparedClearPathModels.PreparedPath.Tracing prepared
  | _, _, _, _, .nil point owner, _, _, _, _ => ⟨.nil point owner, rfl⟩
  | start, _, _, _, .cons head tail owner within first rest, budgets, generated, enough, small => by
      cases budgets with
      | cons budget tailBudgets =>
          have headBound : PreparedDyadicTrace.PreparedTraceBudget.movementDepth budget ≤
              max (PreparedDyadicTrace.PreparedTraceBudget.movementDepth budget) tailBudgets.movementDepth := by
            rw [Order.max_eq_natMax]
            exact Order.le_max_left _ _
          have tailBound : tailBudgets.movementDepth ≤
              max (PreparedDyadicTrace.PreparedTraceBudget.movementDepth budget) tailBudgets.movementDepth := by
            rw [Order.max_eq_natMax]
            exact Order.le_max_right _ _
          have headEnough : PreparedDyadicTrace.PreparedTraceBudget.movementDepth budget ≤ depth :=
            headBound.trans enough
          have tailEnough : tailBudgets.movementDepth ≤ depth := tailBound.trans enough
          have headSmall : diameter ≤ budget.rootDiameter := small.trans (Fraction.Order.Basic.min_le_left _ _)
          have tailSmall : diameter ≤ tailBudgets.diameter := small.trans (Fraction.Order.Basic.min_le_right _ _)
          have fits : budget.RequestsFit zeroEndpoint first.subdivision.requests := by
            rw [generated.1]
            exact PreparedDyadicTrace.PreparedTraceBudget.dyadicRequests_fit_of_movementDepth
              budget (by decide) depth diameter positive headEnough headSmall
          let headTrace := PreparedPathTrace.CompleteSegment.ownerPath first budget fits
          let tailTrace := tracePrepared depth diameter positive rest tailBudgets generated.2 tailEnough tailSmall
          exact
            { trace := headTrace.append tailTrace.trace
              winding_eq := by
                change Winding.Polygon.Basic.chainRaw polynomial start (headTrace.append tailTrace.trace).vertices =
                  PreparedPathWinding.ClearSegment.rawWinding head + PreparedPathWinding.ClearPath.rawWinding tail
                rw [OwnerPath.append_vertices, Winding.Polygon.Basic.chainRaw_append, headTrace.vertices_terminal,
                  PreparedPathTrace.CompleteSegment.ownerPath_chainRaw first budget fits,
                    PreparedPathWinding.PreparedClearPathModels.CompleteSegment.moving_winding first,
                    tailTrace.winding_eq]
                }

end PathTraceBudgets

end Purelib.Riemann.Paths.PreparedDyadicTrace.PreparedClearPathModels

namespace Purelib.Riemann.Paths.PreparedDyadicTrace.PreparedCycleModels

open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Paths.PreparedClearPathModels
open Purelib.Riemann.Readings.PreparedBoundaryGluing (FinishedDyadic)
open Purelib.Riemann.Paths.PreparedDyadicTrace.PreparedClearPathModels (PathTraceBudgets)

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
set_option genInjectivity false in
/-- A retained finished dyadic bank with an owner trace for its exact cached preparation.

The bank carries its original dyadic preparation and finishing owner. Its trace reads that same cached certificate, with
winding and owner handoff tied to the exact supplied path. -/
structure TracedFinishedDyadic {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    {start finish : Gaussian} (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (owner : Owner (polynomial.eval start)) (diameter : Fraction.Rational) (positive : 0 < diameter) where
  /-- The retained finished dyadic bank with its exact terminal-owner identity. -/ bank : FinishedDyadic path owner
    diameter positive
  /-- The owner trace and winding certificate for that exact cached bank. -/ tracing :
    PreparedDyadicTrace.PreparedClearPathModels.PreparedPath.Tracing bank.certificate.prepared

constructive_injectivity TracedFinishedDyadic

namespace TracedFinishedDyadic

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Attach a certified owner trace to the supplied finished bank under its depth and diameter bounds. -/
@[expose] def ofBank {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} {owner : Owner (polynomial.eval start)}
    {diameter : Fraction.Rational} {positive : 0 < diameter}
    (budgets : PathTraceBudgets path) (bank : FinishedDyadic path owner diameter positive)
    (enough : budgets.movementDepth ≤ bank.depth) (small : diameter ≤ budgets.diameter) :
    TracedFinishedDyadic path owner diameter positive :=
  ⟨bank, PathTraceBudgets.tracePrepared bank.depth diameter positive bank.certificate.prepared budgets
    bank.certificate.generated enough small⟩

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
open Purelib.RootIsolation in
/-- Prepare a traced bank starting at the retained movement-depth floor.

Adaptive selection preserves that floor; the selected bank is cached once and traced against the exact supplied path
budgets and positive diameter. -/
@[expose] def total {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient
  : Box} {start finish : Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) (within : path.WithinAmbient)
    (owner : Owner (polynomial.eval start)) (budgets : PathTraceBudgets path)
    (diameter : Fraction.Rational) (positive : 0 < diameter) (small : diameter ≤ budgets.diameter) :
    TracedFinishedDyadic path owner diameter positive :=
  let selected := SquareRoot.Preparation.Bank.Adaptive.selectFrom
    [SquareRoot.Preparation.Bank.Adaptive.Task.ofPath path within owner] diameter positive budgets.movementDepth
  let certificate := SquareRoot.Preparation.Bank.Cache.DyadicBank.cache selected.banks.head
  let bank : FinishedDyadic path owner diameter positive :=
    ⟨selected.depth, certificate, PreparedPathGluing.finishOwner certificate.prepared, rfl⟩
  ofBank budgets bank selected.minimum_le small

end TracedFinishedDyadic

end Purelib.Riemann.Paths.PreparedDyadicTrace.PreparedCycleModels
