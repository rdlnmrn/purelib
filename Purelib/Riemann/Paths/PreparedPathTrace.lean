module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Int.Arithmetic
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Polynomial.Winding.Polygon.Stationary

public import Purelib.Riemann.Paths.PreparedSubdivisionTrace
public import Purelib.Riemann.Paths.PreparedPathGluing
public import Purelib.RootIsolation.SquareRoot.Preparation.Terminal
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Mathlib.Order.Basic

/-!
# Automatically traced complete prepared paths

The complete-segment and path constructions retain their actual integration
spines.  Root traces end at the very owners passed to the next integration
piece.  Only erased endpoint transports connect local segment parameters to
the displayed Gaussian coordinates; no extra owner is independently selected.
-/

namespace Purelib.Riemann.Paths.PreparedPathTrace

open Purelib.Data

public section

open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.PreparedClearPathModels
open Purelib.RootIsolation.SquareRoot.Preparation.Terminal
open _root_.Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)

namespace CompleteSegment

variable {polynomial : GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box} {start finish : Gaussian}
  {segment : ClearSegment polynomial ambient start finish} {within :
    segment.WithinAmbient}
  {owner : Owner (polynomial.eval start)}

/-- The original ordered moving endpoint vertices of the retained complete segment's request list. -/
@[expose] def movingVertices (prepared : CompleteSegment segment within owner) : List Gaussian :=
  prepared.subdivision.requests.map fun request => segment.pointAt request.endpoint.parameter

open Purelib.Riemann.Paths in
open Purelib.RootIsolation in
/-- Transport the retained subdivision trace to the complete segment's exact original endpoint owners.

The original start and finish point equations and owner identities preserve the cached subdivision while giving the
owner path its nominal endpoint indices. -/
@[expose] def ownerPath (prepared : CompleteSegment segment within owner)
    (budget : PreparedTraceBudget segment zeroEndpoint oneEndpoint)
    (fits : budget.RequestsFit zeroEndpoint prepared.subdivision.requests) :
    OwnerPath polynomial start owner finish prepared.finishOwner :=
  (PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath
    budget prepared.subdivision fits).castEndpoints prepared.start_eq prepared.finish_eq
    (by unfold ownerAtStart; exact SquareRoot.Owner.Transport.castOwnerParameter_heq _ _)
    prepared.finishOwner_heq_terminalOwner.symm

open Purelib.Riemann.Paths in
/-- The complete segment owner path retains the exact original subdivision trace-vertex list. -/
theorem ownerPath_vertices (prepared : CompleteSegment segment within owner)
    (budget : PreparedTraceBudget segment zeroEndpoint oneEndpoint)
    (fits : budget.RequestsFit zeroEndpoint prepared.subdivision.requests) :
    (ownerPath prepared budget fits).vertices =
      PreparedSubdivisionTrace.PreparedTraceBudget.traceVertices
        segment zeroEndpoint prepared.subdivision.requests := by
  rw [ownerPath, OwnerPath.castEndpoints_vertices,
    PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath_vertices]

open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- The retained complete segment trace has the same raw winding as its exact original moving endpoint list. -/
theorem ownerPath_chainRaw (prepared : CompleteSegment segment within owner)
    (budget : PreparedTraceBudget segment zeroEndpoint oneEndpoint)
    (fits : budget.RequestsFit zeroEndpoint prepared.subdivision.requests) :
    Winding.Polygon.Basic.chainRaw polynomial start (ownerPath prepared budget fits).vertices =
      Winding.Polygon.Basic.chainRaw polynomial start (CompleteSegment.movingVertices prepared) := by
  rw [ownerPath_vertices prepared budget fits]
  have equality := PreparedSubdivisionTrace.PreparedTraceBudget.traceVertices_chainRaw
    segment zeroEndpoint prepared.subdivision.requests
  rw [prepared.start_eq] at equality
  exact equality

open Purelib.Geometry.Rational in
open Purelib.Riemann.Paths in
/-- The original complete segment's moving endpoint list terminates at its exact finish point. -/
theorem movingVertices_terminal (prepared : CompleteSegment segment within owner)
    (budget : PreparedTraceBudget segment zeroEndpoint oneEndpoint)
    (fits : budget.RequestsFit zeroEndpoint prepared.subdivision.requests) :
    Polygon.Chain.terminal start (CompleteSegment.movingVertices prepared) = finish := by
  have equality := PreparedSubdivisionTrace.PreparedTraceBudget.traceVertices_terminal
    segment zeroEndpoint prepared.subdivision.requests
  rw [prepared.start_eq, ← ownerPath_vertices prepared budget fits] at equality
  exact equality.symm.trans (ownerPath prepared budget fits).vertices_terminal

end CompleteSegment

open Purelib.Polynomial in
set_option genInjectivity false in
/-- A retained complete prepared segment with its trace budget, exact terminal-owner cache and deferred owner path.

The original request-fit certificate and moving-vertex equation preserve the executable subdivision. The deferred trace
retains an exact raw winding equality with those original moving vertices. -/
structure TracedSegment {polynomial : GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box}
    {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (owner : Owner (polynomial.eval start)) where
  /-- The retained trace budget for the exact original segment and unit endpoint interval. -/ budget :
    PreparedTraceBudget segment zeroEndpoint oneEndpoint
  /-- The original prepared segment or path retained by this trace certificate. -/ prepared : CompleteSegment segment
    within owner
  /-- The exact original subdivision request list satisfies its retained trace budget. -/ fits : budget.RequestsFit
    zeroEndpoint prepared.subdivision.requests
  /-- The retained original finish-owner cache at the exact endpoint parameter. -/ finishOwner : Owner (polynomial.eval
    finish)
  /-- The cached finish owner equals the original stored preparation's finish owner exactly. -/ finishOwner_eq :
    finishOwner = prepared.finishOwner
  /-- The retained ordered original moving endpoint cache. -/ movingVertices : List Gaussian
  /-- The moving cache equals the original request-derived moving vertices exactly. -/ movingVertices_eq :
    movingVertices = (CompleteSegment.movingVertices prepared)
  /-- The deferred original owner path, indexed by the exact retained endpoint owners. -/ trace : Thunk (OwnerPath
    polynomial start owner finish finishOwner)
  /-- The deferred trace and original retained moving vertices have equal raw polynomial winding. -/ winding_eq :
    Winding.Polygon.Basic.chainRaw polynomial start trace.get.vertices =
    Winding.Polygon.Basic.chainRaw polynomial start (CompleteSegment.movingVertices prepared)

constructive_injectivity TracedSegment

namespace TracedSegment

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Retain a traced segment from the original prepared subdivision, exact request cache and exact terminal-owner cache.

The moving vertices consume the supplied cached requests, and the owner trace is deferred while retaining the original
winding comparison and owner equality. -/
@[expose] def ofPrepared {polynomial : GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box} {start finish :
  Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)} (budget : PreparedTraceBudget segment zeroEndpoint oneEndpoint)
    (prepared : CompleteSegment segment within owner)
    (fits : budget.RequestsFit zeroEndpoint prepared.subdivision.requests)
    (requests : List PreparedSheetContinuation.StepRequest)
    (requests_eq : requests = prepared.subdivision.requests)
    (finishOwner : Owner (polynomial.eval finish)) (finishOwner_eq : finishOwner = prepared.finishOwner) :
    TracedSegment segment within owner :=
  { budget := budget
    prepared := prepared
    fits := fits
    finishOwner := finishOwner
    finishOwner_eq := finishOwner_eq
    movingVertices := requests.map fun request => segment.pointAt request.endpoint.parameter
    movingVertices_eq := by rw [requests_eq]; rfl
    trace := ⟨fun _ => (CompleteSegment.ownerPath prepared budget fits).reindexOwners rfl finishOwner_eq.symm⟩
    winding_eq := by
      change Winding.Polygon.Basic.chainRaw polynomial start
        ((CompleteSegment.ownerPath prepared budget fits).reindexOwners rfl finishOwner_eq.symm).vertices = _
      rw [OwnerPath.reindexOwners_vertices]
      exact CompleteSegment.ownerPath_chainRaw prepared budget fits }

open Purelib.Approximation.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation in
/-- Acquire a traced prepared segment using its original budget, movement depth and certified fallback depth.

The selected dyadic result retains its exact request list and terminal owner, and the two possible chosen depths each
establish the original request-fit certificate. -/
@[expose] def build {polynomial : GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box} {start finish :
  Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start)) : TracedSegment segment within owner :=
  let budget := PreparedTraceBudget.build segment zeroEndpoint oneEndpoint
  let depth := Geometric.Search.firstQuarterBelow budget.variation 0 budget.movementBudget
  let acquired := SquareRoot.Preparation.Terminal.AcquiredDyadic.acquire segment within owner budget.rootDiameter
    budget.rootDiameter_positive
    depth budget.depth (budget.meshSafe (ownerAtStart segment owner) (by decide))
  have fits : budget.RequestsFit zeroEndpoint acquired.val.prepared.subdivision.requests := by
    rw [PreparedSheetContinuation.Subdivision.tryDyadic_requests segment within
      zeroEndpoint oneEndpoint (ownerAtStart segment owner) acquired.val.depth budget.rootDiameter
      budget.rootDiameter_positive acquired.val.success]
    rcases acquired.property with selected | selected
    · rw [selected]
      apply budget.dyadicRequests_fit_of_variation (by decide) depth budget.rootDiameter
        budget.rootDiameter_positive le_rfl
      exact (Geometric.Search.firstQuarterBelow_accurate budget.variation (by
        rw [budget.variation_eq]
        exact ClearSheetContinuation.variationBound_nonneg segment _ _) 0 _
        budget.movementBudget_positive).le
    · rw [selected]
      exact budget.dyadicRequests_fit (by decide)
  ofPrepared budget acquired.val.prepared fits acquired.val.requests acquired.val.requests_eq
    acquired.val.finishOwner acquired.val.finishOwner_eq

end TracedSegment

namespace PreparedPath

section
open Purelib.Polynomial
/-- Concatenate the exact original request endpoint vertices across the retained prepared path in segment order. -/
@[expose] def movingVertices {polynomial : GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box} :
    {start finish : Gaussian} → {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} →
      {owner : Owner (polynomial.eval start)} → PreparedPath path owner → List Gaussian
  | _, _, _, _, .nil _ _ => []
  | _, _, _, _, .cons _ _ _ _ head tail => CompleteSegment.movingVertices head ++ movingVertices tail

/-- Transport an original prepared path along exact equality of its starting owner. -/
@[expose] def castOwner {polynomial : GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box} {start finish :
  Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} {first second : Owner (polynomial.eval
      start)}
    (equal : first = second) (prepared : PreparedPath path first) : PreparedPath path second := by
  cases equal
  exact prepared

end

open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- Transporting equal original starting owners preserves the retained prepared path's exact finish owner. -/
theorem castOwner_finishOwner {polynomial : GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box} {start finish
  : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} {first second : Owner (polynomial.eval
      start)}
    (equal : first = second) (prepared : PreparedPath path first) :
    PreparedPathGluing.finishOwner (castOwner equal prepared) = PreparedPathGluing.finishOwner prepared := by
  cases equal
  rfl

open Purelib.Polynomial in
/-- Transporting equal original starting owners preserves the exact moving vertex list. -/
theorem castOwner_movingVertices {polynomial : GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box} {start
  finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} {first second : Owner (polynomial.eval
      start)}
    (equal : first = second) (prepared : PreparedPath path first) :
    movingVertices (castOwner equal prepared) = movingVertices prepared := by
  cases equal
  rfl

open Purelib.Polynomial in
set_option genInjectivity false in
/-- Retained segment budgets and request-fit certificates for the exact original prepared path construction.

Each nonempty step keeps its original finish-owner equality and tail lineage, including the exact owner transport used
to join the stored path. -/
inductive TraceLineage {polynomial : GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box} :
    {start finish : Gaussian} → {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} →
      {owner : Owner (polynomial.eval start)} → PreparedPath path owner → Type
  /-- The empty lineage retains the exact original point and owner. -/ | nil (point : Gaussian) (owner : Owner
    (polynomial.eval point)) : TraceLineage (.nil point owner)
  /-- Retain the original segment budget, request-fit certificate, finish-owner equality and exact tail lineage. -/ |
    cons {start middle finish : Gaussian} {head : Geometry.ClearPath.ClearSegment polynomial ambient start middle}
      {tail : Polynomial.Geometry.ClearPath polynomial ambient middle finish} {owner : Owner (polynomial.eval start)}
      {within : head.WithinAmbient} {first : CompleteSegment head within owner}
      {finishOwner : Owner (polynomial.eval middle)} {rest : PreparedPath tail finishOwner}
      (budget : PreparedTraceBudget head zeroEndpoint oneEndpoint)
      (fits : budget.RequestsFit zeroEndpoint first.subdivision.requests)
      (finishOwner_eq : finishOwner = first.finishOwner)
      (remaining : TraceLineage rest) :
        TraceLineage (.cons head tail owner within first (PreparedPath.castOwner finishOwner_eq rest))

constructive_injectivity TraceLineage

end PreparedPath

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
set_option genInjectivity false in
/-- An original prepared path with retained trace lineage, terminal-owner and moving-vertex caches, and a deferred owner
trace.

The exact original endpoint owners and ordered path remain indices. Winding equality and terminal geometry relate the
deferred trace to the same retained moving vertices. -/
structure TracedPath {polynomial : GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box}
    {start finish : Gaussian} (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (owner : Owner (polynomial.eval start)) where
  /-- The original prepared segment or path retained by this trace certificate. -/ prepared : PreparedPath path owner
  /-- The retained original segment budgets and owner transports belonging to the exact stored prepared path. -/ lineage
    : PreparedPath.TraceLineage prepared
  /-- The retained original finish-owner cache at the exact endpoint parameter. -/ finishOwner : Owner (polynomial.eval
    finish)
  /-- The cached finish owner equals the original stored preparation's finish owner exactly. -/ finishOwner_eq :
    finishOwner = PreparedPathGluing.finishOwner prepared
  /-- The retained ordered original moving endpoint cache. -/ movingVertices : List Gaussian
  /-- The moving cache equals the original request-derived moving vertices exactly. -/ movingVertices_eq :
    movingVertices = (PreparedPath.movingVertices prepared)
  /-- The deferred original owner path, indexed by the exact retained endpoint owners. -/ trace : Thunk (OwnerPath
    polynomial start owner finish finishOwner)
  /-- The deferred trace and original retained moving vertices have equal raw polynomial winding. -/ winding_eq :
    Winding.Polygon.Basic.chainRaw polynomial start trace.get.vertices =
    Winding.Polygon.Basic.chainRaw polynomial start (PreparedPath.movingVertices prepared)
  /-- The original retained moving vertex list terminates at the exact path finish point. -/ moving_terminal :
    Polygon.Chain.terminal start (PreparedPath.movingVertices prepared) = finish

constructive_injectivity TracedPath

namespace TracedPath

open Purelib.Polynomial in
/-- For a returning original traced path, its closed trace winding equals the raw winding of the exact retained moving
vertices.

The retained endpoint owner certifies the stationary closing segment. The
original trace winding equation then identifies the exact cached moving list. -/
theorem closedRaw_eq_moving {polynomial : GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box} {base :
  Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient base base} {owner : Owner (polynomial.eval base)}
    (traced : TracedPath path owner) :
    Winding.Polygon.Basic.closedRaw polynomial base traced.trace.get.vertices =
      Winding.Polygon.Basic.chainRaw polynomial base (PreparedPath.movingVertices traced.prepared) := by
  rw [Winding.Polygon.Basic.closedRaw, Winding.Polygon.Basic.chainRaw_append,
    traced.trace.get.vertices_terminal, Winding.Polygon.Basic.chainRaw,
    Winding.Polygon.Stationary.segment_self_doubledWinding polynomial base owner.parameterNonzero,
    Winding.Polygon.Basic.chainRaw, Int.Arithmetic.zero_add, Int.add_zero, traced.winding_eq]

open Purelib.Approximation.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- Odd winding of the original retained moving path excludes equivalence of its final and initial root names.

The deferred owner trace has the same exact winding, and a putative return comparison would produce a closed square-root
trace with even winding. -/
theorem root_not_equivalent_of_odd {polynomial : GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box} {base :
  Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient base base} {owner : Owner (polynomial.eval base)}
    (traced : TracedPath path owner) (turns : Int)
    (odd : Winding.Polygon.Basic.chainRaw polynomial base (PreparedPath.movingVertices traced.prepared) = 4 * (2 * turns
      + 1)) :
    Equivalence.NamedEquivalent
      (OwnerTraceReadings.ownerName traced.finishOwner)
      (OwnerTraceReadings.ownerName owner) → False := by
  intro equivalent
  exact traced.trace.get.not_odd_of_return equivalent turns (traced.closedRaw_eq_moving.trans odd)

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- Prepend the original traced segment to a retained traced tail at its exact cached finish owner.

The constructor reuses both prepared paths and moving caches, retains the owner transport in its lineage, and defers
concatenation of the original owner traces with exact winding and terminal certificates. -/
@[expose] def cons {polynomial : GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box} {start middle finish :
  Gaussian}
    {head : Geometry.ClearPath.ClearSegment polynomial ambient start middle} {tail : Polynomial.Geometry.ClearPath
      polynomial ambient middle finish}
    {within : head.WithinAmbient} {owner : Owner (polynomial.eval start)}
    (first : TracedSegment head within owner) (rest : TracedPath tail first.finishOwner) :
    TracedPath (.cons head tail) owner :=
      { prepared := .cons head tail owner within first.prepared (PreparedPath.castOwner first.finishOwner_eq
        rest.prepared)
        lineage := .cons first.budget first.fits first.finishOwner_eq rest.lineage
        finishOwner := rest.finishOwner
        finishOwner_eq := rest.finishOwner_eq.trans (PreparedPath.castOwner_finishOwner first.finishOwner_eq
          rest.prepared).symm
        movingVertices := first.movingVertices ++ rest.movingVertices
        movingVertices_eq := by
          change _ = (CompleteSegment.movingVertices first.prepared) ++ (PreparedPath.movingVertices
            (PreparedPath.castOwner first.finishOwner_eq rest.prepared))
          rw [PreparedPath.castOwner_movingVertices, first.movingVertices_eq, rest.movingVertices_eq]
        trace := ⟨fun _ => first.trace.get.append rest.trace.get⟩
        winding_eq := by
          change Winding.Polygon.Basic.chainRaw polynomial _ (first.trace.get.append rest.trace.get).vertices =
            Winding.Polygon.Basic.chainRaw polynomial _
              ((CompleteSegment.movingVertices first.prepared) ++ (PreparedPath.movingVertices (PreparedPath.castOwner
                first.finishOwner_eq rest.prepared)))
          rw [PreparedPath.castOwner_movingVertices, OwnerPath.append_vertices, Winding.Polygon.Basic.chainRaw_append,
            first.trace.get.vertices_terminal, first.winding_eq, rest.winding_eq]
          rw [Winding.Polygon.Basic.chainRaw_append,
            CompleteSegment.movingVertices_terminal first.prepared first.budget first.fits]
        moving_terminal := by
          change Polygon.Chain.terminal _
            ((CompleteSegment.movingVertices first.prepared) ++ (PreparedPath.movingVertices (PreparedPath.castOwner
              first.finishOwner_eq rest.prepared))) = _
          rw [PreparedPath.castOwner_movingVertices, Polygon.Chain.terminal_append,
            CompleteSegment.movingVertices_terminal first.prepared first.budget first.fits, rest.moving_terminal] }

open Purelib.Polynomial in
/-- Construct a retained traced path recursively along the exact original cleared segments.

The empty path keeps its original owner and empty caches. Each segment passes its cached finish owner into the original
tail construction and retains the deferred trace through concatenation. -/
@[expose] def build {polynomial : GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box} :
    {start finish : Gaussian} → (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) →
      path.WithinAmbient → (owner : Owner (polynomial.eval start)) → TracedPath path owner
  | _, _, .nil point, _within, owner =>
      { prepared := .nil point owner
        lineage := .nil point owner
        finishOwner := owner
        finishOwner_eq := rfl
        movingVertices := []
        movingVertices_eq := rfl
        trace := ⟨fun _ => .nil point owner⟩
        winding_eq := rfl
        moving_terminal := rfl }
  | _, _, .cons head tail, within, owner =>
      let first := TracedSegment.build head within.head owner
      cons first (build tail within.tail first.finishOwner)

end TracedPath

end

end Purelib.Riemann.Paths.PreparedPathTrace
