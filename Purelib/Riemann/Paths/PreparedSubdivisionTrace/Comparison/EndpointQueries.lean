module

public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Comparison
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.QuerySource.Endpoints
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Original endpoint query comparisons at retained subdivision occurrences

Every finite child index descends through the original comparison cache's
stored View and identical tailTrace. Results keep the actual selected
query and literal source, moving or retention Owner; target Owner casts
change only exact physical indices. No observer or trace is replayed.
-/

public section

namespace Purelib.Riemann.Paths.PreparedSubdivisionTrace

namespace PreparedTraceBudget.Comparison.Cache

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision Endpoint StepRequest CachedSource)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge CenterStates centeredEdges edgeOfStep)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter castOwnerParameter_heq)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName_castOwnerParameter)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
    {first last : Endpoint} {budget : PreparedTraceBudget segment first last} {sheet : Fin 2}
    {referenceSource : Canonical} {referenceOwner : Owner referenceSource}
    {second : FixedRootBoxBudget.Budget referenceOwner}
    {movement : ∀ time : Rational, Inside time →
      Norm.Basic.normSq (referenceSource - curve.polynomial.eval (segment.pointAt time)) ≤ second.movement}

/-- The original zero-query comparison to its actual inherited prepared-edge Owner. -/
@[expose] def SourceComparison (parent : CenteredEdge curve differential) : Type :=
  PreparedEdge.Query parent.edge 0 parent.edge.baseInside →
    NamedEquivalent (parent.edge.rootName 0 parent.edge.baseInside) (ownerName parent.edge.owner)

/-- One actual endpoint Owner and signed comparison on the same retained original upper query.

The Owner is at the selected original parent's endpoint. It remains the
whole actual moving or retention suffix Owner under exact parameter
transport; the comparison keeps the original query channel as its source.
-/
@[expose] def EndpointResult (parent : CenteredEdge curve differential) : Type :=
  (owner : Owner (curve.polynomial.eval (parent.edge.point 1))) ×
    NamedEquivalent (parent.edge.rootName 1 (of_decide_eq_true rfl)) (ownerName owner)

/-- The exact original upper-query input and retained endpoint comparison result. -/
@[expose] def EndpointComparison (parent : CenteredEdge curve differential) : Type :=
  PreparedEdge.Query parent.edge 1 (of_decide_eq_true rfl) → EndpointResult parent

/-- The bounded original parent-list family of source comparisons, retaining occurrence order. -/
@[expose] def SourceFamily (parents : List (CenteredEdge curve differential)) : Type :=
  (index : Fin parents.length) → SourceComparison (parents[index.val]'index.isLt)

/-- The bounded original parent-list family of upper-query comparisons with actual endpoint Owners. -/
@[expose] def EndpointFamily (parents : List (CenteredEdge curve differential)) : Type :=
  (index : Fin parents.length) → EndpointComparison (parents[index.val]'index.isLt)

/-- Dispatch a source query through the same original stored View and literal comparison-cache tails.

The index chooses an occurrence, including repeated coordinates, by finite
list position. The nil case has no query occurrence; no fabricated Owner
or source execution is inserted into an empty subdivision.
-/
def sourceAt {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace)
    (centers : CenterStates curve differential sheet subdivision) :
    SourceFamily (centeredEdges curve differential sheet subdivision centers) :=
  Subdivision.casesOn
    (motive := fun current _ subdivision =>
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : Trace budget subdivision fits) →
      Cache curve differential budget sheet second movement subdivision fits trace →
      (centers : CenterStates curve differential sheet subdivision) →
      SourceFamily (centeredEdges curve differential sheet subdivision centers))
    subdivision
    (fun _ _ _ _ _ _ index => Fin.elim0 index)
    (fun current inherited request cached ordered small remaining _fits _trace retained centers index =>
      Fin.cases
        (motive := fun index => SourceComparison
          ((centeredEdges curve differential sheet
            (Subdivision.next current inherited request cached ordered small remaining) centers)[index.val]'index.isLt))
        (fun _query => retained.1.sourceEquivalent sheet)
        (fun index => sourceAt retained.2.2.2 centers.2 index) index)
    fits trace retained centers
termination_by structural subdivision

/-- Read and compare the actual moving endpoint Owner at one literal original centered-parent occurrence.

The same View supplies its actual moving suffix. Only its proven physical
point index is cast; the root comparison is derived by original endpoint
readbacks on the supplied Query. The result stores both that whole Owner
and its original-query relation, rather than reconstructing its factory.
-/
def movingAt {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace)
    (centers : CenterStates curve differential sheet subdivision) :
    EndpointFamily (centeredEdges curve differential sheet subdivision centers) :=
  Subdivision.casesOn
    (motive := fun current _ subdivision =>
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : Trace budget subdivision fits) →
      Cache curve differential budget sheet second movement subdivision fits trace →
      (centers : CenterStates curve differential sheet subdivision) →
      EndpointFamily (centeredEdges curve differential sheet subdivision centers))
    subdivision
    (fun _ _ _ _ _ _ index => Fin.elim0 index)
    (fun current inherited request cached ordered small remaining _fits _trace retained centers index =>
      Fin.cases
        (motive := fun index => EndpointComparison
          ((centeredEdges curve differential sheet
            (Subdivision.next current inherited request cached ordered small remaining) centers)[index.val]'index.isLt))
        (fun query =>
          let view := retained.1
          let edge := edgeOfStep curve differential segment within
            current inherited request cached ordered small sheet
          let equal := congrArg curve.polynomial.eval (view.moving_point.trans edge.point_one.symm)
          let actual := castOwnerParameter equal view.moving.owner
          let compared := view.queryMovingEquivalent query
          let nameEq : ownerName actual = ownerName view.moving.owner :=
            ownerRootName_castOwnerParameter equal view.moving.owner
          ⟨actual, NamedEquivalent.transport rfl nameEq.symm compared⟩)
        (fun index => movingAt retained.2.2.2 centers.2 index) index)
    fits trace retained centers
termination_by structural subdivision

/-- Read and compare the distinct actual post-retention Owner at one literal original parent occurrence.

The actual reset link derives the additional signed relation. The same
upper Query and original tail Owner are retained separately; no reserve
retention or next source preparation is executed by this finite lookup.
-/
def retainedAt {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace)
    (centers : CenterStates curve differential sheet subdivision) :
    EndpointFamily (centeredEdges curve differential sheet subdivision centers) :=
  Subdivision.casesOn
    (motive := fun current _ subdivision =>
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : Trace budget subdivision fits) →
      Cache curve differential budget sheet second movement subdivision fits trace →
      (centers : CenterStates curve differential sheet subdivision) →
      EndpointFamily (centeredEdges curve differential sheet subdivision centers))
    subdivision
    (fun _ _ _ _ _ _ index => Fin.elim0 index)
    (fun current inherited request cached ordered small remaining _fits _trace retained centers index =>
      Fin.cases
        (motive := fun index => EndpointComparison
          ((centeredEdges curve differential sheet
            (Subdivision.next current inherited request cached ordered small remaining) centers)[index.val]'index.isLt))
        (fun query =>
          let view := retained.1
          let edge := edgeOfStep curve differential segment within
            current inherited request cached ordered small sheet
          let equal := congrArg curve.polynomial.eval (view.tail_point.trans edge.point_one.symm)
          let actual := castOwnerParameter equal view.tail.owner
          let compared := view.queryRetainedEquivalent query
          let nameEq : ownerName actual = ownerName view.tail.owner :=
            ownerRootName_castOwnerParameter equal view.tail.owner
          ⟨actual, NamedEquivalent.transport rfl nameEq.symm compared⟩)
        (fun index => retainedAt retained.2.2.2 centers.2 index) index)
    fits trace retained centers
termination_by structural subdivision

section Head

variable {current : Endpoint}
variable {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
variable {request : StepRequest}
variable {cached : CachedSource segment current inherited request}
variable {ordered : current.parameter ≤ request.endpoint.parameter}
variable {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound}
variable {remaining : Subdivision segment within request.endpoint
  (PreparedSheetContinuation.advance segment within current inherited request small)}
variable {fits : budget.RequestsFit current
  (Subdivision.next current inherited request cached ordered small remaining).requests}
variable {trace : Trace budget (Subdivision.next current inherited request cached ordered small remaining) fits}
variable (retained : Cache curve differential budget sheet second movement
  (Subdivision.next current inherited request cached ordered small remaining) fits trace)
variable (centers : CenterStates curve differential sheet
  (Subdivision.next current inherited request cached ordered small remaining))

/-- The head dispatch is the same actual View comparison, including its entire retained relation value. -/
theorem sourceAt_head
    (query : PreparedEdge.Query
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)
      0
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet).baseInside) :
    sourceAt retained centers ⟨0, Nat.zero_lt_succ _⟩ query = retained.1.sourceEquivalent sheet := by
  unfold sourceAt
  rfl

/-- The actual moving-result Owner is the whole original moving suffix under only its proven parameter cast. -/
theorem movingAt_head_owner_heq
    (query : PreparedEdge.Query
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)
      1 (of_decide_eq_true rfl)) :
    HEq (movingAt retained centers ⟨0, Nat.zero_lt_succ _⟩ query).1 retained.1.moving.owner := by
  unfold movingAt
  exact castOwnerParameter_heq _ _

/-- The actual reset-result Owner is the whole distinct original tail suffix under only its proven parameter cast. -/
theorem retainedAt_head_owner_heq
    (query : PreparedEdge.Query
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)
      1 (of_decide_eq_true rfl)) :
    HEq (retainedAt retained centers ⟨0, Nat.zero_lt_succ _⟩ query).1 retained.1.tail.owner := by
  unfold retainedAt
  exact castOwnerParameter_heq _ _

end Head

end PreparedTraceBudget.Comparison.Cache

end Purelib.Riemann.Paths.PreparedSubdivisionTrace

end
