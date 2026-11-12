module

public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Alignment
public import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Interior queries at original retained subdivision occurrences

The exact original centered-child occurrence selects its own cached RootPath,
shared reference and already derived Alignment entry. Recursion reads the SAME
materialized comparison/center tails; no path, reference, source preparation,
advancement or query is constructed by this lookup comparison.
-/

public section

namespace Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Comparison.Cache.Alignment

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision Endpoint)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates centeredEdges)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

attribute [local irreducible] CertifiedSquareRoot.rawRoot

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
    {first last : Endpoint} {budget : PreparedTraceBudget segment first last} {sheet : Fin 2}
    {referenceSource : Canonical} {referenceOwner : Owner referenceSource}
    {second : FixedRootBoxBudget.Budget referenceOwner}
    {movement : ∀ time : Rational, Inside time →
      Norm.Basic.normSq (referenceSource - curve.polynomial.eval (segment.pointAt time)) ≤ second.movement}

/-- The exact interior query-comparison operation on one retained centered-child occurrence.

This function type keeps the actual child, query, independent point Owner
and original reference-box refinement as indices. Naming it leaves the
recursive subdivision motive compact without copying or replacing an Owner.
-/
@[expose] def QueryComparison {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    (centers : CenterStates curve differential sheet subdivision)
    (index : Fin (centeredEdges curve differential sheet subdivision centers).length) : Type :=
  (time : Rational) → (inside : Inside time) →
    Integration.PreparedConstantModels.PreparedEdge.Query
      ((centeredEdges curve differential sheet subdivision centers)[index.val]'index.isLt).edge time inside →
    (atTime : Owner (curve.polynomial.eval
      (((centeredEdges curve differential sheet subdivision centers)[index.val]'index.isLt).edge.point time))) →
    atTime.track.initial.box.Refines referenceOwner.track.initial.box →
    NamedEquivalent
      (((centeredEdges curve differential sheet subdivision centers)[index.val]'index.isLt).edge.rootName time inside)
      (ownerRootName atTime.parameterNonzero atTime)

/-- Derive the actual interior query comparison at any original bounded centered-child occurrence.

The selected direct-query cache and independent same-point Owner are
retained inputs. Lookup consumes the stored Alignment head or identical
tail, with its actual shared reference and refinement. No desired query
agreement or fresh source/advance/reference factory is supplied or run.
-/
def queryAtEquivalent {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace)
    (reference : Owner (curve.polynomial.eval (segment.pointAt current.parameter)))
    (aligned : Alignment retained reference)
    (refines : reference.track.initial.box.Refines referenceOwner.track.initial.box)
    (centers : CenterStates curve differential sheet subdivision)
    (index : Fin (centeredEdges curve differential sheet subdivision centers).length) :
    QueryComparison (referenceOwner := referenceOwner) centers index :=
  Subdivision.casesOn
    (motive := fun current _ subdivision =>
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : Trace budget subdivision fits) →
      (retained : Cache curve differential budget sheet second movement subdivision fits trace) →
      (reference : Owner (curve.polynomial.eval (segment.pointAt current.parameter))) →
      Alignment retained reference →
      reference.track.initial.box.Refines referenceOwner.track.initial.box →
      (centers : CenterStates curve differential sheet subdivision) →
      (index : Fin (centeredEdges curve differential sheet subdivision centers).length) →
      QueryComparison (referenceOwner := referenceOwner) centers index)
    subdivision
    (fun _ _ _ _ _ _ _ _ _ index => Fin.elim0 index)
    (fun current inherited request cached ordered small remaining fits trace retained reference aligned refines
        centers index =>
      Fin.cases
        (motive := fun index => QueryComparison (referenceOwner := referenceOwner) centers index)
        (fun time inside query atTime atTimeRefines =>
          queryEquivalent (curve := curve) (differential := differential) (budget := budget) (sheet := sheet)
            (second := second) (movement := movement) (current := current) (inherited := inherited)
            (request := request) (cached := cached) (ordered := ordered) (small := small) (remaining := remaining)
            (fits := fits) (trace := trace) (retained := retained) (reference := reference)
            (time := time) (inside := inside) aligned refines query atTime atTimeRefines)
        (fun index => queryAtEquivalent retained.2.2.2 retained.2.2.1.val aligned.2 retained.2.2.1.refines centers.2
          index) index)
    fits trace retained reference aligned refines centers index
termination_by structural subdivision

variable {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace)
    (reference : Owner (curve.polynomial.eval (segment.pointAt current.parameter)))
    (aligned : Alignment retained reference)
    (refines : reference.track.initial.box.Refines referenceOwner.track.initial.box)
    (centers : CenterStates curve differential sheet subdivision)
    (index : Fin (centeredEdges curve differential sheet subdivision centers).length)
    {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}

/-- Compare a retained global query on an exactly identified original local child, preserving its whole parent Owner.

The parent equality is the original occurrence readback, not a signed root
hypothesis. Equality elimination changes only the parent/point indices of
the supplied complete query and same-point Owner, then selects the SAME
local cached path and alignment by its retained bounded child occurrence.
-/
def queryParentEquivalent (parent_eq : parent =
      (centeredEdges curve differential sheet subdivision centers)[index.val]'index.isLt)
    (time : Rational) (inside : Inside time)
    (query : Integration.PreparedConstantModels.PreparedEdge.Query parent.edge time inside)
    (atTime : Owner (curve.polynomial.eval (parent.edge.point time)))
    (atTimeRefines : atTime.track.initial.box.Refines referenceOwner.track.initial.box) :
    NamedEquivalent (parent.edge.rootName time inside) (ownerRootName atTime.parameterNonzero atTime) := by
  cases parent_eq
  exact queryAtEquivalent retained reference aligned refines centers index time inside query atTime atTimeRefines

/-- Compare a retained query with an original Owner at a provably identical physical point.

Only the exact point/radicand index is transported. The complete original
Owner, its initial-box refinement and its root name are retained through
existing transport laws. This operation performs no query or continuation
factory and supplies no comparison between different physical points.
-/
def queryPointEquivalent (parent_eq : parent =
      (centeredEdges curve differential sheet subdivision centers)[index.val]'index.isLt)
    (time : Rational) (inside : Inside time)
    (query : Integration.PreparedConstantModels.PreparedEdge.Query parent.edge time inside)
    {point : Canonical} (point_eq : point = parent.edge.point time)
    (atPoint : Owner (curve.polynomial.eval point))
    (atPointRefines : atPoint.track.initial.box.Refines referenceOwner.track.initial.box) :
    NamedEquivalent (parent.edge.rootName time inside) (ownerRootName atPoint.parameterNonzero atPoint) := by
  let transport : ∀ {source target : Canonical}, source = target →
      (owner : Owner source) → owner.track.initial.box.Refines referenceOwner.track.initial.box →
      ((next : Owner target) → next.track.initial.box.Refines referenceOwner.track.initial.box →
        NamedEquivalent (parent.edge.rootName time inside) (ownerRootName next.parameterNonzero next)) →
      NamedEquivalent (parent.edge.rootName time inside) (ownerRootName owner.parameterNonzero owner) := by
    intro source target equal owner paid compare
    cases equal
    exact compare owner paid
  exact transport (congrArg curve.polynomial.eval point_eq) atPoint atPointRefines
    (fun atTime paid => queryParentEquivalent retained reference aligned refines centers index parent_eq
      time inside query atTime paid)

end Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Comparison.Cache.Alignment

end
