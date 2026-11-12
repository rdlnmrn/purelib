module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Geometry
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.PrimitiveCover.Acquisition.Chain
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Entries
import Purelib.Data.List.Append
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore

/-! # The SAME refined geometric chain across an original materialized subdivision

Each actual request reads its already acquired children and direct chain.
Concatenation follows the original request spine and literal endpoint
indices. Empty inner words retain their original outer geometry entries;
no query, source, root trace or primitive observation is executed.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Cache.Geometry

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain allParentsProper_append)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates CenteredEdge)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.PreparedClearPathModels.PreparedPath (StrictParameterEdges)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count : Nat} {sheet : Fin 2}
variable {ambient : Purelib.Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {left right : PreparedSheetContinuation.Endpoint}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

/-- Flatten the SAME acquired children in original request order, retaining every repeated or stationary child. -/
@[expose] def parents (diameter : Rational) (positive : 0 < diameter)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    Geometry (count := count) diameter positive budget subdivision centers fits trace →
      List (CenteredEdge (Fibre.frameCurve frame) basis)
  | _, _, .stop _ _, _, _, _, _ => []
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, geometry =>
      geometry.1.val.acquisition.parents ++
        parents diameter positive budget remaining centers.2 fits.2.2 geometry.1.val.nextTrace geometry.2
termination_by structural _ _ subdivision _ _ _ _ => subdivision

/-- Every retained child interval is strict in the actual flattened request order.

The original acquisition supplies each block's certificate. Concatenation
preserves the same child lists; no old parent strictness, physical movement
or new acquisition is assumed.
-/
theorem parents_proper (diameter : Rational) (positive : 0 < diameter)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (geometry : Geometry (count := count) diameter positive budget subdivision centers fits trace) →
      AllParentsProper (parents diameter positive budget subdivision centers fits trace geometry)
  | _, _, .stop _ _, _, _, _, _ => True.intro
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, geometry =>
      allParentsProper_append geometry.1.val.acquisition.parents_proper
        (parents_proper diameter positive budget remaining centers.2 fits.2.2 geometry.1.val.nextTrace geometry.2)
termination_by structural _ _ subdivision _ _ _ _ => subdivision

/-- The actual flattened child list has exactly the pre-observation count from the SAME geometry bank. -/
theorem parents_length (diameter : Rational) (positive : 0 < diameter)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (geometry : Geometry (count := count) diameter positive budget subdivision centers fits trace) →
      (parents diameter positive budget subdivision centers fits trace geometry).length =
        childCount diameter positive budget subdivision centers fits trace geometry
  | _, _, .stop _ _, _, _, _, _ => rfl
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, geometry =>
      (Data.List.Append.length_append geometry.1.val.acquisition.parents
        (parents diameter positive budget remaining centers.2 fits.2.2 geometry.1.val.nextTrace geometry.2)).trans
          (congrArg₂ Nat.add geometry.1.val.acquisition.parents_length
            (parents_length diameter positive budget remaining centers.2 fits.2.2 geometry.1.val.nextTrace geometry.2))
termination_by structural _ _ subdivision _ _ _ _ => subdivision

/-- Strict original requests contribute at least their own count to the SAME actual refined child word.

Only the given strict parameter edges and each retained acquired branch
are inspected. Physically stationary or repeated edges still count; no
root, geometry, mesh, query or source producer executes in this proof.
-/
theorem stepCount_le_childCount (diameter : Rational) (positive : 0 < diameter)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (geometry : Geometry (count := count) diameter positive budget subdivision centers fits trace) →
    StrictParameterEdges subdivision.parameterEdges →
      subdivision.stepCount ≤ childCount diameter positive budget subdivision centers fits trace geometry
  | _, _, .stop _ _, _, _, _, _, _ => Nat.le_refl 0
  | _, _, .next current _owner request _cached _ordered _small remaining,
      centers, fits, _trace, geometry, proper => by
      change (current.parameter < request.endpoint.parameter ∧
        StrictParameterEdges remaining.parameterEdges) at proper
      have firstCount : 1 ≤ geometry.1.val.childCount :=
        Nat.succ_le_of_lt (geometry.1.val.acquisition.childCount_positive proper.1)
      have followingCount := stepCount_le_childCount diameter positive budget remaining centers.2 fits.2.2
        geometry.1.val.nextTrace geometry.2 proper.2
      have total := Nat.add_le_add firstCount followingCount
      exact Eq.mp (congrArg (fun size : Nat => size ≤ geometry.1.val.childCount +
        childCount diameter positive budget remaining centers.2 fits.2.2 geometry.1.val.nextTrace geometry.2)
          (Nat.add_comm 1 remaining.stepCount)) total
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

/-- Join the SAME successful child covering spines without inspecting or preparing another patch. -/
@[expose] def covered (diameter : Rational) (positive : 0 < diameter)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (geometry : Geometry (count := count) diameter positive budget subdivision centers fits trace) →
      CoveredParents count (parents diameter positive budget subdivision centers fits trace geometry)
  | _, _, .stop _ _, _, _, _, _ => .nil
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, geometry =>
      geometry.1.val.acquisition.covered.append
        (covered diameter positive budget remaining centers.2 fits.2.2 geometry.1.val.nextTrace geometry.2)
termination_by structural _ _ subdivision _ _ _ _ => subdivision

/-- Join actual acquired child chains at the original ordered request endpoints on the retained sheet.

The original parent of each acquisition is the SAME edgeOfStep with its
actual source and requested target. Those coordinate and sheet indices
identify the geometric seam only. Every original View/query/root-chain
certificate remains separately retained in the supplied geometry bank.
-/
def chain (diameter : Rational) (positive : 0 < diameter)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (geometry : Geometry (count := count) diameter positive budget subdivision centers fits trace) →
      CenteredPathChain (parents diameter positive budget subdivision centers fits trace geometry)
        (start := ⟨segment.pointAt current.parameter, sheet⟩)
        (finish := ⟨segment.pointAt subdivision.endpoint.parameter, sheet⟩)
  | _, _, .stop current _owner, _, _, _, _ => .nil ⟨segment.pointAt current.parameter, sheet⟩
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, geometry =>
      geometry.1.val.acquisition.chain.append
        (chain diameter positive budget remaining centers.2 fits.2.2 geometry.1.val.nextTrace geometry.2)
termination_by structural _ _ subdivision _ _ _ _ => subdivision

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Cache.Geometry

end
