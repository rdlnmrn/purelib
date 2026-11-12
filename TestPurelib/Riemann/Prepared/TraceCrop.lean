module

import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Crop

/-! # Whole-result regression for the shared retained-View lookup

The private reference is the exact frozen original endpointsAt recursion,
with only its local name changed. The private all-input theorem compares
its complete product, preserving functional witnesses and actual Owners.
This regression is separate from the production traversal.
-/

namespace PreparedTraceCropAgreement

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision Endpoint StepRequest CachedSource)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore
  (CenteredEdge CenterStates centeredEdges centeredEdges_length edgeOfStep)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName_castOwnerParameter)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter castOwnerParameter_heq)

open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Trace

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
variable {first last : Endpoint} {budget : PreparedTraceBudget segment first last} {sheet : Fin 2}

/-- The complete old structural lookup, retained only for all-input result regression. -/
private def legacyEndpointsAt {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests}
    (trace : Trace budget subdivision fits)
    (centers : CenterStates curve differential sheet subdivision) :
    (index : Fin (centeredEdges curve differential sheet subdivision centers).length) →
    EndpointComparisons ((centeredEdges curve differential sheet subdivision centers)[index.val]'index.isLt) :=
  Subdivision.casesOn
    (motive := fun current _ subdivision =>
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : Trace budget subdivision fits) →
      (centers : CenterStates curve differential sheet subdivision) →
      (index : Fin (centeredEdges curve differential sheet subdivision centers).length) →
      EndpointComparisons ((centeredEdges curve differential sheet subdivision centers)[index.val]'index.isLt))
    subdivision
    (fun _ _ _ _ _ index => Fin.elim0 index)
    (fun current inherited request cached ordered small remaining _fits trace centers index =>
      let view := View.build trace
      Fin.cases
        (motive := fun index => EndpointComparisons
          ((centeredEdges curve differential sheet
            (Subdivision.next current inherited request cached ordered small remaining) centers)[index.val]'index.isLt))
        (view.endpointComparisons centers.1)
        (fun next => legacyEndpointsAt view.tailTrace centers.2 next) index)
    fits trace centers
termination_by structural subdivision

section Accepted

variable {current : Endpoint}
variable {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
variable {request : StepRequest} {cached : CachedSource segment current inherited request}
variable {ordered : current.parameter ≤ request.endpoint.parameter}
variable {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound}
variable {remaining : Subdivision segment within request.endpoint
  (PreparedSheetContinuation.advance segment within current inherited request small)}
variable {fits : budget.RequestsFit current
  (Subdivision.next current inherited request cached ordered small remaining).requests}
variable (trace : Trace budget (Subdivision.next current inherited request cached ordered small remaining) fits)
variable (centers : CenterStates curve differential sheet
  (Subdivision.next current inherited request cached ordered small remaining))

/-- The frozen reference returns the complete original head comparison product. -/
private theorem legacyEndpointsAt_head : legacyEndpointsAt trace centers ⟨0, Nat.zero_lt_succ _⟩ =
    (View.build trace).endpointComparisons centers.1 := by
  unfold legacyEndpointsAt
  rfl

/-- The frozen reference recurses on the literal original tail and center family. -/
private theorem legacyEndpointsAt_succ
    (index : Fin (centeredEdges curve differential sheet remaining centers.2).length) :
    legacyEndpointsAt trace centers index.succ = legacyEndpointsAt (View.build trace).tailTrace centers.2 index := by
  conv_lhs => unfold legacyEndpointsAt
  rfl

end Accepted

/-- The shared original traversal preserves the full old result for every actual Trace, centers and occurrence.

definitional branch comparison retains the complete source/moving/reset
functions and their actual dependent Owner witnesses. The literal-tail
induction does not use function extensionality or coordinate selection.
-/
theorem endpointsAt_agrees {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests}
    (trace : Trace budget subdivision fits)
    (centers : CenterStates curve differential sheet subdivision)
    (index : Fin (centeredEdges curve differential sheet subdivision centers).length) :
    endpointsAt trace centers index = legacyEndpointsAt trace centers index :=
  Subdivision.rec
    (motive := fun current _ subdivision =>
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : Trace budget subdivision fits) →
      (centers : CenterStates curve differential sheet subdivision) →
      (index : Fin (centeredEdges curve differential sheet subdivision centers).length) →
      endpointsAt trace centers index = legacyEndpointsAt trace centers index)
    (fun current inherited _fits _trace centers index => by
      have count := (centeredEdges_length curve differential sheet
        (Subdivision.stop (segment := segment) (within := within) current inherited) centers).trans
          (Subdivision.stepCount_stop current inherited)
      exact Fin.elim0 (Fin.cast count index))
    (fun current inherited request cached ordered small remaining ih fits trace centers index => by
      change PreparedEdge.CenterState
          (edgeOfStep curve differential segment within current inherited request cached ordered small sheet) ×
        CenterStates curve differential sheet remaining at centers
      exact Fin.cases (n := (centeredEdges curve differential sheet remaining centers.2).length)
        (motive := fun index => endpointsAt trace centers index = legacyEndpointsAt trace centers index)
        (by
          exact (endpointsAt_head trace centers).trans (legacyEndpointsAt_head trace centers).symm)
        (fun next => by
          have first := endpointsAt_succ trace centers next
          have middle := ih fits.2.2 (View.build trace).tailTrace centers.2 next
          exact first.trans (middle.trans (legacyEndpointsAt_succ trace centers next).symm)) index)
    subdivision fits trace centers index

end PreparedTraceCropAgreement
