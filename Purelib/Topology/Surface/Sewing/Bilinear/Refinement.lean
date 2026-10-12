module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search

import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.Bilinear.Errors
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Topology.Surface.Sewing.Bilinear.Requests
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveRefinement
import Purelib.Data.Gaussian.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Algebra

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.Bilinear

open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

public section

/-! A shared later stage for both differential contact banks. Existing
sample caches are consumed through pointwise readbacks; no sewing is replayed. -/

namespace Purelib.Topology.Surface.Sewing.Bilinear

open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (ContactBank SourceContact SourceEdge)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveRefinement (ContactRates)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.Bilinear.Requests (AreaRequest)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests (LocalAccuracy)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (Coordinate)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear
open Purelib.Topology.Surface.Sewing.Bilinear.Errors (traceAt)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)

open Purelib.Topology.Polygon.Stokes (OrientedTriangle PrimitivePoint triangleWedgeArea)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {patch : SewingTree.SewnPatch faces} {magnitude target : SewnPrimitiveFaces.Coordinate}
  {contacts : SewnPrimitiveContacts.ContactBank patch.assembly}
  {leftFamily rightFamily : Nat → Fin faceCount → PrimitiveSewing.PrimitiveValues 3}

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
set_option genInjectivity false in
/-- A common retained stage at which both original differential contact banks meet one area request.

The stage lies above the supplied floor and carries separate geometric error certificates for the two input families. -/
structure Refinement (request : Requests.AreaRequest patch magnitude target)
    (leftRates : SewnPrimitiveRefinement.ContactRates contacts leftFamily) (rightRates :
      SewnPrimitiveRefinement.ContactRates contacts rightFamily) (floor : Nat) where
  /-- Retained common stage for the two original contact-rate families. -/ index : Nat
  /-- The chosen stage is at least the original requested floor. -/ later : floor ≤ index
  /-- The first contact bank's geometric bound meets the retained request tolerance. -/ leftAccurate :
    Geometric.Basic.quarterRadius leftRates.total index < request.tolerance
  /-- The second contact bank's geometric bound meets the same retained request tolerance. -/ rightAccurate :
    Geometric.Basic.quarterRadius rightRates.total index < request.tolerance

-- Preserve the original constructor certificate names of this unchanged nominal datatype.

constructive_injectivity Refinement

namespace Refinement

variable {request : Requests.AreaRequest patch magnitude target}
  {leftRates : SewnPrimitiveRefinement.ContactRates contacts leftFamily} {rightRates :
    SewnPrimitiveRefinement.ContactRates contacts rightFamily} {floor : Nat}

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
/-- Search successive finite geometric stages to meet both contact tolerances above the original floor. -/
@[expose] def build (request : Requests.AreaRequest patch magnitude target)
    (leftRates : SewnPrimitiveRefinement.ContactRates contacts leftFamily) (rightRates :
      SewnPrimitiveRefinement.ContactRates contacts rightFamily) (floor : Nat) :
    Refinement request leftRates rightRates floor :=
  let first := Search.firstQuarterBelow leftRates.total floor request.tolerance
  let last := Search.firstQuarterBelow rightRates.total first request.tolerance
  ⟨last, (Search.firstQuarterBelow_ge _ _ _).trans
      (Search.firstQuarterBelow_ge _ _ _),
    (quarterRadius_antitone leftRates.total_nonnegative
      (Search.firstQuarterBelow_ge _ _ _)).trans_lt
      (Search.firstQuarterBelow_accurate leftRates.total leftRates.total_nonnegative
        floor request.tolerance request.tolerance_positive),
    Search.firstQuarterBelow_accurate rightRates.total rightRates.total_nonnegative
      first request.tolerance request.tolerance_positive⟩

open Purelib.Topology.Surface.Sewing.Bilinear.Refinement in
/-- A retained geometric contact bound gives local accuracy for an existing sample with exact family readback. -/
private theorem localAccuracy {family : Nat → Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
    (rates : SewnPrimitiveRefinement.ContactRates contacts family) {first stage : Nat}
    (accurate : Geometric.Basic.quarterRadius rates.total first < request.tolerance)
    (later : first ≤ stage) {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
    (surface : SewnPrimitiveSamples.CachedSample patch localValues) (readback : ∀ source, localValues source = family
      stage source) :
    Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests.LocalAccuracy request.tolerance surface.sewn.readings := by
  apply SewnPrimitiveContacts.localAccuracy_of_sourceContacts surface.sewn.readings
  intro contact member
  have bound := (rates.mismatch_le stage contact (by rw [contacts.entries_eq]; exact member)).trans_lt
    ((quarterRadius_antitone rates.total_nonnegative later).trans_lt accurate)
  simpa only [SourceContact.mismatch, SourceEdge.increment, readback] using bound.le

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
/-- Every later cached bilinear sample satisfies the original requested area accuracy.

Pointwise family readbacks and the original magnitude bounds connect both retained contact-rate certificates to that
exact sample. -/
theorem accurate (refinement : Refinement request leftRates rightRates floor) {stage : Nat}
    (later : refinement.index ≤ stage) {leftLocal rightLocal : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
    {left : SewnPrimitiveSamples.CachedSample patch leftLocal} {right : SewnPrimitiveSamples.CachedSample patch
      rightLocal}
    (sample : Samples left right)
    (leftReadback : ∀ source, leftLocal source = leftFamily stage source)
    (rightReadback : ∀ source, rightLocal source = rightFamily stage source)
    (bounded : ∀ position (index : Fin 3),
      (PrimitivePoint.Bounded (⟨leftLocal (Errors.traceAt left position).source index - leftLocal (Errors.traceAt left
        position).source 0,
        rightLocal (Errors.traceAt left position).source index - rightLocal (Errors.traceAt left position).source 0⟩ :
          Purelib.Topology.Polygon.Stokes.PrimitivePoint)) magnitude) :
    Data.Gaussian.Norm.Basic.normSq (sample.boundaryArea - FiniteSum.Fin.sumFin (fun position =>
      Stokes.triangleWedgeArea
      ⟨leftLocal (Errors.traceAt left position).source 0, rightLocal (Errors.traceAt left position).source 0⟩
      ⟨leftLocal (Errors.traceAt left position).source 1, rightLocal (Errors.traceAt left position).source 1⟩
      ⟨leftLocal (Errors.traceAt left position).source 2, rightLocal (Errors.traceAt left position).source 2⟩)) < target
        :=
  request.accurate sample
    (localAccuracy leftRates refinement.leftAccurate later left leftReadback)
    (localAccuracy rightRates refinement.rightAccurate later right rightReadback) bounded

end Refinement
end Purelib.Topology.Surface.Sewing.Bilinear
