module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Norm.Basic

public section

/-!
# A common finite accuracy index on fixed sewn geometry

Analytic contact rates are cached before any larger polynomial is built.
Their finite sum and the actual assembly amplification select one index,
beyond any existing surface index. Sampling then retains the original local
values, the sewn values, and the complete face-error bank. This layer pays
proved local rates; constructing those rates from the actual curve sheets
remains the responsibility of the analytic model layer.
-/

section

open Purelib

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.Patch

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.PrimitiveSewing.CutPatch

open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces

namespace Purelib.Topology.Surface.Sewing.SewnPrimitiveRefinement

open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceContact ContactBank)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests (LocalMismatch LocalAccuracy Request)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (FaceBank Coordinate)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)

open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}

set_option genInjectivity false in
/-- A checked rate for one actual original-face contact. No successful finite test or exact matching of its increments
is required. -/
structure ContactRate (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount)
    (family : Nat → Fin faceCount → PrimitiveSewing.PrimitiveValues 3) where
  /-- Original face contact whose mismatch is bounded. -/ contact : SewnPrimitiveContacts.SourceContact faces
  /-- Fixed geometric-decay scale for this contact. -/ scale : SewnPrimitiveFaces.Coordinate
  /-- The contact's retained scale is nonnegative. -/ nonnegative : 0 ≤ scale
  /-- Every family index bounds this contact's mismatch by its quarter-geometric radius. -/ bounded : ∀ index,
    contact.mismatch (family index) ≤ Geometric.Basic.quarterRadius scale index

constructive_injectivity ContactRate

variable {family : Nat → Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
  {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
  {patch : Patch.CutPatch faces indices boundary} {assembly : CutPatch.Assembly faces patch}

set_option genInjectivity false in
/-- Checked geometric decay rates for the exact retained contact bank.

The entry list reproduces every original contact, and its cached scale sum supplies a common bound for later family
indices. -/
structure ContactRates (contacts : SewnPrimitiveContacts.ContactBank assembly) (family : Nat → Fin faceCount →
  PrimitiveSewing.PrimitiveValues 3) where
  /-- Checked rate entries for the retained contact occurrences. -/ entries : List (SewnPrimitiveRefinement.ContactRate
    faces family)
  /-- The rate entries reproduce the original contact bank in order. -/ contacts_eq : entries.map
    Purelib.Topology.Surface.Sewing.SewnPrimitiveRefinement.ContactRate.contact = contacts.entries
  /-- Cached finite sum of the contact-rate scales. -/ total : SewnPrimitiveFaces.Coordinate
  /-- The cached total is the exact coordinate sum of retained entry scales. -/ total_eq : total = Squares.coordinateSum
    (entries.map Purelib.Topology.Surface.Sewing.SewnPrimitiveRefinement.ContactRate.scale)

constructive_injectivity ContactRates

namespace ContactRates

variable {contacts : SewnPrimitiveContacts.ContactBank assembly}

/-- Package the original contact-rate list and cache its finite scale sum. -/
@[expose] def build (entries : List (SewnPrimitiveRefinement.ContactRate faces family))
    (coverage : entries.map Purelib.Topology.Surface.Sewing.SewnPrimitiveRefinement.ContactRate.contact =
      contacts.entries) : SewnPrimitiveRefinement.ContactRates contacts family :=
  ⟨entries, coverage, Squares.coordinateSum (entries.map
    Purelib.Topology.Surface.Sewing.SewnPrimitiveRefinement.ContactRate.scale), rfl⟩

/-- The cached total contact scale is nonnegative. -/
theorem total_nonnegative (rates : SewnPrimitiveRefinement.ContactRates contacts family) : 0 ≤ rates.total := by
  rw [rates.total_eq]
  exact Squares.coordinateSum_map_nonnegative ContactRate.scale rates.entries (fun entry _ => entry.nonnegative)

/-- The common total rate bounds each original contact mismatch at every family index. -/
theorem mismatch_le (rates : SewnPrimitiveRefinement.ContactRates contacts family) (index : Nat)
    (contact : SewnPrimitiveContacts.SourceContact faces) (member : contact ∈ contacts.entries) :
    contact.mismatch (family index) ≤ Geometric.Basic.quarterRadius rates.total index := by
  rw [← rates.contacts_eq] at member
  rcases Map.mem_map.mp member with ⟨entry, entryMember, equal⟩
  rw [← equal]
  apply (entry.bounded index).trans
  rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    ((Squares.coordinate_le_coordinateSum_map ContactRate.scale rates.entries (fun entry _ => entry.nonnegative) entry
      entryMember).trans_eq rates.total_eq.symm)
    (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide : (0 : SewnPrimitiveFaces.Coordinate) ≤ 1 / 4) index)

end ContactRates

set_option genInjectivity false in
/-- The index is chosen entirely from retained geometry and fixed rates. The floor permits reuse of an already selected
surface triangulation. -/
structure ContactRefinement {contacts : SewnPrimitiveContacts.ContactBank assembly} (rates :
  SewnPrimitiveRefinement.ContactRates contacts family)
    {target : SewnPrimitiveFaces.Coordinate} (request : SewnPrimitiveRequests.Request assembly target) (floor : Nat)
      where
  /-- Selected family index for the requested tolerance. -/ index : Nat
  /-- The selected index respects the retained lower floor. -/ later : floor ≤ index
  /-- The total quarter-geometric radius is strictly below the request tolerance. -/ accurate :
    Geometric.Basic.quarterRadius rates.total index < request.tolerance

constructive_injectivity ContactRefinement

namespace ContactRefinement

variable {contacts : SewnPrimitiveContacts.ContactBank assembly} {rates :
  Purelib.Topology.Surface.Sewing.SewnPrimitiveRefinement.ContactRates contacts family}
  {target : SewnPrimitiveFaces.Coordinate} {request : SewnPrimitiveRequests.Request assembly target} {floor : Nat}

/-- Find a family index beyond the given floor meeting the request's local tolerance. -/
@[expose] def build (rates : SewnPrimitiveRefinement.ContactRates contacts family) (request :
  SewnPrimitiveRequests.Request assembly target) (floor : Nat) :
    SewnPrimitiveRefinement.ContactRefinement rates request floor :=
  ⟨Search.firstQuarterBelow rates.total floor request.tolerance,
    Search.firstQuarterBelow_ge _ _ _,
    Search.firstQuarterBelow_accurate rates.total rates.total_nonnegative floor _ request.tolerance_positive⟩

/-- Every retained original contact meets the local tolerance at the selected index. -/
theorem mismatch_lt (refinement : SewnPrimitiveRefinement.ContactRefinement rates request floor)
    (contact : SewnPrimitiveContacts.SourceContact faces) (member : contact ∈ contacts.entries) :
    contact.mismatch (family refinement.index) < request.tolerance :=
  (rates.mismatch_le refinement.index contact member).trans_lt refinement.accurate

set_option genInjectivity false in
/-- All three banks are actual executable data, not bounds on a recomputed sewing. Original face samples are
materialized only at the selected index. -/
structure Sample (refinement : SewnPrimitiveRefinement.ContactRefinement rates request floor) where
  /-- Cached original local readings at the selected family index. -/ localValues : Data.Vector
    (PrimitiveSewing.PrimitiveValues 3) faceCount
  /-- Each cached source reading is the original family's reading at that index. -/ localValues_eq : ∀ source,
    localValues source = family refinement.index source
  /-- Actual assembly sample built from the retained local values. -/ sewn : Assembly.Sample assembly localValues
  /-- Cached face-error bank for that exact sewn sample. -/ faces : SewnPrimitiveFaces.FaceBank patch localValues
    sewn.values
  /-- The retained face bank is the one computed from the actual sewn readings. -/ faces_eq : faces = FaceBank.build
    sewn.readings
  /-- The actual cached aggregate squared error is strictly below the requested target. -/ accurate :
    faces.squaredErrors < target

constructive_injectivity Sample

/-- Materialize local values, sewn readings and face errors at the selected family index.

The result retains the actual caches and certifies their aggregate error against the original request target. -/
@[expose] def sample (refinement : SewnPrimitiveRefinement.ContactRefinement rates request floor) :
  ContactRefinement.Sample refinement :=
  let localValues := Data.Vector.Basic.vectorOfFn (family refinement.index)
  let sewn := Assembly.sample localValues assembly
  let faces := FaceBank.build sewn.readings
  { localValues := localValues
    localValues_eq := Data.Vector.Basic.vectorOfFn_apply _
    sewn := sewn
    faces := faces
    faces_eq := rfl
    accurate := contacts.accurate request sewn.readings (by
      intro contact member
      simpa only [SourceContact.mismatch, SourceEdge.increment, localValues, Data.Vector.Basic.vectorOfFn_apply,
        -eq_self, -iff_self]
        using (refinement.mismatch_lt contact member).le) }

end ContactRefinement

end Purelib.Topology.Surface.Sewing.SewnPrimitiveRefinement

end
