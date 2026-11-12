module

public import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Membership
import Purelib.Data.Vector.Basic

/-! # Shared mesh values reusing original cached point readings

The finite selector matches a coordinate and both numerical cell indices
on the SAME primitive/anchor/offset owners. It makes no comparison of
square-root Owners, labels or independent primitive normalizations.
Only unmatched mesh vertices receive new polynomial evaluations.
-/

public section

namespace Purelib.Riemann.Readings.RectangularPointReadings.PointReadings

open Purelib
open Purelib.Data.List
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial Gaussian)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex ModelTriangle OwnedTriangulation)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)

variable {polynomial numerator : Polynomial} {columns rows count pairs : Nat}
variable {geometry : Geometry columns rows} {models : Bank polynomial geometry}
variable {primitives : Primitives models numerator pairs} {anchors : PrimitiveAnchors primitives}
variable {offsets : LinearAlgebra.Grid.Offsets anchors.edges} {points : Fin count → Gaussian}
variable (fixed : PointReadings anchors offsets points)
variable {triangles : List (ModelTriangle geometry)} (surface : OwnedTriangulation triangles)

/-- A cached point reading uses this exact numerical coordinate and pair of containing-cell indices. -/
abbrev SameLocation (owner : OwnedVertex geometry) (index : Fin count) : Prop :=
  (fixed.owners index).column = owner.column ∧ (fixed.owners index).row = owner.row ∧
    (fixed.owners index).point = owner.point

/-- Select the first cached reading at the same coordinate and numerical cell on the supplied finite index list. -/
@[expose] def select (owner : OwnedVertex geometry) : List (Fin count) → Option (Fin count)
  | [] => none
  | index :: remaining =>
      if fixed.SameLocation owner index then some index else select owner remaining

/-- A successful finite selection retains the actual cached coordinate and numerical cell indices. -/
theorem select_some (owner : OwnedVertex geometry) (indices : List (Fin count)) (index : Fin count)
    (found : fixed.select owner indices = some index) : fixed.SameLocation owner index := by
  induction indices with
  | nil => cases found
  | cons head rest ih =>
      by_cases same : fixed.SameLocation owner head
      · rewrite [select, if_pos same] at found
        cases found
        exact same
      · rewrite [select, if_neg same] at found
        exact ih found

/-- A failed finite selection certifies that no listed cached reading has the displayed coordinate and cell indices. -/
theorem select_none (owner : OwnedVertex geometry) (indices : List (Fin count))
    (absent : fixed.select owner indices = none) :
    ∀ index ∈ indices, ¬ fixed.SameLocation owner index := by
  induction indices with
  | nil => intro index member; exact (List.not_mem_nil member).elim
  | cons head rest ih =>
      by_cases same : fixed.SameLocation owner head
      · rewrite [select, if_pos same] at absent
        cases absent
      · rewrite [select, if_neg same] at absent
        intro index member
        rcases Membership.mem_cons.mp member with equal | member
        · cases equal
          exact same
        · exact ih absent index member

/-- Retain every actual finite reading selection at the original mesh vertex owners. -/
@[expose] def Selection : Type :=
  {value : Data.Vector (Option (Fin count)) surface.mesh.vertices.length //
    value = vectorOfFn (fun vertex => fixed.select (surface.owners vertex) (List.ofFn id))}

/-- Materialize the original finite selections once, before constructing new shared values. -/
def selectMesh : fixed.Selection surface :=
  let indices := List.ofFn (fun index : Fin count => index)
  let selected := vectorOfFn fun vertex => fixed.select (surface.owners vertex) indices
  ⟨selected, rfl⟩

variable {fixed surface}

/-- A retained vertex selection has the original first-match readback on the complete finite cached point bank. -/
theorem selection_eq (selected : fixed.Selection surface) (vertex : Fin surface.mesh.vertices.length) :
    selected.val vertex = fixed.select (surface.owners vertex) (List.ofFn id) := by
  have same := congrArg (fun values : Data.Vector (Option (Fin count)) surface.mesh.vertices.length => values vertex)
    selected.property
  rewrite [vectorOfFn_apply] at same
  exact same

/-- Construct original SharedPrimitiveValues using cached readings on selected matches and new evaluations elsewhere. -/
def ofSelection (selected : fixed.Selection surface) : SharedPrimitiveValues anchors offsets surface where
  values := vectorOfFn fun vertex =>
    match selected.val vertex with
    | some index => fixed.values index
    | none => anchors.alignedValue offsets (surface.owners vertex).column
        (surface.owners vertex).row (surface.owners vertex).point
  value_eq := fun vertex => by
    rewrite [vectorOfFn_apply]
    cases same : selected.val vertex with
    | none => rfl
    | some index =>
        have found := fixed.select_some (surface.owners vertex) (List.ofFn id) index
          ((selection_eq selected vertex).symm.trans same)
        have value := fixed.value_eq index
        rewrite [found.1, found.2.1, found.2.2] at value
        exact value

variable (fixed surface)

/-- Retain the whole original point bank, materialized selectors and new original shared mesh readings.

SharedPrimitiveValues alone does not retain the source reading bank or
the selection decisions. These original Sigma/Subtype containers retain
both, with exact factory laws, without a replacement numerical owner.
-/
@[expose] def OnMesh : Type :=
  Σ original : {value : PointReadings anchors offsets points // value = fixed},
  Σ selected : original.val.Selection surface,
  {value : SharedPrimitiveValues anchors offsets surface // value = ofSelection selected}

namespace OnMesh

/-- Keep the complete old bank verbatim, select its matching entries once and evaluate only unmatched vertices. -/
def build (fixed : PointReadings anchors offsets points) (surface : OwnedTriangulation triangles) :
    fixed.OnMesh surface :=
  let original := fixed
  let selected := original.selectMesh surface
  let shared := ofSelection selected
  ⟨⟨original, rfl⟩, selected, ⟨shared, rfl⟩⟩

variable {fixed surface}
variable (cached : fixed.OnMesh surface)

/-- Read the complete original supplied point bank, including every old outside value and owner. -/
@[expose] def original : PointReadings anchors offsets points := cached.1.val

/-- Read the materialized same-location selectors on the original retained mesh owners. -/
@[expose] def selected : cached.original.Selection surface := cached.2.1

/-- Read the actual original SharedPrimitiveValues on this same surface. -/
@[expose] def shared : SharedPrimitiveValues anchors offsets surface := cached.2.2.val

/-- The whole original bank is literally the supplied old cache. -/
theorem original_eq : cached.original = fixed := cached.1.property

/-- Every cached selection retains the whole original finite first-match factory equality. -/
theorem selected_eq : cached.selected.val = vectorOfFn (fun vertex =>
    cached.original.select (surface.owners vertex) (List.ofFn id)) := cached.selected.property

/-- The actual shared value bank is its constructor on the SAME retained selections. -/
theorem shared_eq : cached.shared = ofSelection cached.selected := cached.2.2.property

/-- A successful stored selection returns that exact original cached value, rather than evaluating it anew. -/
theorem value_of_some (vertex : Fin surface.mesh.vertices.length) (index : Fin count)
    (found : cached.selected.val vertex = some index) :
    cached.shared.values vertex = cached.original.values index := by
  have same := congrArg
    (fun values : SharedPrimitiveValues anchors offsets surface => values.values vertex) cached.shared_eq
  rewrite [ofSelection, vectorOfFn_apply, found] at same
  exact same

/-- An actually matching old reading cannot take the fresh-evaluation branch at that mesh vertex. -/
theorem selected_ne_none (index : Fin count) (vertex : Fin surface.mesh.vertices.length)
    (same : fixed.SameLocation (surface.owners vertex) index) : cached.selected.val vertex ≠ none := by
  intro absent
  have originalSame : cached.original.SameLocation (surface.owners vertex) index := cached.original_eq.symm ▸ same
  have missing := cached.original.select_none (surface.owners vertex) (List.ofFn id)
    ((selection_eq cached.selected vertex).symm.trans absent)
  exact missing index (OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩) originalSame

/-- The actual mesh value at a matching original numerical owner is exactly its old cached scalar, without weakening. -/
theorem cached_eq (index : Fin count) (vertex : Fin surface.mesh.vertices.length)
    (same : fixed.SameLocation (surface.owners vertex) index) : cached.shared.values vertex = fixed.values index := by
  have current := cached.shared.value_eq vertex
  have old := fixed.value_eq index
  rewrite [same.1, same.2.1, same.2.2] at old
  exact current.trans old.symm

end OnMesh
end Purelib.Riemann.Readings.RectangularPointReadings.PointReadings

end
