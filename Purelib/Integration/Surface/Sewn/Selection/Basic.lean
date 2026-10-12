module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Filter
import Purelib.Data.List.Map
import Purelib.Topology.Polygon.WitnessReadbacks
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Selecting actual sewn face occurrences

Selection uses the retained source index, but copies the actual cut triangle
and its primitive-error trace. No primitive is descended to original vertices.
The exact area partition includes signed contributions and all seam offsets.
-/

namespace Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (FaceBank FaceTrace)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Data.List

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Purelib.Topology.Polygon.Stokes.OrientedTriangle
  vertexCount}
  {localValues : Fin faceCount → Purelib.Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3}

open Purelib.Integration in
open Purelib.Topology.Polygon in
open Purelib.Topology.Surface in
open Purelib.Topology.Surface.Sewing in
/-- Every retained bank trace projects through the cut labels to its source face.

The bank retains the exact triangle and source lists. Structural map readback
identifies the supplied member without replacing its source occurrence. -/
theorem FaceBank.trace_projection {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
    {patch : Cut.Patch.CutPatch faces indices boundary} {values : PrimitiveSewing.PrimitiveValues patch.count}
    (bank : SewnPrimitiveFaces.FaceBank patch localValues values) (trace : SewnPrimitiveFaces.FaceTrace localValues
      values) (member : trace ∈ bank.entries) :
    VertexSewing.OrientedTriangle.map patch.vertexLabels trace.triangle = faces trace.source := by
  have equal := (congrArg (List.map (VertexSewing.OrientedTriangle.map patch.vertexLabels)) bank.triangles_eq).trans
    (patch.triangles_eq.trans (congrArg (List.map faces) bank.sources_eq).symm)
  simp only [Map.map_map, Function.comp_def] at equal
  exact Map.maps_pointwise _ _ bank.entries equal trace member

namespace CachedSample

variable {patch : Purelib.Topology.Surface.Sewing.SewingTree.SewnPatch faces} (sample :
  Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample patch localValues)

open Purelib.Data.Gaussian in
open Purelib.Topology.Polygon in
open Purelib.Topology.Surface.Sewing in
set_option genInjectivity false in
/-- Cached selected face traces, triangles and area from the exact original sewn sample.

The selection predicate acts on retained source indices; each cached list and area has an exact readback to those
original traces. -/
structure FaceSelection (keep : Fin faceCount → Bool) where
  /-- The retained selected traces from the original face bank. -/ traces : List (SewnPrimitiveFaces.FaceTrace
    localValues sample.sewn.values)
  /-- The traces equal the original bank filtered by its exact source selection. -/ traces_eq : traces =
    sample.faces.entries.filter (fun trace => keep trace.source)
  /-- The cached triangles of the retained selected traces. -/ triangles : List (Stokes.OrientedTriangle
    patch.cut.count)
  /-- The triangles are exactly the triangle projection of the retained traces. -/ triangles_eq : triangles = traces.map
    SewnPrimitiveFaces.FaceTrace.triangle
  /-- The cached area of the retained selected triangle boundaries. -/ area : Basic.Canonical
  /-- The cached area is the exact boundary sum using the original sample energy values. -/ area_eq : area =
    Stokes.edgeListArea sample.energyValues (triangles.flatMap Stokes.OrientedTriangle.boundary)

constructive_injectivity FaceSelection

namespace FaceSelection

open Purelib.Integration in
open Purelib.Topology.Polygon in
open Purelib.Topology.Surface.Sewing in
/-- Cache the sample's selected traces, triangles and boundary-area sum.

The predicate filters the retained face-bank entries in their source order.
Triangle readback and the exact flattened boundary sum certify those caches. -/
@[expose] def build (keep : Fin faceCount → Bool) :
  Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample keep :=
  let traces := sample.faces.entries.filter (fun trace => keep trace.source)
  let triangles := traces.map SewnPrimitiveFaces.FaceTrace.triangle
  ⟨traces, rfl, triangles, rfl, Stokes.edgeListArea sample.energyValues (triangles.flatMap
    Stokes.OrientedTriangle.boundary), rfl⟩

variable {sample} {keep : Fin faceCount → Bool}

section
open Purelib.Integration
open Purelib.Topology.Surface.Sewing
/-- Each selected face trace projects through the cut labels to its source face.

The selection readback retains original-bank membership of the displayed
trace, whose projection uses the same source index and cut labels. -/
theorem trace_projection (selected : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample
  keep)
    (trace : SewnPrimitiveFaces.FaceTrace localValues sample.sewn.values) (member : trace ∈ selected.traces) :
    VertexSewing.OrientedTriangle.map patch.cut.vertexLabels trace.triangle = faces trace.source := by
  rw [selected.traces_eq] at member
  exact Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.FaceBank.trace_projection
    sample.faces trace (Filter.mem_filter.mp member).1

/-- Every selected trace's source index satisfies the selection predicate.

Membership is transferred through the retained filtered-list equality,
keeping the predicate and the exact source occurrence together. -/
theorem trace_kept (selected : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample keep)
    (trace : SewnPrimitiveFaces.FaceTrace localValues sample.sewn.values) (member : trace ∈ selected.traces) : keep
      trace.source = true := by
  rw [selected.traces_eq] at member
  exact (Filter.mem_filter.mp member).2

end

open Purelib.Integration in
open Purelib.Polynomial.Geometry.Grid in
open Purelib.Topology.Polygon in
/-- The selected area cache equals the filtered trace-area sum.

The retained triangle and trace readbacks identify the same selected
occurrences, preserving their boundary order and energy values. -/
theorem area_readback (selected : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample
  keep) :
    selected.area = CellBoundary.sumValues (fun trace => Stokes.edgeListArea sample.energyValues
      trace.triangle.boundary)
      (sample.faces.entries.filter (fun trace => keep trace.source)) := by
  rw [selected.area_eq, WitnessReadbacks.triangles_area, selected.triangles_eq, CellBoundary.sumValues_map,
    selected.traces_eq]

open Purelib.Integration
open Purelib.Polynomial.Geometry.Grid
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Sewing
/-- Complementary selected area caches partition the sample boundary area.

Both selections retain the same sample. Their complementary predicates
partition its face occurrences and the exact sewn boundary-area equality. -/
theorem partition (selected : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample keep)
    (remaining : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample (fun index => !(keep
      index))) :
    selected.area + remaining.area = sample.boundaryArea := by
  rw [selected.area_readback, remaining.area_readback,
    CellBoundary.sum_filter_partition]
  rw [← CellBoundary.sumValues_map (fun triangle : Stokes.OrientedTriangle patch.cut.count =>
    Stokes.edgeListArea sample.energyValues triangle.boundary) SewnPrimitiveFaces.FaceTrace.triangle,
    sample.faces.triangles_eq, ← WitnessReadbacks.triangles_area]
  exact sample.surface_eq_boundary

/-- A pairwise disjoint retained family of face selections and its complement partition the original boundary area.

All selections retain the same original sewn sample and source indices, so the family sum uses those exact cached areas.
-/
theorem family_partition {Label : Type} (labels : List Label) (keep : Label → Fin faceCount → Bool)
    (disjoint : labels.Pairwise (fun first second => ∀ index,
      keep first index = true → keep second index = true → False))
    (selected : (label : Label) → Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample
      (keep label))
    (remaining : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample (fun index =>
      !(labels.any (fun label => keep label index)))) :
    CellBoundary.sumValues (fun label => (selected label).area) labels + remaining.area = sample.boundaryArea := by
  have areas := CellBoundary.sumValues_congr _ _ labels
    (fun label _ => (selected label).area_readback)
  have separate : labels.Pairwise (fun first second => ∀ trace : SewnPrimitiveFaces.FaceTrace localValues
    sample.sewn.values,
      keep first trace.source = true → keep second trace.source = true → False) :=
    disjoint.imp (fun separated (trace : SewnPrimitiveFaces.FaceTrace localValues sample.sewn.values) => separated
      trace.source)
  rw [areas, ← CellBoundary.sum_filter_family _ _ labels separate,
    remaining.area_readback, CellBoundary.sum_filter_partition]
  rw [← CellBoundary.sumValues_map (fun triangle : Stokes.OrientedTriangle patch.cut.count =>
    Stokes.edgeListArea sample.energyValues triangle.boundary) SewnPrimitiveFaces.FaceTrace.triangle,
    sample.faces.triangles_eq, ← WitnessReadbacks.triangles_area]
  exact sample.surface_eq_boundary

end FaceSelection

open Purelib.Data.Gaussian in
open Purelib.Integration in
set_option genInjectivity false in
/-- A retained remaining face selection and removed area partitioning the original boundary area.

The original sample remains the owner, while the retained equality keeps the signed removed and remaining contributions
distinct. -/
structure AreaExcision where
  /-- The retained predicate selecting the original faces that remain. -/ keep : Fin faceCount → Bool
  /-- The retained remaining selection indexed by the exact original sample and predicate. -/ remaining :
    Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample keep
  /-- The retained signed area removed from the original sample. -/ removedArea : Basic.Canonical
  /-- The removed and remaining cached areas add to the original boundary area. -/ partition : removedArea +
    remaining.area = sample.boundaryArea

constructive_injectivity AreaExcision

namespace AreaExcision

variable {sample}

open Purelib.Integration in
/-- Build an excision certificate from the exact original selected and complementary face caches.

The retained remaining selection keeps the complement predicate, and the removed area reuses the original selected cache
with its partition equality. -/
@[expose] def build {keep : Fin faceCount → Bool}
    (removed : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample keep)
    (remaining : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection
      sample (fun index => !(keep index))) :
    Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.AreaExcision sample :=
  ⟨_, remaining, removed.area, removed.partition remaining⟩

open Purelib.Data.Gaussian in
open Purelib.Integration in
/-- Subtracting the removed area preserves the boundary comparison error.

The excision partition retains signed removed and remaining contributions,
so the scalar error equals that of the full sample against the reference. -/
theorem comparison_error (excision : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.AreaExcision sample)
    (periodArea : Basic.Canonical) :
    excision.remaining.area - (periodArea - excision.removedArea) = sample.boundaryArea - periodArea := by
  rw [← excision.partition]
  ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration in
/-- The boundary-area accuracy bound transports through the excision equality.

The same target and squared Gaussian error are retained while the reference
area is adjusted by the cached signed removed contribution. -/
theorem accurate (excision : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.AreaExcision sample)
    (periodArea : Basic.Canonical) {target : Fraction.Rational}
    (bound : Data.Gaussian.Norm.Basic.normSq (sample.boundaryArea - periodArea) < target) :
    Data.Gaussian.Norm.Basic.normSq
      (excision.remaining.area - (periodArea - excision.removedArea)) < target :=
  Eq.mpr (congrArg (fun value => Data.Gaussian.Norm.Basic.normSq value < target)
    (excision.comparison_error periodArea)) bound

end AreaExcision
end CachedSample
end Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces
