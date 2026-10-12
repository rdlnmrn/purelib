module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Vector.Basic

import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.JoinedTraceProperties
import Purelib.LinearAlgebra.Grid.Offsets
public import Purelib.Integration.Path.PairedEndpointPolygon
public import Purelib.Riemann.Readings.RectangularPointReadings

@[expose] public section

/-! Endpoint polygons share coordinates while retaining both original model
owners. Every differential reading consumes these cached owners. -/
namespace Purelib.Riemann.Readings.RectangularPairedEndpointReadings

open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial Gaussian)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Integration.Path.JoinedTrace (VertexTrace)
open Purelib.Integration.Path.PairedEndpointPolygon
  (pairedEndpointPolygon pairedEndpointPolygon_all)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

variable {leftColumns leftRows rightColumns rightRows count : Nat}
  {leftGeometry : Geometry leftColumns leftRows} {rightGeometry : Geometry rightColumns rightRows}

open Purelib.Integration in
open Purelib.Data in
set_option genInjectivity false in
/-- Shared polygon coordinates with both original endpoint owners retained.

Each owner vector is exactly the corresponding projection of the paired endpoint polygon, and both project to the same
cached point vector. -/
structure PairedEndpointReadingsGeometry
    (first : Fin (count + 1) → Path.JoinedTrace.VertexTrace (OwnedVertex leftGeometry))
    (last : Fin (count + 1) → Path.JoinedTrace.VertexTrace (OwnedVertex rightGeometry)) where
  /-- The original left owners in endpoint-polygon order. -/ leftOwners : Data.Vector (OwnedVertex leftGeometry)
    (Path.PairedEndpointPolygon.pairedEndpointPolygon first last).rest.length.succ
  /-- The original right owners in endpoint-polygon order. -/ rightOwners : Data.Vector (OwnedVertex
    rightGeometry) (Path.PairedEndpointPolygon.pairedEndpointPolygon first last).rest.length.succ
  /-- Each left owner is the paired polygon's original first projection. -/ left_eq : ∀ vertex, leftOwners vertex =
    ((Path.PairedEndpointPolygon.pairedEndpointPolygon first last).indexed vertex).1
  /-- Each right owner is the paired polygon's original second projection. -/ right_eq : ∀ vertex, rightOwners vertex =
    ((Path.PairedEndpointPolygon.pairedEndpointPolygon first last).indexed vertex).2
  /-- The cached common polygon coordinates. -/ points : Data.Vector Gaussian
    (Path.PairedEndpointPolygon.pairedEndpointPolygon first last).rest.length.succ
  /-- The retained left owners project to the cached coordinates. -/ left_point : ∀ vertex, (leftOwners vertex).point =
    points vertex
  /-- The retained right owners project to the same cached coordinates. -/ right_point : ∀ vertex, (rightOwners
    vertex).point = points vertex

constructive_injectivity PairedEndpointReadingsGeometry

namespace PairedEndpointReadingsGeometry

variable {first : Fin (count + 1) → Purelib.Integration.Path.JoinedTrace.VertexTrace (OwnedVertex leftGeometry)}
  {last : Fin (count + 1) → Purelib.Integration.Path.JoinedTrace.VertexTrace (OwnedVertex rightGeometry)}

open Purelib.Integration in
open Purelib.Data in
/-- Cache both endpoint-owner vectors and their common coordinates.

Matching starts and ends of the paired traces certify coordinate agreement throughout the actual endpoint polygon. -/
def build (first : Fin (count + 1) → Path.JoinedTrace.VertexTrace (OwnedVertex leftGeometry))
    (last : Fin (count + 1) → Path.JoinedTrace.VertexTrace (OwnedVertex rightGeometry))
    (starts : ∀ index, (first index).first.point = (last index).first.point)
    (ends : ∀ index, (first index).last.point = (last index).last.point) :
    PairedEndpointReadingsGeometry first last := by
  let trace := Path.PairedEndpointPolygon.pairedEndpointPolygon first last
  have matching := Path.PairedEndpointPolygon.pairedEndpointPolygon_all first last
    (fun pair => pair.1.point = pair.2.point) starts ends
  let leftOwners := Vector.Basic.vectorOfFn (fun vertex => (trace.indexed vertex).1)
  let rightOwners := Vector.Basic.vectorOfFn (fun vertex => (trace.indexed vertex).2)
  let points := Vector.Basic.vectorOfFn (fun vertex => (trace.indexed vertex).1.point)
  refine ⟨leftOwners, rightOwners, Vector.Basic.vectorOfFn_apply _, Vector.Basic.vectorOfFn_apply _, points, ?_, ?_⟩
  · intro vertex
    dsimp only [leftOwners, points]
    rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
  · intro vertex
    dsimp only [rightOwners, points]
    rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
    exact (Path.JoinedTraceProperties.All.indexed matching vertex).symm

section
open Purelib.LinearAlgebra
/-- Evaluate aligned primitives through the cached left endpoint owners.

The returned point readings retain the same owner vector and its common-coordinate equation. -/
def leftReadings (geometry : PairedEndpointReadingsGeometry first last) {polynomial numerator : Polynomial}
    {models : Bank polynomial leftGeometry} {primitives : Primitives models numerator}
    (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges) :
    PointReadings anchors offsets (fun vertex => geometry.points vertex) :=
  PointReadings.build anchors offsets (fun vertex => geometry.points vertex) geometry.leftOwners geometry.left_point

/-- Evaluate aligned primitives through the cached right endpoint owners.

The returned point readings retain the same owner vector and its common-coordinate equation. -/
def rightReadings (geometry : PairedEndpointReadingsGeometry first last) {polynomial numerator : Polynomial}
    {models : Bank polynomial rightGeometry} {primitives : Primitives models numerator}
    (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges) :
    PointReadings anchors offsets (fun vertex => geometry.points vertex) :=
  PointReadings.build anchors offsets (fun vertex => geometry.points vertex) geometry.rightOwners geometry.right_point

end

open Purelib.Integration
open Purelib.LinearAlgebra
/-- A left reading is the aligned primitive at the paired polygon's original left owner. -/
theorem leftReadings_value (geometry : PairedEndpointReadingsGeometry first last) {polynomial numerator : Polynomial}
    {models : Bank polynomial leftGeometry} {primitives : Primitives models numerator}
    (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (vertex : Fin ((Path.PairedEndpointPolygon.pairedEndpointPolygon first last).rest.length + 1)) :
    (geometry.leftReadings anchors offsets).values vertex =
      let owner := ((Path.PairedEndpointPolygon.pairedEndpointPolygon first last).indexed vertex).1
      anchors.alignedValue offsets owner.column owner.row owner.point := by
  rw [(geometry.leftReadings anchors offsets).value_eq]
  change anchors.alignedValue offsets (geometry.leftOwners vertex).column
    (geometry.leftOwners vertex).row (geometry.leftOwners vertex).point = _
  rw [geometry.left_eq]

/-- A right reading is the aligned primitive at the paired polygon's original right owner. -/
theorem rightReadings_value (geometry : PairedEndpointReadingsGeometry first last) {polynomial numerator : Polynomial}
    {models : Bank polynomial rightGeometry} {primitives : Primitives models numerator}
    (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (vertex : Fin ((Path.PairedEndpointPolygon.pairedEndpointPolygon first last).rest.length + 1)) :
    (geometry.rightReadings anchors offsets).values vertex =
      let owner := ((Path.PairedEndpointPolygon.pairedEndpointPolygon first last).indexed vertex).2
      anchors.alignedValue offsets owner.column owner.row owner.point := by
  rw [(geometry.rightReadings anchors offsets).value_eq]
  change anchors.alignedValue offsets (geometry.rightOwners vertex).column
    (geometry.rightOwners vertex).row (geometry.rightOwners vertex).point = _
  rw [geometry.right_eq]

end PairedEndpointReadingsGeometry
end Purelib.Riemann.Readings.RectangularPairedEndpointReadings
