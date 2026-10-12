module
import Purelib.Data.Vector.Basic

import Purelib.Integration.Path.JoinedTrace
import Purelib.LinearAlgebra.Grid.Offsets
public import Purelib.Integration.Path.JoinedTraceIndices
public import Purelib.Riemann.Readings.RectangularPointReadings

@[expose] public section

/-! Restrict cached point readings to an original joined-trace occurrence.
The executable adapter copies retained owners and values only. -/
namespace Purelib.Riemann.Paths.RectangularJoinedTraceReadings

open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Integration.Path.JoinedTrace (VertexTrace)
open Purelib.Integration.Path.JoinedTrace.VertexTrace (ofIndexed)
open Purelib.Integration.Path.JoinedTraceIndices (Embedding)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Polynomial)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
variable {Vertex : Type} {part whole : Purelib.Integration.Path.JoinedTrace.VertexTrace Vertex}
  {polynomial numerator : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
  {models : Bank polynomial geometry} {primitives : Primitives models numerator}
  {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
  {point : Vertex → Gaussian}

section
open Purelib.Integration
open Purelib.Data
/-- Restrict cached rectangular point readings along a retained trace embedding.

Copy the existing owners and values at the embedding's exact indices, preserving their point and aligned-value
equations. -/
def readings (embedding : Path.JoinedTraceIndices.Embedding part whole)
    (original : PointReadings anchors offsets (fun vertex => point (whole.indexed vertex))) :
    PointReadings anchors offsets (fun vertex => point (part.indexed vertex)) :=
  let owners := Vector.Basic.vectorOfFn (fun vertex => original.owners (embedding.index vertex))
  let values := Vector.Basic.vectorOfFn (fun vertex => original.values (embedding.index vertex))
  { owners := owners
    point_eq := by
      intro vertex
      dsimp only [owners]
      rw [Vector.Basic.vectorOfFn_apply, original.point_eq, embedding.indexed_eq]
    values := values
    value_eq := by
      intro vertex
      dsimp only [values, owners]
      rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
      exact original.value_eq (embedding.index vertex) }

/-- A restricted trace value is the original cached value at its embedding index. -/
theorem readings_value (embedding : Path.JoinedTraceIndices.Embedding part whole)
    (original : PointReadings anchors offsets (fun vertex => point (whole.indexed vertex)))
    (vertex : Fin (part.rest.length + 1)) :
    (readings embedding original).values vertex = original.values (embedding.index vertex) :=
  Vector.Basic.vectorOfFn_apply (fun entry => original.values (embedding.index entry)) vertex

/-- A restricted trace owner is the original cached owner at its embedding index. -/
theorem readings_owner (embedding : Path.JoinedTraceIndices.Embedding part whole)
    (original : PointReadings anchors offsets (fun vertex => point (whole.indexed vertex)))
    (vertex : Fin (part.rest.length + 1)) :
    (readings embedding original).owners vertex = original.owners (embedding.index vertex) :=
  Vector.Basic.vectorOfFn_apply (fun entry => original.owners (embedding.index entry)) vertex

/-- Restrict cached point readings to an indexed trace occurrence.

Use the retained indexed embedding to copy the same owners and values without reevaluating primitives. -/
def readingsOfIndexed {count : Nat} {vertices : Fin (count + 1) → Vertex}
    (embedding : Path.JoinedTraceIndices.Embedding (Path.JoinedTrace.VertexTrace.ofIndexed vertices) whole)
    (original : PointReadings anchors offsets (fun vertex => point (whole.indexed vertex))) :
    PointReadings anchors offsets (fun vertex => point (vertices vertex)) :=
  let owners := Vector.Basic.vectorOfFn (fun vertex => original.owners (embedding.indexOfIndexed vertex))
  let values := Vector.Basic.vectorOfFn (fun vertex => original.values (embedding.indexOfIndexed vertex))
  { owners := owners
    point_eq := by
      intro vertex
      dsimp only [owners]
      rw [Vector.Basic.vectorOfFn_apply, original.point_eq, embedding.indexOfIndexed_eq]
    values := values
    value_eq := by
      intro vertex
      dsimp only [values, owners]
      rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
      exact original.value_eq (embedding.indexOfIndexed vertex) }

/-- The indexed adapter reads the original cached value at the retained index. -/
theorem readingsOfIndexed_value {count : Nat} {vertices : Fin (count + 1) → Vertex}
    (embedding : Path.JoinedTraceIndices.Embedding (Path.JoinedTrace.VertexTrace.ofIndexed vertices) whole)
    (original : PointReadings anchors offsets (fun vertex => point (whole.indexed vertex))) (vertex : Fin (count + 1)) :
    (readingsOfIndexed embedding original).values vertex = original.values (embedding.indexOfIndexed vertex) :=
  Vector.Basic.vectorOfFn_apply (fun entry => original.values (embedding.indexOfIndexed entry)) vertex

/-- The indexed adapter reads the original cached owner at the retained index. -/
theorem readingsOfIndexed_owner {count : Nat} {vertices : Fin (count + 1) → Vertex}
    (embedding : Path.JoinedTraceIndices.Embedding (Path.JoinedTrace.VertexTrace.ofIndexed vertices) whole)
    (original : PointReadings anchors offsets (fun vertex => point (whole.indexed vertex))) (vertex : Fin (count + 1)) :
    (readingsOfIndexed embedding original).owners vertex = original.owners (embedding.indexOfIndexed vertex) :=
  Vector.Basic.vectorOfFn_apply (fun entry => original.owners (embedding.indexOfIndexed entry)) vertex

end

open Purelib.Integration in
/-- Transport an existing pointwise readback through the indexed trace adapter. -/
theorem readingsOfIndexed_spec {count : Nat} {vertices : Fin (count + 1) → Vertex}
    (embedding : Path.JoinedTraceIndices.Embedding (Path.JoinedTrace.VertexTrace.ofIndexed vertices) whole)
    (original : PointReadings anchors offsets (fun vertex => point (whole.indexed vertex)))
    (values : Vertex → Gaussian) (readback : ∀ vertex, original.values vertex = values (whole.indexed vertex))
    (vertex : Fin (count + 1)) :
    (readingsOfIndexed embedding original).values vertex = values (vertices vertex) :=
  (readingsOfIndexed_value embedding original vertex).trans
    ((readback (embedding.indexOfIndexed vertex)).trans (congrArg values (embedding.indexOfIndexed_eq vertex)))

end Purelib.Riemann.Paths.RectangularJoinedTraceReadings
