module

import Purelib.Integration.Path.JoinedTrace
public import Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Paths.RectangularHorizontalTraceLengths
import Purelib.Riemann.Paths.RectangularVerticalTraceLengths
public import Purelib.Integration.Path.TraceLengths
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Meshes.RectangularObservationMesh

@[expose] public section

/-! Owned perimeter traces preserve the forward ordering and exact physical
endpoints of the original dyadic traces. -/
namespace Purelib.Riemann.Integration.RectangularOwnedPerimeterOrder
open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian)
open Purelib.Integration.Path.JoinedTrace (VertexTrace)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces (bottomOwned topOwned leftOwned rightOwned)
open Purelib.Riemann.Integration.RectangularCenteredPerimeter
open Purelib.Integration.Path.TraceLengths.VertexTrace (Ordered ordered_ofIndexed)

variable {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry} {box : Box}
  {mesh : ObservationMesh cuts box}

open Purelib.Integration.Path in
open Purelib.Riemann.Paths in
/-- The retained bottom perimeter vertices are ordered by their original real coordinates. -/
theorem bottomOwned_ordered (traces : PerimeterTraces mesh) :
    TraceLengths.VertexTrace.Ordered (bottomOwned traces) (fun owner => owner.point.re) := by
  apply TraceLengths.VertexTrace.ordered_ofIndexed
  intro edge
  exact TraceLengths.VertexTrace.ordered_indexed traces.bottom.vertices (fun vertex => (traces.bottom.point vertex).re)
    (RectangularHorizontalTraceLengths.ordered traces.bottom) edge

open Purelib.Riemann.Integration in
/-- The first retained bottom vertex is the original lower-left box corner. -/
theorem bottomOwned_first_point (traces : PerimeterTraces mesh) :
    (bottomOwned traces).first.point = ⟨box.xLower, box.yLower⟩ :=
  RectangularCenteredPerimeter.bottom_first_point traces

open Purelib.Integration.Path in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- The last retained bottom vertex is the original lower-right box corner. -/
theorem bottomOwned_last_point (traces : PerimeterTraces mesh) :
    (bottomOwned traces).last.point = ⟨box.xUpper, box.yLower⟩ := by
  rw [RectangularOwnedPerimeterTraces.bottomOwned, JoinedTrace.VertexTrace.ofIndexed_last]
  exact RectangularCenteredPerimeter.bottom_last_point traces

open Purelib.Integration.Path in
open Purelib.Riemann.Paths in
/-- The retained top perimeter vertices are ordered by their original real coordinates. -/
theorem topOwned_ordered (traces : PerimeterTraces mesh) :
    TraceLengths.VertexTrace.Ordered (topOwned traces) (fun owner => owner.point.re) := by
  apply TraceLengths.VertexTrace.ordered_ofIndexed
  intro edge
  exact TraceLengths.VertexTrace.ordered_indexed traces.top.vertices (fun vertex => (traces.top.point vertex).re)
    (RectangularHorizontalTraceLengths.ordered traces.top) edge

open Purelib.Riemann.Integration in
/-- The first retained top vertex is the original upper-left box corner. -/
theorem topOwned_first_point (traces : PerimeterTraces mesh) :
    (topOwned traces).first.point = ⟨box.xLower, box.yUpper⟩ :=
  RectangularCenteredPerimeter.top_first_point traces

open Purelib.Integration.Path in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- The last retained top vertex is the original upper-right box corner. -/
theorem topOwned_last_point (traces : PerimeterTraces mesh) :
    (topOwned traces).last.point = ⟨box.xUpper, box.yUpper⟩ := by
  rw [RectangularOwnedPerimeterTraces.topOwned, JoinedTrace.VertexTrace.ofIndexed_last]
  exact RectangularCenteredPerimeter.top_last_point traces

open Purelib.Integration.Path in
open Purelib.Riemann.Paths in
/-- The retained left perimeter vertices are ordered by their original imaginary coordinates. -/
theorem leftOwned_ordered (traces : PerimeterTraces mesh) :
    TraceLengths.VertexTrace.Ordered (leftOwned traces) (fun owner => owner.point.im) := by
  apply TraceLengths.VertexTrace.ordered_ofIndexed
  intro edge
  exact TraceLengths.VertexTrace.ordered_indexed traces.left.vertices (fun vertex => (traces.left.point vertex).im)
    (RectangularVerticalTraceLengths.ordered traces.left) edge

open Purelib.Riemann.Integration in
/-- The first retained left vertex is the original lower-left box corner. -/
theorem leftOwned_first_point (traces : PerimeterTraces mesh) :
    (leftOwned traces).first.point = ⟨box.xLower, box.yLower⟩ :=
  RectangularCenteredPerimeter.left_first_point traces

open Purelib.Integration.Path in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- The last retained left vertex is the original upper-left box corner. -/
theorem leftOwned_last_point (traces : PerimeterTraces mesh) :
    (leftOwned traces).last.point = ⟨box.xLower, box.yUpper⟩ := by
  rw [RectangularOwnedPerimeterTraces.leftOwned, JoinedTrace.VertexTrace.ofIndexed_last]
  exact RectangularCenteredPerimeter.left_last_point traces

open Purelib.Integration.Path in
open Purelib.Riemann.Paths in
/-- The retained right perimeter vertices are ordered by their original imaginary coordinates. -/
theorem rightOwned_ordered (traces : PerimeterTraces mesh) :
    TraceLengths.VertexTrace.Ordered (rightOwned traces) (fun owner => owner.point.im) := by
  apply TraceLengths.VertexTrace.ordered_ofIndexed
  intro edge
  exact TraceLengths.VertexTrace.ordered_indexed traces.right.vertices (fun vertex => (traces.right.point vertex).im)
    (RectangularVerticalTraceLengths.ordered traces.right) edge

open Purelib.Riemann.Integration in
/-- The first retained right vertex is the original lower-right box corner. -/
theorem rightOwned_first_point (traces : PerimeterTraces mesh) :
    (rightOwned traces).first.point = ⟨box.xUpper, box.yLower⟩ :=
  RectangularCenteredPerimeter.right_first_point traces

open Purelib.Integration.Path in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- The last retained right vertex is the original upper-right box corner. -/
theorem rightOwned_last_point (traces : PerimeterTraces mesh) :
    (rightOwned traces).last.point = ⟨box.xUpper, box.yUpper⟩ := by
  rw [RectangularOwnedPerimeterTraces.rightOwned, JoinedTrace.VertexTrace.ofIndexed_last]
  exact RectangularCenteredPerimeter.right_last_point traces

end Purelib.Riemann.Integration.RectangularOwnedPerimeterOrder
