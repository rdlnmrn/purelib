module

public import Purelib.Riemann.Integration.PreparedConstantModels
public import Purelib.Riemann.Readings.RectangularPointReadings.SharedMesh.Paths
import Purelib.Polynomial.Geometry.ClearPath.Segments
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map

/-! # Actual axis subdivisions of retained prepared-parent children

The original localSegment fixes the physical child's axis. The same
retained horizontal and vertical mesh words realize their original ordered
axis steps. The transverse word is empty, while its outer route occurrence
remains present in the supplied chord and word preparations. These are
geometric readbacks; actual RootedQuery, Point, Entry, row and join evidence
remain their separate original owners.
-/

public section

namespace Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Riemann.Readings.RectangularPointReadings.Chord (MeshReadings)
open Purelib.Riemann.Readings.RectangularPointReadings.Chord.MeshReadings
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts SegmentSplit)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Polynomial.Geometry.Grid
open Purelib.LinearAlgebra.Grid (Offsets)

variable {genus : Nat} {curve : HyperellipticCurve genus} {basis : Differential genus}
    (parent : PreparedEdge curve basis)

/-- Two actual local unit parameters preserve the axis of the same original prepared segment. -/
theorem point_axis (lower upper : Rational)
    (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1) :
    (parent.point lower).im = (parent.point upper).im ∨
      (parent.point lower).re = (parent.point upper).re :=
  parent.localSegment.pointAt_axis lower upper lowerInside upperInside

variable {columns rows : Nat} {geometry : Geometry columns rows} {polynomial numerator : Polynomial}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator}
    {anchors : PrimitiveAnchors primitives} {offsets : Offsets anchors.edges}
    {cuts : GridCuts geometry} {sourceStart sourceFinish : Canonical}
    (split : SegmentSplit cuts sourceStart sourceFinish) (cached : MeshReadings split anchors offsets)
    (position : Fin split.pieces.length)

/-- The literal mesh words are ordered subdivisions of the same original physical axis child.

Each full source-coordinate list equals the retained axis walk's ordered
step embedding at the original perpendicular endpoint. The same parent's
local segment proves that one transverse word is empty. Source labels,
orientations, repeated vertices and the two distinct outer route roles
remain unchanged; no root equality or signed face incidence is an input.
-/
theorem axis_subdivision (lower upper : Rational)
    (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1)
    (firstEq : (split.pieces[position.val]'position.isLt).firstPoint = parent.point lower)
    (lastEq : (split.pieces[position.val]'position.isLt).lastPoint = parent.point upper)
    (choice : Paths.CellChoice split position)
    (height : AxisPartition.Endpoint (Paths.partition split cached position choice).y
      (split.pieces[position.val]'position.isLt).firstPoint.im)
    (row : Paths.AxisPosition (Paths.partition split cached position choice).y height.interval)
    (width : AxisPartition.Endpoint (Paths.partition split cached position choice).x
      (split.pieces[position.val]'position.isLt).lastPoint.re)
    (column : Paths.AxisPosition (Paths.partition split cached position choice).x width.interval)
    (horizontal : AxisWalks.Walk (Paths.partition split cached position choice).x.intervals
      (split.pieces[position.val]'position.isLt).firstPoint.re
      (split.pieces[position.val]'position.isLt).lastPoint.re)
    (vertical : AxisWalks.Walk (Paths.partition split cached position choice).y.intervals
      (split.pieces[position.val]'position.isLt).firstPoint.im
      (split.pieces[position.val]'position.isLt).lastPoint.im)
    (horizontalSources : {value : List (SourceEdge
        ((MeshReadings.mesh split cached).triangles.map ModelTriangle.triangle).length) //
      value = (MeshReadings.mesh split cached).horizontalSources
        choice.val.index row.val.index height.high horizontal})
    (verticalSources : {value : List (SourceEdge
        ((MeshReadings.mesh split cached).triangles.map ModelTriangle.triangle).length) //
      value = (MeshReadings.mesh split cached).verticalSources
        choice.val.index column.val.index width.high vertical}) :
    horizontalSources.val.map (fun source =>
      ((MeshReadings.mesh split cached).surface.mesh.coordinate
          (source.project (MeshReadings.mesh split cached).surface.mesh.triangulation.faces).start,
        (MeshReadings.mesh split cached).surface.mesh.coordinate
          (source.project (MeshReadings.mesh split cached).surface.mesh.triangulation.faces).finish)) =
      horizontal.steps.map (fun pair =>
        ((⟨pair.1, (split.pieces[position.val]'position.isLt).firstPoint.im⟩ : Canonical),
          (⟨pair.2, (split.pieces[position.val]'position.isLt).firstPoint.im⟩ : Canonical))) ∧
    verticalSources.val.map (fun source =>
      ((MeshReadings.mesh split cached).surface.mesh.coordinate
          (source.project (MeshReadings.mesh split cached).surface.mesh.triangulation.faces).start,
        (MeshReadings.mesh split cached).surface.mesh.coordinate
          (source.project (MeshReadings.mesh split cached).surface.mesh.triangulation.faces).finish)) =
      vertical.steps.map (fun pair =>
        ((⟨(split.pieces[position.val]'position.isLt).lastPoint.re, pair.1⟩ : Canonical),
          (⟨(split.pieces[position.val]'position.isLt).lastPoint.re, pair.2⟩ : Canonical))) ∧
    (((split.pieces[position.val]'position.isLt).firstPoint.im =
        (split.pieces[position.val]'position.isLt).lastPoint.im ∧ verticalSources.val = []) ∨
      ((split.pieces[position.val]'position.isLt).firstPoint.re =
        (split.pieces[position.val]'position.isLt).lastPoint.re ∧ horizontalSources.val = [])) := by
  let piece := split.pieces[position.val]'position.isLt
  let mesh := MeshReadings.mesh split cached
  let part := Paths.partition split cached position choice
  let fixedHeight := if height.high then (part.y.intervals[row.val.index.val]'row.val.index.isLt).upper
    else (part.y.intervals[row.val.index.val]'row.val.index.isLt).lower
  let fixedWidth := if width.high then (part.x.intervals[column.val.index.val]'column.val.index.isLt).upper
    else (part.x.intervals[column.val.index.val]'column.val.index.isLt).lower
  have heightEq : fixedHeight = piece.firstPoint.im := Paths.endpoint_coordinate part.y height row
  have widthEq : fixedWidth = piece.lastPoint.re := Paths.endpoint_coordinate part.x width column
  have firstCoordinates := (congrArg (fun values => values.map (fun source =>
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start,
        mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish)))
      horizontalSources.property).trans
    (mesh.horizontalSources_coordinates choice.val.index row.val.index height.high horizontal)
  have lastCoordinates := (congrArg (fun values => values.map (fun source =>
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start,
        mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish)))
      verticalSources.property).trans
    (mesh.verticalSources_coordinates choice.val.index column.val.index width.high vertical)
  have horizontalEq := firstCoordinates.trans
    (congrArg (fun fixed : Rational => horizontal.steps.map
      (fun pair : Rational × Rational =>
        ((⟨pair.1, fixed⟩ : Canonical), (⟨pair.2, fixed⟩ : Canonical)))) heightEq)
  have verticalEq := lastCoordinates.trans
    (congrArg (fun fixed : Rational => vertical.steps.map
      (fun pair : Rational × Rational =>
        ((⟨fixed, pair.1⟩ : Canonical), (⟨fixed, pair.2⟩ : Canonical)))) widthEq)
  refine ⟨horizontalEq, verticalEq, ?_⟩
  rcases parent.point_axis lower upper lowerInside upperInside with horizontalLine | verticalLine
  · have same := (congrArg (fun point : Canonical => point.im) firstEq).trans
      (horizontalLine.trans (congrArg (fun point : Canonical => point.im) lastEq).symm)
    have empty := vertical.steps_nil_of_eq same
    have mapped := verticalEq.trans (congrArg (fun values : List (Rational × Rational) => values.map
      (fun pair : Rational × Rational =>
        ((⟨piece.lastPoint.re, pair.1⟩ : Canonical), (⟨piece.lastPoint.re, pair.2⟩ : Canonical)))) empty)
    refine Or.inl ⟨same, ?_⟩
    cases original : verticalSources.val with
    | nil => rfl
    | cons =>
        rewrite [original] at mapped
        cases mapped
  · have same := (congrArg (fun point : Canonical => point.re) firstEq).trans
      (verticalLine.trans (congrArg (fun point : Canonical => point.re) lastEq).symm)
    have empty := horizontal.steps_nil_of_eq same
    have mapped := horizontalEq.trans (congrArg (fun values : List (Rational × Rational) => values.map
      (fun pair : Rational × Rational =>
        ((⟨pair.1, piece.firstPoint.im⟩ : Canonical), (⟨pair.2, piece.firstPoint.im⟩ : Canonical)))) empty)
    refine Or.inr ⟨same, ?_⟩
    cases original : horizontalSources.val with
    | nil => rfl
    | cons =>
        rewrite [original] at mapped
        cases mapped

end Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge

end
