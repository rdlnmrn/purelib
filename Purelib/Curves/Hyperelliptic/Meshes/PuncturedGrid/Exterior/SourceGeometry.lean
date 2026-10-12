module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.QuadrilateralDual
import Purelib.Topology.Polygon.Stokes

public section

/-! Read the original exterior endpoints from their retained oriented
rectangle side, without an independent geometric alignment assumption. -/
section

open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh
open Purelib.Geometry
open Purelib.Geometry.Rectangle
open Purelib.Geometry.Rectangle.Partition
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
open Purelib.Riemann.Meshes.GridLiftedDualSteps
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence AllSurfacePreparation)
open
  ExteriorProgram.SurfaceOccurrence
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters (signedAxis signedInterval)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies (LocatedSourceBlock)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfaceOccurrence

/-- The original rectangle side endpoints in the retained occurrence's traversal direction. -/
@[expose] def sideEndpoints (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential) :
  Data.Gaussian.Basic.Canonical × Gaussian :=
  let side := occurrence.sideOccurrence
  let endpoints := RectangleEdge.coordinates
    (base.faces.regulars[side.position.val]'side.position.isLt).cell.box side.side.kind
  if side.backward then (endpoints.2, endpoints.1) else endpoints

/-- The occurrence endpoints equal the original oriented rectangle side endpoints certified by its retained location. -/
theorem endpoints_eq (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential) :
    (occurrence.start, occurrence.finish) =
      (sideEndpoints
      occurrence) := by
  let side := occurrence.sideOccurrence
  let located := lifted.mesh.locateFace side.position side.sheet
  have coordinates := located.lifted.rectangleCoordinates.edge_coordinates side.side.kind
  have projected := LocatedFace.sideSource_project located side.side
  have sourceCoordinates :
      (lifted.vertices.coordinate (side.source.project lifted.mesh.triangulation.faces).start,
        lifted.vertices.coordinate (side.source.project lifted.mesh.triangulation.faces).finish) =

        (sideEndpoints
        occurrence) := by
    have forward := (congrArg (fun edge =>
      (lifted.vertices.coordinate edge.start, lifted.vertices.coordinate edge.finish)) projected).trans coordinates
    cases backward : side.backward with
    | false =>
      have backward' : occurrence.sideOccurrence.backward = false := backward
      simpa only [SideOccurrence.source, backward, if_neg (show (false : Bool) ≠ true from Bool.noConfusion), if_pos
        (show (true : Bool) = true from rfl),

          sideEndpoints,
          backward', LocatedFace.sideSource, side, located, -eq_self, -iff_self] using forward
    | true =>
      have backward' : occurrence.sideOccurrence.backward = true := backward
      have reversed := congrArg Prod.swap forward
      simpa only [SideOccurrence.source, backward, if_neg (show (false : Bool) ≠ true from Bool.noConfusion), if_pos
        (show (true : Bool) = true from rfl),
        sideEndpoints,
        backward', SourceEdge.project, Prod.swap,
        LocatedFace.sideSource, side, located, -eq_self, -iff_self] using reversed
  have source := occurrence.side_source
  have edge := (congrArg (fun source => source.project lifted.mesh.triangulation.faces) source).trans
    occurrence.placement.location.sourceEdge_project
  have endpoints := congrArg (fun edge =>
    (lifted.vertices.coordinate edge.start, lifted.vertices.coordinate edge.finish)) edge
  exact (congrArg₂ Prod.mk occurrence.placement.start_eq occurrence.placement.finish_eq).symm.trans
    (endpoints.symm.trans sourceCoordinates)

/-- Whether the original retained occurrence runs on a vertical rectangle side. -/
@[expose] def sourceVertical (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential) : Bool :=
  match occurrence.sideOccurrence.side with
  | .bottom | .top => false
  | .right | .left => true

/-- Whether the original side traversal increases its selected source coordinate. -/
@[expose] def sourceForward (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential) : Bool :=
  match occurrence.sideOccurrence.side with
  | .bottom | .right => !occurrence.sideOccurrence.backward
  | .top | .left => occurrence.sideOccurrence.backward

/-- The original proper face interval expressed in the retained source traversal orientation. -/
@[expose] def sourceSpan (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential) :
  PreparedAxisPartitions.Interval :=
  let face := base.faces.regulars[occurrence.sideOccurrence.position.val]'occurrence.sideOccurrence.position.isLt
  SourceBlockParameters.signedInterval
    (sourceForward
    occurrence)
    (if
      (sourceVertical
      occurrence) then ⟨face.cell.box.yLower, face.cell.box.yUpper, face.cell.box_proper.2⟩
      else ⟨face.cell.box.xLower, face.cell.box.xUpper, face.cell.box_proper.1⟩)

/-- The signed occurrence endpoints are exactly the lower and upper endpoints of its retained source span. -/
theorem source_span_endpoints (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential) :
    SourceBlockParameters.signedAxis
      (sourceVertical
      occurrence)
      (sourceForward
      occurrence) occurrence.start =
      (sourceSpan
      occurrence).lower ∧
      SourceBlockParameters.signedAxis
        (sourceVertical
        occurrence)
        (sourceForward
        occurrence) occurrence.finish =
        (sourceSpan
        occurrence).upper := by
  have first := congrArg Prod.fst
    (endpoints_eq
    occurrence)
  have last := congrArg Prod.snd
    (endpoints_eq
    occurrence)
  change occurrence.start =
    (sideEndpoints
    occurrence).1 at first
  change occurrence.finish =
    (sideEndpoints
    occurrence).2 at last
  rw [first, last]
  cases side : occurrence.sideOccurrence.side <;> cases backward : occurrence.sideOccurrence.backward <;>
    simp only
      [sourceVertical,
      sourceForward,
      sourceSpan,
      sideEndpoints,
      side, backward,
      SourceBlockParameters.signedAxis, SourceBlockParameters.signedInterval,
      SourceIntervals.axisCoordinate, GridSide.kind,
      RectangleEdge.coordinates, Bool.not_false, Bool.not_true,
      if_neg (show (false : Bool) ≠ true from Bool.noConfusion), if_pos (show (true : Bool) = true from rfl), -eq_self,
        -iff_self] <;> exact ⟨rfl, rfl⟩

end SurfaceOccurrence
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry

/-- Build the located source-block bank from the original occurrence position, sheet and traversal direction.

The retained endpoint certificates identify each block with its actual side interval and source owner. -/
@[expose] def sourceBank
    {other : Differentials.Basic.Differential genus} {occurrence : ExteriorProgram.SurfaceOccurrence regular domains
      differential}
    {target : InverseRootPolynomial.Coordinate} {minimum stage fine : Nat} {box otherBox : Rational.Box}
    {sample : Primitives.Sample cap differential stage box}
    {otherSample : Primitives.Sample cap other stage otherBox}
    {plan : PairedSourceReferences.PairedSourcePlan occurrence other target minimum}
    {prepared : ExteriorProgram.AllSurfacePreparation regular domains differential} {previous : RegularMeshes.CommonCuts
      domains}
    (selected : SourceCuts prepared previous) (member : occurrence ∈ prepared.occurrences)
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) → RegularMeshes.Preflights domains sheet} {meshTarget :
      InverseRootPolynomial.Coordinate}
    (request : TwoSheetBilinearRequest.TwoSheetRequest
      (fun sheet => RegularMeshes.build domains selected.cuts sheet coarseDepth) fixed meshTarget)
    (evaluated : PairedSourcePlan.ParentEvaluation plan sample otherSample fine) :=
  LocatedSourceBlock.buildBank selected member request occurrence.sideOccurrence.sheet
    occurrence.sideOccurrence.position
    evaluated
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.sourceVertical
      occurrence)
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.sourceForward
      occurrence)
    (by
      have endpoint :=
        (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.source_span_endpoints
        occurrence).1
      exact endpoint.le)
    (by
      have endpoint :=
        (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.source_span_endpoints
        occurrence).2
      exact endpoint.symm.le)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry

end
