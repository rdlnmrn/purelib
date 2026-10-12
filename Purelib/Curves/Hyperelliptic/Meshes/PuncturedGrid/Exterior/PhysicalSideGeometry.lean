module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

open Purelib.Geometry

open Purelib.Geometry.Rectangle

open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness

open Purelib.Riemann.Meshes.GridLiftedDualSteps

public section

/-! Physical rectangle bounds and fixed coordinates of the retained exterior side. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideGeometry
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  (sideEndpoints endpoints_eq sourceVertical sourceForward)
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Geometry.Rectangle.SourceIntervals (axisCoordinate)

/-- The original regular face box retained by this exterior side occurrence. -/
@[expose] def physicalBox (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential) :
  Rational.Box :=
  (base.faces.regulars[occurrence.sideOccurrence.position.val]'occurrence.sideOccurrence.position.isLt).cell.box

/-- The constant transverse coordinate of the original retained rectangle side. -/
@[expose] def fixedCoordinate (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential) : Coordinate
  :=
  match occurrence.sideOccurrence.side with
  | .bottom => (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideGeometry.physicalBox occurrence).yLower
  | .top => (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideGeometry.physicalBox occurrence).yUpper
  | .left => (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideGeometry.physicalBox occurrence).xLower
  | .right => (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideGeometry.physicalBox occurrence).xUpper

/-- The increasing physical side and the source-oriented occurrence have exactly the same endpoints, including the
retained backward bit. -/
theorem physical_bounds (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential) :
    (if (SurfaceOccurrence.sourceVertical occurrence) then
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideGeometry.physicalBox occurrence).yLower else
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideGeometry.physicalBox occurrence).xLower) =
      (if (SurfaceOccurrence.sourceForward occurrence) then SourceIntervals.axisCoordinate
        (SurfaceOccurrence.sourceVertical occurrence) occurrence.start
        else SourceIntervals.axisCoordinate (SurfaceOccurrence.sourceVertical occurrence) occurrence.finish) ∧
    (if (SurfaceOccurrence.sourceVertical occurrence) then
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideGeometry.physicalBox occurrence).yUpper else
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideGeometry.physicalBox occurrence).xUpper) =
      (if (SurfaceOccurrence.sourceForward occurrence) then SourceIntervals.axisCoordinate
        (SurfaceOccurrence.sourceVertical occurrence) occurrence.finish
        else SourceIntervals.axisCoordinate (SurfaceOccurrence.sourceVertical occurrence) occurrence.start) := by
  have first := congrArg Prod.fst (SurfaceOccurrence.endpoints_eq occurrence)
  have last := congrArg Prod.snd (SurfaceOccurrence.endpoints_eq occurrence)
  change occurrence.start = (SurfaceOccurrence.sideEndpoints occurrence).1 at first
  change occurrence.finish = (SurfaceOccurrence.sideEndpoints occurrence).2 at last
  rw [first, last]
  cases side : occurrence.sideOccurrence.side <;> cases backward : occurrence.sideOccurrence.backward <;>
    simp only [-eq_self, -iff_self, SurfaceOccurrence.sourceVertical, SurfaceOccurrence.sourceForward,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideGeometry.physicalBox,
      SurfaceOccurrence.sideEndpoints, side, backward,
      SourceIntervals.axisCoordinate, GridSide.kind, RectangleEdge.coordinates,
      Bool.not_false, Bool.not_true, if_neg (show (false : Bool) ≠ true by decide), if_pos (rfl : (true : Bool) = true)]
        <;> exact ⟨rfl, rfl⟩

/-- Both original occurrence endpoints have the retained side's constant transverse coordinate. -/
theorem fixed_coordinates (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential) :
    SourceIntervals.axisCoordinate (!(SurfaceOccurrence.sourceVertical occurrence)) occurrence.start =
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideGeometry.fixedCoordinate occurrence) ∧
    SourceIntervals.axisCoordinate (!(SurfaceOccurrence.sourceVertical occurrence)) occurrence.finish =
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideGeometry.fixedCoordinate occurrence) := by
  have first := congrArg Prod.fst (SurfaceOccurrence.endpoints_eq occurrence)
  have last := congrArg Prod.snd (SurfaceOccurrence.endpoints_eq occurrence)
  change occurrence.start = (SurfaceOccurrence.sideEndpoints occurrence).1 at first
  change occurrence.finish = (SurfaceOccurrence.sideEndpoints occurrence).2 at last
  rw [first, last]
  cases side : occurrence.sideOccurrence.side <;> cases backward : occurrence.sideOccurrence.backward <;>
    simp only [-eq_self, -iff_self, SurfaceOccurrence.sourceVertical,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideGeometry.fixedCoordinate,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideGeometry.physicalBox,
      SurfaceOccurrence.sideEndpoints, side, backward,
      SourceIntervals.axisCoordinate, GridSide.kind, RectangleEdge.coordinates,
      Bool.not_false, Bool.not_true, if_neg (show (false : Bool) ≠ true by decide), if_pos (rfl : (true : Bool) = true)]
        <;> exact ⟨rfl, rfl⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideGeometry
