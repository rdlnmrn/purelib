module
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Geometry.Rectangle.SourceIntervals
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial

public section

/-! Derive the fixed coordinate and orientation of each retained rectangle side. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfaceOccurrence

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
open Purelib.Geometry.Rectangle
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Geometry.Rectangle.SourceIntervals (axisCoordinate)
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential
    genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

/-- Height of a horizontal side, or width coordinate of a vertical side. Reversing traversal changes neither this
coordinate nor its geometric owner. -/
@[expose] def
  sourceConstant
  (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential) : Coordinate :=
  let box :=
    (base.faces.regulars[occurrence.sideOccurrence.position.val]'occurrence.sideOccurrence.position.isLt).cell.box
  match occurrence.sideOccurrence.side with
  | .bottom => box.yLower
  | .top => box.yUpper
  | .left => box.xLower
  | .right => box.xUpper

open
  ExteriorProgram.SurfaceOccurrence

/-- Both original side endpoints retain the same fixed transverse source coordinate. -/
theorem
  source_constant_endpoints
  (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential) :
    SourceIntervals.axisCoordinate (!SurfaceOccurrence.sourceVertical occurrence) occurrence.start =
      sourceConstant
      occurrence ∧
      SourceIntervals.axisCoordinate (!SurfaceOccurrence.sourceVertical occurrence) occurrence.finish =
        sourceConstant
        occurrence := by
  have first := congrArg Prod.fst (SurfaceOccurrence.endpoints_eq occurrence)
  have last := congrArg Prod.snd (SurfaceOccurrence.endpoints_eq occurrence)
  change occurrence.start = (SurfaceOccurrence.sideEndpoints occurrence).1 at first
  change occurrence.finish = (SurfaceOccurrence.sideEndpoints occurrence).2 at last
  rw [first, last]
  cases side : occurrence.sideOccurrence.side <;> cases backward : occurrence.sideOccurrence.backward <;>
    simp only [SurfaceOccurrence.sourceVertical,
      sourceConstant,
      SurfaceOccurrence.sideEndpoints, side, backward,
      SourceIntervals.axisCoordinate, GridSide.kind, RectangleEdge.coordinates,
      Bool.not_false, Bool.not_true, if_pos (rfl : true = true), if_neg Bool.false_ne_true, -eq_self, -iff_self] <;>
        exact ⟨rfl, rfl⟩

/-- A horizontal occurrence's endpoints have the retained constant imaginary coordinate. -/
theorem
  source_horizontal_endpoints
  (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential)
    (axis : SurfaceOccurrence.sourceVertical occurrence = false) :
    occurrence.start.im =
      sourceConstant
      occurrence ∧ occurrence.finish.im =
      sourceConstant
      occurrence := by
  have fixed :=
    source_constant_endpoints
    occurrence
  simpa only [axis, Bool.not_false, SourceIntervals.axisCoordinate, if_pos (rfl : true = true), if_neg
    Bool.false_ne_true, -eq_self, -iff_self] using fixed

/-- A vertical occurrence's endpoints have the retained constant real coordinate. -/
theorem
  source_vertical_endpoints
  (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential)
    (axis : SurfaceOccurrence.sourceVertical occurrence = true) :
    occurrence.start.re =
      sourceConstant
      occurrence ∧ occurrence.finish.re =
      sourceConstant
      occurrence := by
  have fixed :=
    source_constant_endpoints
    occurrence
  simpa only [axis, Bool.not_true, SourceIntervals.axisCoordinate, if_pos (rfl : true = true), if_neg
    Bool.false_ne_true, -eq_self, -iff_self] using fixed

/-- The rectangle side determines the axis without an independent hypothesis. -/
theorem
  bottom_axis
  (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential)
    (side : occurrence.sideOccurrence.side = .bottom) :
      sourceVertical
      occurrence = false := by
  unfold SurfaceOccurrence.sourceVertical
  rw [side]

/-- The original top rectangle side selects the horizontal source axis. -/
theorem
  top_axis
  (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential)
    (side : occurrence.sideOccurrence.side = .top) :
      sourceVertical
      occurrence = false := by
  unfold SurfaceOccurrence.sourceVertical
  rw [side]

/-- The original left rectangle side selects the vertical source axis. -/
theorem
  left_axis
  (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential)
    (side : occurrence.sideOccurrence.side = .left) :
      sourceVertical
      occurrence = true := by
  unfold SurfaceOccurrence.sourceVertical
  rw [side]

/-- The original right rectangle side selects the vertical source axis. -/
theorem
  right_axis
  (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential)
    (side : occurrence.sideOccurrence.side = .right) :
      sourceVertical
      occurrence = true := by
  unfold SurfaceOccurrence.sourceVertical
  rw [side]

end SurfaceOccurrence
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
