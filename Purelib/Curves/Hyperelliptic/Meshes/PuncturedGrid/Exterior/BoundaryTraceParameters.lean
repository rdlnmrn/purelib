module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisInterval
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.PreparedSegmentBoundaryGeometry
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation
import Purelib.Riemann.Paths.RectangularTraceParameterReadings
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring

public section

/-! Transport the physical trace to its selected closed-bank parent without
replacing any owner, primitive value, or cached area sample. -/
section

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
open Purelib.Data.Rat
open Purelib.Geometry.Rectangle
open Purelib.Geometry.Rectangle.Partition
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
open Purelib.Riemann.Integration
open Purelib.Riemann.Meshes.GridLiftedDualSteps
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.RectangularTraceParameterReadings

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Geometry.Rectangle.SourceIntervals (axisCoordinate)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters (signedAxis)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisInterval (ParentInterval)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation (LocatedParent)
open Purelib.Riemann.Paths.RectangularTraceParameterReadings (ParentParameters)
open Purelib.Riemann.Integration.RectangularPairedPointBanks (Trace)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrences : List
    (ExteriorProgram.SurfaceOccurrence
    regular domains differential)}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters

/-- The original parameter interval endpoint first encountered in the selected traversal direction. -/
@[expose] def firstParameter (forward : Bool) (range : PreparedAxisPartitions.Interval) : Coordinate :=
  if forward then range.lower else range.upper

/-- The original parameter interval endpoint last encountered in the selected traversal direction. -/
@[expose] def lastParameter (forward : Bool) (range : PreparedAxisPartitions.Interval) : Coordinate :=
  if forward then range.upper else range.lower

/-- The selected coordinate of the retained parent is affine in its original parameter. -/
private theorem parent_axis (vertical : Bool) (parameter : InverseRootPolynomial.Coordinate) :
    SourceIntervals.axisCoordinate vertical (parent.edge.point parameter) = SourceIntervals.axisCoordinate vertical
      (parent.edge.point 0) +
      parameter * (SourceIntervals.axisCoordinate vertical (parent.edge.point 1) - SourceIntervals.axisCoordinate
        vertical (parent.edge.point 0)) := by
  rw [PreparedParentSplitting.prepared_point_eq]
  exact SourceIntervals.axis_affine vertical _ _ parameter

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisInterval.ParentInterval

/-- The direction-selected parent interval endpoints read the original physical interval endpoints. -/
theorem endpoint_axes {vertical forward : Bool} {physical : PreparedAxisPartitions.Interval}
    (range : BoundaryAxisInterval.ParentInterval parent vertical physical)
    (ordered : SourceBlockParameters.signedAxis vertical forward (parent.edge.point 0) <
      SourceBlockParameters.signedAxis vertical forward (parent.edge.point 1)) :
    SourceIntervals.axisCoordinate vertical (parent.edge.point
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.firstParameter forward range.val)) =
      physical.lower ∧
      SourceIntervals.axisCoordinate vertical (parent.edge.point
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.lastParameter forward range.val)) =
        physical.upper := by
  cases forward with
  | true =>
    change SourceIntervals.axisCoordinate vertical (parent.edge.point range.val.lower) = physical.lower ∧
      SourceIntervals.axisCoordinate vertical (parent.edge.point range.val.upper) = physical.upper
    rcases range.property.2 with ⟨positive, first, last⟩ | ⟨negative, _, _⟩
    · exact ⟨(Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.parent_axis vertical _).trans
        first, (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.parent_axis vertical _).trans
        last⟩
    · exact (not_lt_of_ge (Fraction.Order.Arithmetic.sub_pos_direct ordered).le negative).elim
  | false =>
    change SourceIntervals.axisCoordinate vertical (parent.edge.point range.val.upper) = physical.lower ∧
      SourceIntervals.axisCoordinate vertical (parent.edge.point range.val.lower) = physical.upper
    have direction := Fraction.Order.Arithmetic.neg_lt_neg_direct ordered
    change -(-SourceIntervals.axisCoordinate vertical (parent.edge.point 1)) < -(-SourceIntervals.axisCoordinate
      vertical (parent.edge.point 0)) at direction
    rw [neg_neg, neg_neg] at direction
    rcases range.property.2 with ⟨positive, _, _⟩ | ⟨negative, first, last⟩
    · exact (not_lt_of_ge (Fraction.Order.Boundary.sub_nonpositive_iff.mpr direction.le) positive).elim
    · exact ⟨(Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.parent_axis vertical _).trans
        last, (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.parent_axis vertical _).trans
        first⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisInterval.ParentInterval

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters

/-- A strictly ordered retained parent has unique parameters for equal selected-axis coordinates. -/
theorem parent_parameter_eq {vertical forward : Bool} {first last : InverseRootPolynomial.Coordinate}
    (ordered : SourceBlockParameters.signedAxis vertical forward (parent.edge.point 0) <
      SourceBlockParameters.signedAxis vertical forward (parent.edge.point 1))
    (equal : SourceIntervals.axisCoordinate vertical (parent.edge.point first) = SourceIntervals.axisCoordinate vertical
      (parent.edge.point last)) :
    first = last := by
  have nonzero : SourceIntervals.axisCoordinate vertical (parent.edge.point 1) - SourceIntervals.axisCoordinate vertical
    (parent.edge.point 0) ≠ 0 := by
    cases forward with
    | true => exact (Fraction.Order.Arithmetic.sub_pos_direct ordered).ne'
    | false =>
      have direction := Fraction.Order.Arithmetic.neg_lt_neg_direct ordered
      change -(-SourceIntervals.axisCoordinate vertical (parent.edge.point 1)) < -(-SourceIntervals.axisCoordinate
        vertical (parent.edge.point 0)) at direction
      rw [neg_neg, neg_neg] at direction
      have negative := Fraction.Order.Arithmetic.sub_lt_sub_right_direct direction (SourceIntervals.axisCoordinate
        vertical (parent.edge.point 0))
      rw [sub_self] at negative
      exact negative.ne
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.parent_axis vertical first,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.parent_axis vertical last] at equal
  apply Fraction.Field.mul_right_cancel_of_ne nonzero
  have cancelled := congrArg (fun value : Coordinate => value -
    SourceIntervals.axisCoordinate vertical (parent.edge.point 0)) equal
  calc
    _ = (SourceIntervals.axisCoordinate vertical (parent.edge.point 0) + first *
        (SourceIntervals.axisCoordinate vertical (parent.edge.point 1) -
          SourceIntervals.axisCoordinate vertical (parent.edge.point 0))) -
        SourceIntervals.axisCoordinate vertical (parent.edge.point 0) := by ring1
    _ = _ := cancelled
    _ = _ := by ring1

/-- A strictly ordered retained parent has unique parameters for equal signed-axis coordinates. -/
theorem parent_signed_parameter_eq {vertical forward : Bool} {first last : InverseRootPolynomial.Coordinate}
    (ordered : SourceBlockParameters.signedAxis vertical forward (parent.edge.point 0) <
      SourceBlockParameters.signedAxis vertical forward (parent.edge.point 1))
    (equal : SourceBlockParameters.signedAxis vertical forward (parent.edge.point first) =
      SourceBlockParameters.signedAxis vertical forward (parent.edge.point last)) :
    first = last := by
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.parent_parameter_eq ordered
  cases forward with
  | true => exact equal
  | false =>
    have result := congrArg Neg.neg equal
    simpa only [SourceBlockParameters.signedAxis, if_neg (show (false : Bool) ≠ true from Bool.noConfusion), if_pos
      (show (true : Bool) = true from rfl), neg_neg, -eq_self, -iff_self] using result

/-- Every parameter in the unit interval lies between the original parent's signed endpoint coordinates. -/
theorem parent_signed_bounds {vertical forward : Bool} {parameter : InverseRootPolynomial.Coordinate}
    (ordered : SourceBlockParameters.signedAxis vertical forward (parent.edge.point 0) <
      SourceBlockParameters.signedAxis vertical forward (parent.edge.point 1))
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    SourceBlockParameters.signedAxis vertical forward (parent.edge.point 0) ≤ SourceBlockParameters.signedAxis vertical
      forward (parent.edge.point parameter) ∧
      SourceBlockParameters.signedAxis vertical forward (parent.edge.point parameter) ≤ SourceBlockParameters.signedAxis
        vertical forward (parent.edge.point 1) := by
  have affine : SourceBlockParameters.signedAxis vertical forward (parent.edge.point parameter) =
      SourceBlockParameters.signedAxis vertical forward (parent.edge.point 0) + parameter *
        (SourceBlockParameters.signedAxis vertical forward (parent.edge.point 1) - SourceBlockParameters.signedAxis
          vertical forward (parent.edge.point 0)) := by
    cases forward with
    | true =>
      exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.parent_axis vertical
        parameter
    | false =>
      change -SourceIntervals.axisCoordinate vertical (parent.edge.point parameter) = _
      rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.parent_axis vertical parameter]
      change -(_ + parameter * (_ - _)) = -_ + parameter * (-_ - -_)
      ring1
  have positive := (Fraction.Order.Arithmetic.sub_pos_direct ordered).le
  have lower := le_add_of_nonneg_right (a := SourceBlockParameters.signedAxis vertical forward (parent.edge.point 0))
    (Fraction.Order.Arithmetic.mul_nonneg_direct inside.1 positive)
  have upper := Fraction.Order.Arithmetic.add_le_add_direct (le_refl (SourceBlockParameters.signedAxis vertical forward
    (parent.edge.point 0)))
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct inside.2 positive)
  exact ⟨lower.trans_eq affine.symm, affine.trans_le (upper.trans_eq (by ring1))⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfaceOccurrence

/-- The original occurrence's fixed transverse coordinate read at its retained start. -/
@[expose] def sourceAcross (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential) : Coordinate :=
  SourceIntervals.axisCoordinate (!occurrence.sourceVertical) occurrence.start

end SurfaceOccurrence
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

open
  ExteriorProgram.SurfaceOccurrence
  (sourceAcross)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters

/-- The original occurrence finish retains the same fixed transverse coordinate as its start. -/
private theorem source_across (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential) :
    SourceIntervals.axisCoordinate (!occurrence.sourceVertical) occurrence.finish =
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.sourceAcross
      occurrence := by
  have first := congrArg Prod.fst occurrence.endpoints_eq
  have last := congrArg Prod.snd occurrence.endpoints_eq
  change occurrence.start = occurrence.sideEndpoints.1 at first
  change occurrence.finish = occurrence.sideEndpoints.2 at last
  unfold
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.sourceAcross
  rw [first, last]
  cases side : occurrence.sideOccurrence.side <;> cases backward : occurrence.sideOccurrence.backward <;>
    simp only [SurfaceOccurrence.sourceVertical, SurfaceOccurrence.sideEndpoints, side, backward,
      RectangleEdge.coordinates, GridSide.kind, Bool.not_false, Bool.not_true,
      SourceIntervals.axisCoordinate, if_neg (show (false : Bool) ≠ true from Bool.noConfusion), if_pos (show (true :
        Bool) = true from rfl), -eq_self, -iff_self] <;> rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation.LocatedParent

/-- Every point of the retained located parent has its original occurrence's fixed transverse coordinate. -/
theorem across (located : BoundaryParentLocation.LocatedParent occurrences parent) (parameter :
  InverseRootPolynomial.Coordinate) :
    SourceIntervals.axisCoordinate (!located.occurrence.sourceVertical) (parent.edge.point parameter) =

        SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.sourceAcross
        located.occurrence := by
  have endpoints := PreparedSegmentBoundaryGeometry.segment_parent_endpoints located.occurrence.compared.entered.cache
    located.parent_mem
  have along (fraction : InverseRootPolynomial.Coordinate) :
      SourceIntervals.axisCoordinate (!located.occurrence.sourceVertical) (located.occurrence.segment.pointAt fraction)
        =

          SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.sourceAcross
          located.occurrence := by
    change SourceIntervals.axisCoordinate (!located.occurrence.sourceVertical)
      (PreparedSegmentCuts.point located.occurrence.start located.occurrence.finish fraction) = _
    rw [SourceIntervals.axis_affine,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.source_across]
    change
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.sourceAcross
      located.occurrence + fraction *
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.sourceAcross
      located.occurrence -
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.sourceAcross
      located.occurrence) = _
    ring1
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.parent_axis, endpoints.1, endpoints.2,
    along, along]
  ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation.LocatedParent

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation.LocatedParent

/-- Full point transport uses the selected occurrence's own fixed side coordinate. The input trace and its readings are
retained unchanged. -/
@[expose] def traceParameters (located : BoundaryParentLocation.LocatedParent occurrences parent)
    {physical : PreparedAxisPartitions.Interval}
    (range : BoundaryAxisInterval.ParentInterval parent located.occurrence.sourceVertical physical)
    (ordered : SourceBlockParameters.signedAxis located.occurrence.sourceVertical located.occurrence.sourceForward
      (parent.edge.point 0) <
      SourceBlockParameters.signedAxis located.occurrence.sourceVertical located.occurrence.sourceForward
        (parent.edge.point 1))
    {lc lr rc rr count : Nat} {lg : RectangularInverseModels.Geometry lc lr} {rg : RectangularInverseModels.Geometry rc
      rr}
    {piece : RectangularPairedSegments.PairedSegmentPiece lg rg} (trace : RectangularPairedPointBanks.Trace piece count)
    (firstAlong : SourceIntervals.axisCoordinate located.occurrence.sourceVertical piece.first = physical.lower)
    (lastAlong : SourceIntervals.axisCoordinate located.occurrence.sourceVertical piece.last = physical.upper)
    (firstAcross : SourceIntervals.axisCoordinate (!located.occurrence.sourceVertical) piece.first =
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.sourceAcross
      located.occurrence)
    (lastAcross : SourceIntervals.axisCoordinate (!located.occurrence.sourceVertical) piece.last =
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.sourceAcross
      located.occurrence) :
    RectangularTraceParameterReadings.ParentParameters trace parent
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.firstParameter
      located.occurrence.sourceForward range.val)
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.lastParameter
        located.occurrence.sourceForward range.val) :=
  ParentParameters.build trace _ _ _
    (Geometry.Rectangle.SourceIntervals.point_from_axes located.occurrence.sourceVertical
      (firstAlong.trans
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisInterval.ParentInterval.endpoint_axes range
        ordered).1.symm) (firstAcross.trans
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation.LocatedParent.across located
        _).symm))
    (Geometry.Rectangle.SourceIntervals.point_from_axes located.occurrence.sourceVertical
      (lastAlong.trans
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisInterval.ParentInterval.endpoint_axes range
        ordered).2.symm) (lastAcross.trans
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation.LocatedParent.across located
        _).symm))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation.LocatedParent

variable {lc lr rc rr count : Nat} {lg : Purelib.Riemann.Normalization.RectangularInverseModels.Geometry lc lr} {rg :
  Purelib.Riemann.Normalization.RectangularInverseModels.Geometry rc rr}
  {piece : Purelib.Riemann.Paths.RectangularPairedSegments.PairedSegmentPiece lg rg} {trace :
    Purelib.Riemann.Integration.RectangularPairedPointBanks.Trace piece count}
  {range : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval} {forward : Bool}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters

/-- Every transported trace parameter remains inside the original retained parent interval. -/
theorem trace_inside (transport : RectangularTraceParameterReadings.ParentParameters trace parent
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.firstParameter forward range)
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.lastParameter forward range))
    (vertex : Fin (count + 1)) : range.lower ≤ transport.parameters vertex ∧ transport.parameters vertex ≤ range.upper
      := by
  cases forward with
  | true => exact transport.inside range.ordered.le vertex
  | false => exact transport.inside_reverse range.ordered.le vertex

/-- The original trace parameter order transports to increasing or decreasing parent order according to the retained
direction. -/
theorem trace_ordered (transport : RectangularTraceParameterReadings.ParentParameters trace parent
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.firstParameter forward range)
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.lastParameter forward range))
    (increasing : ∀ edge : Fin count, trace.parameters edge.castSucc ≤ trace.parameters edge.succ)
    (edge : Fin count) : if forward then transport.parameters edge.castSucc ≤ transport.parameters edge.succ
      else transport.parameters edge.succ ≤ transport.parameters edge.castSucc := by
  cases forward with
  | true => exact transport.ordered range.ordered.le increasing edge
  | false => exact transport.ordered_reverse range.ordered.le increasing edge

/-- The oriented transported trace length is nonnegative and at most one when its original parent interval lies within
the unit interval. -/
theorem trace_length_bound (transport : RectangularTraceParameterReadings.ParentParameters trace parent
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.firstParameter forward range)
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.lastParameter forward range))
    (within : 0 ≤ range.lower ∧ range.upper ≤ 1) :
    let first := transport.parameters 0
    let last := transport.parameters (Fin.last count)
    0 ≤ (if forward then last - first else first - last) ∧
      (if forward then last - first else first - last) ≤ 1 := by
  have inside := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.trace_inside transport 0
  rw [transport.last_parameter]
  cases forward with
  | true =>
    change 0 ≤ range.upper - transport.parameters 0 ∧ range.upper - transport.parameters 0 ≤ 1
    exact ⟨Fraction.Order.Arithmetic.sub_nonneg_direct inside.2,
      (Fraction.Order.Arithmetic.sub_le_sub_direct within.2 (within.1.trans inside.1)).trans_eq (by ring1)⟩
  | false =>
    change 0 ≤ transport.parameters 0 - range.lower ∧ transport.parameters 0 - range.lower ≤ 1
    exact ⟨Fraction.Order.Arithmetic.sub_nonneg_direct inside.1,
      (Fraction.Order.Arithmetic.sub_le_sub_direct (inside.2.trans within.2) within.1).trans_eq (by ring1)⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters

end
