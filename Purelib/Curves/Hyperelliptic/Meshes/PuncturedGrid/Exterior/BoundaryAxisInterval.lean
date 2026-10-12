module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularAxisParameterRange
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentRefinement
import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Tactic.Ring

public section

/-! The actual retained parent endpoints exclude a crossing of a physical
mesh interval. Its parent-parameter range is computed by two finite divisions. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisInterval

open Purelib.Curves

open Purelib.Geometry

open Purelib.Riemann

open Purelib.Riemann.Normalization

open Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts

open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrences : List
    (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential)}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}

/-- A bounded parent-parameter interval corresponding to the supplied physical axis interval.

The interval lies in the original unit parameter range and retains the actual parent endpoints in its axis
correspondence. -/
@[expose] def ParentInterval (parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)
    (vertical : Bool) (physical : Rectangle.Partition.PreparedAxisPartitions.Interval) :=
  { range : Rectangle.Partition.PreparedAxisPartitions.Interval //
    (0 ≤ range.lower ∧ range.upper ≤ 1) ∧ Rectangle.SourceIntervals.AxisCorrespondence vertical
      (parent.edge.point 0) (parent.edge.point 1) range physical }

/-- Transport a signed scalar parameter range to the original parent's physical axis interval.

The retained traversal orientation determines which endpoint identities and strict direction certify the correspondence.
-/
@[expose] def intervalOfRange (vertical forward : Bool) (physical : Rectangle.Partition.PreparedAxisPartitions.Interval)
    (ordered : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward
      (parent.edge.point 0) < Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical
      forward (parent.edge.point 1))
    (range : Integration.RectangularAxisParameterRange.AxisParameterRange
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward (parent.edge.point
      0))
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward (parent.edge.point
        1)) (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward physical)) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisInterval.ParentInterval parent vertical physical := open
      Purelib.Data.Rat in by
  refine ⟨range.range, range.within, ?_⟩
  cases forward with
  | true => exact Or.inl ⟨Fraction.Order.Arithmetic.sub_pos_direct ordered, range.first_eq, range.last_eq⟩
  | false =>
    have direction := Fraction.Order.Arithmetic.neg_lt_neg_direct ordered
    change -(-Rectangle.SourceIntervals.axisCoordinate vertical (parent.edge.point 1)) <
      -(-Rectangle.SourceIntervals.axisCoordinate vertical (parent.edge.point 0)) at direction
    rw [neg_neg, neg_neg] at direction
    have negative := Fraction.Order.Arithmetic.sub_lt_sub_right_direct direction
      (Rectangle.SourceIntervals.axisCoordinate vertical (parent.edge.point 0))
    rw [sub_self] at negative
    exact Or.inr ⟨negative, Fraction.Field.unneg_affine range.first_eq, Fraction.Field.unneg_affine range.last_eq⟩

open Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts in
/-- A midpoint crossing plus retained endpoints computes the entire interval
assignment. Both orientations use the same cached split and physical mesh. -/
@[expose] def LocatedParent.locateInterval (located :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation.LocatedParent occurrences parent)
    {columns rows : Nat} {geometry : Normalization.RectangularInverseModels.Geometry columns rows}
    {cuts : Paths.RectangularSegmentSplitting.GridCuts geometry} {box : Rational.Box}
    (mesh : Meshes.RectangularObservationMesh.ObservationMesh cuts box)
    (retained : ∀ point ∈ located.selected.split.points, point ∈ mesh.points)
    (vertical forward : Bool) (physical : Rectangle.Partition.PreparedAxisPartitions.Interval)
    (present : physical ∈ Rectangle.SourceIntervals.axisIntervals mesh vertical)
    (lower : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward
      (parent.edge.point 0) ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.blockMidpoint forward
      physical)
    (upper : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.blockMidpoint forward physical <
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward (parent.edge.point
      1)) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisInterval.ParentInterval parent vertical physical := open
      Purelib.Data.Rat in by
  have outside {point : Normalization.InverseRootPolynomial.Gaussian} (member : point ∈ mesh.points) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward point ≤
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward physical).lower ∨
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward physical).upper ≤
          Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward point := by
    have bound := Rectangle.SourceIntervals.axis_cut_outside mesh vertical present member
    cases forward with
    | true => exact bound
    | false =>
      exact bound.elim (fun h => Or.inr (Fraction.Order.Arithmetic.neg_le_neg_direct h)) (fun h => Or.inl
        (Fraction.Order.Arithmetic.neg_le_neg_direct h))
  let split := located.selected.split
  have first := Paths.RectangularSegmentRefinement.coordinate_point_mem split split.partition.lower_mem
  have last := Paths.RectangularSegmentRefinement.coordinate_point_mem split split.partition.upper_mem
  rw [Rectangle.Partition.PreparedSegmentCuts.point_zero] at first
  rw [Rectangle.Partition.PreparedSegmentCuts.point_one] at last
  have firstOutside := outside (retained _ first)
  have lastOutside := outside (retained _ last)
  have midpoint := Rectangle.Partition.PreparedSegmentCuts.midpoint_bounds
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward physical)
  have firstBound : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward
    (parent.edge.point 0) ≤ (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward
    physical).lower := by
    rcases firstOutside with bound | bound
    · exact bound
    · exact (not_lt_of_ge (bound.trans lower) midpoint.2).elim
  have lastBound : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward
    physical).upper ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward
    (parent.edge.point 1) := by
    rcases lastOutside with bound | bound
    · exact (not_lt_of_ge (bound.trans midpoint.1.le) upper).elim
    · exact bound
  let ordered := lower.trans_lt upper
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisInterval.intervalOfRange vertical forward physical
    ordered
    (Integration.RectangularAxisParameterRange.AxisParameterRange.build _ _ _ ordered ⟨firstBound, lastBound⟩)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisInterval
