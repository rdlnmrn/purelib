module
import Purelib.Data.List.Map
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Riemann.Integration.PreparedParentAxisLocation
import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalParentHandoffs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockPoints
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockJunctions

public section

/-! Reversed physical sides traverse the retained source parents backwards. -/
section

open Purelib.Data.List

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Data.Rat
open Purelib.Geometry.Rectangle
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedParentAxisLocation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters (signedAxis)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockJunctions.SourceBlockParameters
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder (indexed_parents_separated
  indexed_parents_no_skip)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder (indexed_parent_at_start
  indexed_parent_at_finish)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits (indexedEntry)
open Purelib.Geometry.Rectangle.SourceIntervals (axisCoordinate)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence SurfacePreparation)
open
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
open
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison
open Purelib.Riemann.Normalization
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies (AxisSourceBank)
open Purelib.Data.Gaussian.Basic.Canonical
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Coordinate} {minimum
    stage fine : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : PairedSourcePlan occurrence
    other target minimum}

open Purelib.Data.Rat.Fraction.Compatibility
variable {evaluated :
  ParentEvaluation
  plan sample otherSample fine}
  {beforePhysical afterPhysical : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseParentHandoffs.SourceBlockParameters

/-- Physical order runs backwards through the retained parents on a reversed occurrence. A crossing uses parameters zero
and one, with no skipped parent. -/
theorem reverse_occurrence_parent_handoff
    (before : SourceBlockParameters evaluated occurrence.sourceVertical false beforePhysical)
    (after : SourceBlockParameters evaluated occurrence.sourceVertical false afterPhysical)
    (backward : occurrence.sourceForward = false)
    (consecutive : afterPhysical.lower = beforePhysical.upper) :
    (after.index = before.index ∧ after.firstParameter = before.lastParameter) ∨
      (before.index.val = after.index.val + 1 ∧
        before.lastParameter = 0 ∧ after.firstParameter = 1) := by
  let project := SourceBlockParameters.signedAxis occurrence.sourceVertical false
  have ordered (parent) (member : parent ∈ occurrence.compared.entered.cache.parents) :
      project (parent.edge.point 0) < project (parent.edge.point 1) := by
    have bound := BoundaryAxisLocation.source_parent_ordered occurrence member
    simpa only [backward, -eq_self, -iff_self] using bound
  have monotone : after.index.val ≤ before.index.val := by
    apply Nat.le_of_not_gt
    intro backwards
    have separated := IndexedParentOrder.indexed_parents_separated evaluated project
      (fun parent member => (ordered parent member).le) before.index after.index backwards
    have opposite := Fraction.Order.Arithmetic.neg_le_neg_direct separated
    simp only [project, SourceBlockParameters.signedAxis, if_neg (show (false : Bool) ≠ true from Bool.noConfusion),
      neg_neg, -eq_self, -iff_self] at opposite
    have physical : beforePhysical.lower < afterPhysical.upper :=
      beforePhysical.ordered.trans_le (consecutive.symm.trans_le afterPhysical.ordered.le)
    have positive := before.physical_inside.1.trans_lt (physical.trans_le after.physical_inside.2)
    exact (not_lt_of_ge opposite) positive
  rcases Nat.eq_or_lt_of_le monotone with same | next
  · have equal : after.index = before.index := Fin.ext same
    exact Or.inl ⟨equal, before.same_parent_parameters after equal consecutive⟩
  · have separated := IndexedParentOrder.indexed_parents_separated evaluated project
      (fun parent member => (ordered parent member).le) after.index before.index next
    have opposite := Fraction.Order.Arithmetic.neg_le_neg_direct separated
    simp only [project, SourceBlockParameters.signedAxis, if_neg (show (false : Bool) ≠ true from Bool.noConfusion),
      neg_neg, -eq_self, -iff_self] at opposite
    have endpoints := before.handoff_of_separated after consecutive opposite
    change before.lastParameter = 0 ∧ after.firstParameter = 1 at endpoints
    have joint := before.last_axis.trans (consecutive.symm.trans after.first_axis.symm)
    rw [endpoints.1, endpoints.2] at joint
    have signedJoint := congrArg (fun value : InverseRootPolynomial.Coordinate => -value) joint.symm
    exact Or.inr ⟨indexed_parents_no_skip evaluated project ordered
      after.index before.index next signedJoint, endpoints⟩

/-- The original reversed occurrence endpoints bound the selected source parent's endpoints in the corresponding
physical-coordinate order. -/
private theorem reverse_parent_bounds {physical : PreparedAxisPartitions.Interval}
    (block : SourceBlockParameters evaluated occurrence.sourceVertical false physical)
    (backward : occurrence.sourceForward = false) :
    SourceIntervals.axisCoordinate occurrence.sourceVertical ((IndexedSourceSplits.indexedEntry evaluated
      block.index).plan.parent.edge.point 0) ≤
      SourceIntervals.axisCoordinate occurrence.sourceVertical occurrence.start ∧
    SourceIntervals.axisCoordinate occurrence.sourceVertical occurrence.finish ≤
      SourceIntervals.axisCoordinate occurrence.sourceVertical ((IndexedSourceSplits.indexedEntry evaluated
        block.index).plan.parent.edge.point 1) := by
  have lengths := congrArg List.length
    (Evaluation.source_parents evaluated)
  rw [Map.length_map] at lengths
  let index : Fin occurrence.compared.entered.cache.parents.length :=
    ⟨block.index.val, block.index.isLt.trans_eq lengths⟩
  have read := PreparedParentSplitSelection.mapped_read evaluated.retained
    (fun entry => entry.plan.parent)
    (Evaluation.source_parents evaluated)
    block.index index.isLt
  have bounds := ParentCache.parent_bounds
    occurrence.compared.entered.cache
    (SourceBlockParameters.signedAxis occurrence.sourceVertical false) (fun parent member => by
      have ordered := BoundaryAxisLocation.source_parent_ordered occurrence member
      simpa only [backward, -eq_self, -iff_self] using ordered.le) index
  rw [read] at bounds
  have first := Fraction.Order.Arithmetic.neg_le_neg_direct bounds.1
  have last := Fraction.Order.Arithmetic.neg_le_neg_direct bounds.2
  simp only [SourceBlockParameters.signedAxis, if_neg (show (false : Bool) ≠ true from Bool.noConfusion), neg_neg,
    -eq_self, -iff_self] at first last
  exact ⟨first, last⟩

/-- The low physical endpoint of a reversed occurrence starts at the last source parent and parameter one. -/
theorem reverse_at_physical_start {physical : PreparedAxisPartitions.Interval}
    (block : SourceBlockParameters evaluated occurrence.sourceVertical false physical)
    (backward : occurrence.sourceForward = false)
    (start : physical.lower = SourceIntervals.axisCoordinate occurrence.sourceVertical occurrence.finish) :
    block.index.val + 1 = evaluated.retained.length ∧ block.firstParameter = 1 := by
  have endpoint := _root_.le_antisymm (block.physical_inside.1.trans_eq start)

      (reverse_parent_bounds
      block backward).2
  refine ⟨indexed_parent_at_finish evaluated (SourceBlockParameters.signedAxis occurrence.sourceVertical false)
    (fun parent member => ?_) block.index (congrArg (fun value : InverseRootPolynomial.Coordinate => -value) endpoint),
    block.first_parameter_of_parent_endpoint (start.trans endpoint.symm)⟩
  have ordered := BoundaryAxisLocation.source_parent_ordered occurrence member
  simpa only [backward, -eq_self, -iff_self] using ordered

/-- The high physical endpoint of a reversed occurrence ends at source parent zero and parameter zero. -/
theorem reverse_at_physical_finish {physical : PreparedAxisPartitions.Interval}
    (block : SourceBlockParameters evaluated occurrence.sourceVertical false physical)
    (backward : occurrence.sourceForward = false)
    (finish : physical.upper = SourceIntervals.axisCoordinate occurrence.sourceVertical occurrence.start) :
    block.index.val = 0 ∧ block.lastParameter = 0 := by
  have endpoint := _root_.le_antisymm
    (reverse_parent_bounds
    block backward).1
    (finish.symm.trans_le block.physical_inside.2)
  refine ⟨indexed_parent_at_start evaluated (SourceBlockParameters.signedAxis occurrence.sourceVertical false)
    (fun parent member => ?_) block.index (congrArg (fun value : InverseRootPolynomial.Coordinate => -value) endpoint),
    block.last_parameter_of_parent_endpoint (finish.trans endpoint.symm)⟩
  have ordered := BoundaryAxisLocation.source_parent_ordered occurrence member
  simpa only [backward, -eq_self, -iff_self] using ordered

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseParentHandoffs.SourceBlockParameters

end
