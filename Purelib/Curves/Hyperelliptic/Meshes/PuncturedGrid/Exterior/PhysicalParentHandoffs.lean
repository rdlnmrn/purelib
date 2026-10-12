module
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockPoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockJunctions
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

public section

/-! Parent transitions derived from adjacent physical intervals. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalParentHandoffs

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
open Purelib.Geometry.Rectangle
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockJunctions.SourceBlockParameters
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder (indexed_parents_separated
  indexed_parents_no_skip)
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
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential other :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum
    stage fine : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence
    other target minimum}

namespace SourceBlockParameters
variable {evaluated :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation
  plan sample otherSample fine} {vertical : Bool}
  {beforePhysical afterPhysical : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}

/-- Consecutive forward physical blocks either remain in one retained parent or cross exactly one parent boundary, with
both endpoint parameters certified. -/
theorem consecutive_parent_handoff
    (before : SourceBlockParameters evaluated vertical true beforePhysical)
    (after : SourceBlockParameters evaluated vertical true afterPhysical)
    (ordered : ∀ parent ∈ occurrence.compared.entered.cache.parents,
      SourceIntervals.axisCoordinate vertical (parent.edge.point 0) < SourceIntervals.axisCoordinate vertical
        (parent.edge.point 1))
    (consecutive : afterPhysical.lower = beforePhysical.upper) :
    (after.index = before.index ∧ (SourceBlockParameters.firstParameter after) = (SourceBlockParameters.lastParameter
      before)) ∨
      (after.index.val = before.index.val + 1 ∧
        (SourceBlockParameters.lastParameter before) = 1 ∧ (SourceBlockParameters.firstParameter after) = 0) := by
  have monotone : before.index.val ≤ after.index.val := by
    apply Nat.le_of_not_gt
    intro backwards
    have separated := IndexedParentOrder.indexed_parents_separated evaluated (SourceIntervals.axisCoordinate vertical)
      (fun parent member => (ordered parent member).le) after.index before.index backwards
    have physical : beforePhysical.lower < afterPhysical.upper :=
      beforePhysical.ordered.trans_le (consecutive.symm.trans_le afterPhysical.ordered.le)
    have positive := before.physical_inside.1.trans_lt (physical.trans_le after.physical_inside.2)
    exact (not_lt_of_ge separated) positive
  rcases Nat.eq_or_lt_of_le monotone with same | next
  · have equal : after.index = before.index := Fin.ext same.symm
    exact Or.inl ⟨equal, before.same_parent_parameters after equal consecutive⟩
  · have separated := IndexedParentOrder.indexed_parents_separated evaluated (SourceIntervals.axisCoordinate vertical)
      (fun parent member => (ordered parent member).le) before.index after.index next
    have endpoints := before.handoff_of_separated after consecutive separated
    have joint := (SourceBlockParameters.last_axis before).trans (consecutive.symm.trans after.first_axis.symm)
    change (SourceBlockParameters.lastParameter before) = 1 ∧ (SourceBlockParameters.firstParameter after) = 0
      at endpoints
    rw [endpoints.1, endpoints.2] at joint
    exact Or.inr ⟨indexed_parents_no_skip evaluated (SourceIntervals.axisCoordinate vertical) ordered
      before.index after.index next joint, endpoints⟩

/-- The actual occurrence supplies parent monotonicity; only its physical orientation and the shared interval endpoint
are needed. -/
theorem occurrence_parent_handoff
    (before : SourceBlockParameters evaluated occurrence.sourceVertical true beforePhysical)
    (after : SourceBlockParameters evaluated occurrence.sourceVertical true afterPhysical)
    (forward : occurrence.sourceForward = true)
    (consecutive : afterPhysical.lower = beforePhysical.upper) :
    (after.index = before.index ∧ (SourceBlockParameters.firstParameter after) = (SourceBlockParameters.lastParameter
      before)) ∨
      (after.index.val = before.index.val + 1 ∧
        (SourceBlockParameters.lastParameter before) = 1 ∧ (SourceBlockParameters.firstParameter after) = 0) := by
  apply
    consecutive_parent_handoff
    before after _ consecutive
  intro parent member
  have ordered := BoundaryAxisLocation.source_parent_ordered occurrence member
  simpa only [-eq_self, -iff_self, forward, SourceBlockParameters.signedAxis, if_neg (show (false : Bool) ≠ true by
    decide), if_pos (rfl : (true : Bool) = true)] using ordered

end SourceBlockParameters

namespace AxisSourceBank
open Purelib.Riemann.Normalization.RectangularInverseModels
  Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh
variable {evaluated :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation
  plan sample otherSample fine}
  {columns rows : Nat} {geometry : Purelib.Riemann.Normalization.RectangularInverseModels.Geometry columns rows} {cuts :
    Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts geometry}
  {meshBox : Purelib.Geometry.Rational.Box} {mesh :
    Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh cuts meshBox}

/-- Adjacent entries of the cached physical source bank carry the exact parent transition and parameter join, without
caller-supplied chain evidence. -/
theorem consecutive_handoff
    (bank : FragmentFamilies.AxisSourceBank evaluated mesh occurrence.sourceVertical true)
    (forward : occurrence.sourceForward = true)
    (before after : Fin (SourceIntervals.axisIntervals mesh occurrence.sourceVertical).length)
    (next : after.val = before.val + 1) :
    let left := (bank.get before).block
    let right := (bank.get after).block
    (right.index = left.index ∧ (SourceBlockParameters.firstParameter right) = (SourceBlockParameters.lastParameter
      left)) ∨
      (right.index.val = left.index.val + 1 ∧ (SourceBlockParameters.lastParameter left) = 1 ∧
        (SourceBlockParameters.firstParameter right) = 0) :=

    SourceBlockParameters.occurrence_parent_handoff
    (bank.get before).block (bank.get after).block forward
    (SourceIntervals.axis_consecutive mesh occurrence.sourceVertical before after next)

end AxisSourceBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalParentHandoffs
