module
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Riemann.Integration.PreparedParentAxisLocation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentJunctions
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
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

/-! Derive common-parent transitions directly from retained mesh geometry. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentHandoffs

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
open Purelib.Data.Rat
open Purelib.Geometry.Rectangle
open Purelib.Riemann.Integration.PreparedParentAxisLocation
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence SurfacePreparation)
open
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
open
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks (ParentBlock cacheParent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank (ParentBlockBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentJunctions.ParentBlock
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters (signedAxis)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Geometry.Rectangle.SourceIntervals (axisCoordinate axisIntervals)
open Purelib.Riemann.Integration.RectangularAxisParameterRange (AxisParameterRange)
open Purelib.Data.Rat.Fraction.Compatibility
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
    regular domains differential}

namespace ParentBlock
variable {vertical : Bool}
  {beforePhysical afterPhysical : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock
/-- Consecutive forward physical blocks either remain in one retained parent or cross exactly one parent boundary, with
both endpoint parameters certified. -/
theorem consecutive_parent_handoff
    (before : ParentBlocks.ParentBlock occurrence vertical true beforePhysical)
    (after : ParentBlocks.ParentBlock occurrence vertical true afterPhysical)
    (ordered : ∀ parent ∈ occurrence.compared.entered.cache.parents,
      SourceIntervals.axisCoordinate vertical (parent.edge.point 0) < SourceIntervals.axisCoordinate vertical
        (parent.edge.point 1))
    (consecutive : afterPhysical.lower = beforePhysical.upper) :
    (after.index = before.index ∧ after.firstParameter = before.lastParameter) ∨
      (after.index.val = before.index.val + 1 ∧
        before.lastParameter = 1 ∧ after.firstParameter = 0) := by
  have monotone : before.index.val ≤ after.index.val := by
    apply Nat.le_of_not_gt
    intro backwards
    have separated := ParentCache.parents_separated occurrence.compared.entered.cache (SourceIntervals.axisCoordinate
      vertical)
      (fun parent member => (ordered parent member).le) after.index before.index backwards
    have physical : beforePhysical.lower < afterPhysical.upper :=
      beforePhysical.ordered.trans_le (consecutive.symm.trans_le afterPhysical.ordered.le)
    have positive := before.physical_inside.1.trans_lt (physical.trans_le after.physical_inside.2)
    exact (not_lt_of_ge separated) positive
  rcases Nat.eq_or_lt_of_le monotone with same | next
  · have equal : after.index = before.index := Fin.ext same.symm
    exact Or.inl ⟨equal, before.same_parent_parameters after equal consecutive⟩
  · have separated := ParentCache.parents_separated occurrence.compared.entered.cache (SourceIntervals.axisCoordinate
      vertical)
      (fun parent member => (ordered parent member).le) before.index after.index next
    have endpoints := before.handoff_of_separated after consecutive separated
    have joint := before.last_axis.trans (consecutive.symm.trans after.first_axis.symm)
    change before.lastParameter = 1 ∧ after.firstParameter = 0 at endpoints
    rw [endpoints.1, endpoints.2] at joint
    exact Or.inr ⟨ParentCache.parents_no_skip occurrence.compared.entered.cache (SourceIntervals.axisCoordinate
      vertical) ordered
      before.index after.index next joint, endpoints⟩

/-- The actual occurrence supplies parent monotonicity; only its physical orientation and the shared interval endpoint
are needed. -/
theorem occurrence_parent_handoff
    (before : ParentBlocks.ParentBlock occurrence occurrence.sourceVertical true beforePhysical)
    (after : ParentBlocks.ParentBlock occurrence occurrence.sourceVertical true afterPhysical)
    (forward : occurrence.sourceForward = true)
    (consecutive : afterPhysical.lower = beforePhysical.upper) :
    (after.index = before.index ∧ after.firstParameter = before.lastParameter) ∨
      (after.index.val = before.index.val + 1 ∧
        before.lastParameter = 1 ∧ after.firstParameter = 0) := by
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentHandoffs.ParentBlock.consecutive_parent_handoff
    before after _ consecutive
  intro parent member
  have ordered := BoundaryAxisLocation.source_parent_ordered occurrence member
  simpa only [forward, SourceBlockParameters.signedAxis, if_pos (rfl : true = true), if_neg Bool.false_ne_true,
    -eq_self, -iff_self] using ordered

/-- Physical order runs backwards through the retained parents on a reversed occurrence. A crossing uses parameters zero
and one, with no skipped parent. -/
theorem reverse_occurrence_parent_handoff
    (before : ParentBlocks.ParentBlock occurrence occurrence.sourceVertical false beforePhysical)
    (after : ParentBlocks.ParentBlock occurrence occurrence.sourceVertical false afterPhysical)
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
    have separated := ParentCache.parents_separated occurrence.compared.entered.cache project
      (fun parent member => (ordered parent member).le) before.index after.index backwards
    have opposite := Fraction.Order.Arithmetic.neg_le_neg_direct separated
    simp only [project, SourceBlockParameters.signedAxis, if_neg Bool.false_ne_true, neg_neg, -eq_self, -iff_self]
      at opposite
    have physical : beforePhysical.lower < afterPhysical.upper :=
      beforePhysical.ordered.trans_le (consecutive.symm.trans_le afterPhysical.ordered.le)
    have positive := before.physical_inside.1.trans_lt (physical.trans_le after.physical_inside.2)
    exact (not_lt_of_ge opposite) positive
  rcases Nat.eq_or_lt_of_le monotone with same | next
  · have equal : after.index = before.index := Fin.ext same
    exact Or.inl ⟨equal, before.same_parent_parameters after equal consecutive⟩
  · have separated := ParentCache.parents_separated occurrence.compared.entered.cache project
      (fun parent member => (ordered parent member).le) after.index before.index next
    have opposite := Fraction.Order.Arithmetic.neg_le_neg_direct separated
    simp only [project, SourceBlockParameters.signedAxis, if_neg Bool.false_ne_true, neg_neg, -eq_self, -iff_self]
      at opposite
    have endpoints := before.handoff_of_separated after consecutive opposite
    change before.lastParameter = 0 ∧ after.firstParameter = 1 at endpoints
    have joint := before.last_axis.trans (consecutive.symm.trans after.first_axis.symm)
    rw [endpoints.1, endpoints.2] at joint
    have signedJoint := congrArg (fun value : InverseRootPolynomial.Coordinate => -value) joint.symm
    exact Or.inr ⟨ParentCache.parents_no_skip occurrence.compared.entered.cache project ordered
      after.index before.index next signedJoint, endpoints⟩

end ParentBlock

namespace ParentBlockBank
variable {columns rows : Nat} {geometry : Purelib.Riemann.Normalization.RectangularInverseModels.Geometry columns
  rows} {cuts : Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts geometry}
  {meshBox : Purelib.Geometry.Rational.Box} {mesh :
    Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh cuts meshBox}

/-- Adjacent entries of the cached physical source bank carry the exact parent transition and parameter join, without
caller-supplied chain evidence. -/
theorem consecutive_handoff
    (bank : ParentBank.ParentBlockBank occurrence mesh occurrence.sourceVertical true)
    (forward : occurrence.sourceForward = true)
    (before after : Fin (SourceIntervals.axisIntervals mesh occurrence.sourceVertical).length)
    (next : after.val = before.val + 1) :
    let left := (bank.get before)
    let right := (bank.get after)
    (right.index = left.index ∧ right.firstParameter = left.lastParameter) ∨
      (right.index.val = left.index.val + 1 ∧ left.lastParameter = 1 ∧ right.firstParameter = 0) :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentHandoffs.ParentBlock.occurrence_parent_handoff
    (bank.get before) (bank.get after) forward
    (SourceIntervals.axis_consecutive mesh occurrence.sourceVertical before after next)

/-- The same physical bank traversal gives the reverse parent transition when the occurrence runs against the positive
physical axis. -/
theorem reverse_consecutive_handoff
    (bank : ParentBank.ParentBlockBank occurrence mesh occurrence.sourceVertical false)
    (backward : occurrence.sourceForward = false)
    (before after : Fin (SourceIntervals.axisIntervals mesh occurrence.sourceVertical).length)
    (next : after.val = before.val + 1) :
    let left := bank.get before
    let right := bank.get after
    (right.index = left.index ∧ right.firstParameter = left.lastParameter) ∨
      (left.index.val = right.index.val + 1 ∧ left.lastParameter = 0 ∧ right.firstParameter = 1) :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentHandoffs.ParentBlock.reverse_occurrence_parent_handoff
    (bank.get before) (bank.get after) backward
    (SourceIntervals.axis_consecutive mesh occurrence.sourceVertical before after next)

end ParentBlockBank

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentHandoffs
