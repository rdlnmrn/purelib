module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Riemann.Integration.PreparedParentAxisLocation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentHandoffs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentJunctions
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

public section

/-! Read complete parent-run endpoints from the physical occurrence span. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
open Purelib.Data.Rat
open Purelib.Geometry.Rectangle
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Integration.PreparedParentAxisLocation
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence SurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks (ParentBlock cacheParent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters (signedAxis)
open Purelib.Geometry.Rectangle.SourceIntervals (axisCoordinate)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Integration.RectangularAxisParameterRange (AxisParameterRange)
open Purelib.Data.Rat.Fraction.Compatibility
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
    regular domains differential}

namespace ParentBlock
variable {physical : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock
/-- The original forward occurrence span bounds both endpoints of its selected retained parent. -/
private theorem parent_bounds
    (block : ParentBlocks.ParentBlock occurrence occurrence.sourceVertical true physical)
    (forward : occurrence.sourceForward = true) :
    SourceIntervals.axisCoordinate occurrence.sourceVertical occurrence.start ≤
      SourceIntervals.axisCoordinate occurrence.sourceVertical ((ParentBlocks.cacheParent occurrence
        block.index).edge.point 0) ∧
    SourceIntervals.axisCoordinate occurrence.sourceVertical ((ParentBlocks.cacheParent occurrence
      block.index).edge.point 1) ≤
      SourceIntervals.axisCoordinate occurrence.sourceVertical occurrence.finish := by
  have bounds := ParentCache.parent_bounds occurrence.compared.entered.cache
    (SourceIntervals.axisCoordinate occurrence.sourceVertical) (fun parent member => by
      have ordered := BoundaryAxisLocation.source_parent_ordered occurrence member
      have weak := ordered.le
      simpa only [forward, SourceBlockParameters.signedAxis, if_pos (rfl : true = true), if_neg Bool.false_ne_true,
        -eq_self, -iff_self] using weak) block.index
  exact bounds

/-- A physical block beginning at the occurrence start is in parent zero and begins at parameter zero. -/
theorem at_occurrence_start
    (block : ParentBlocks.ParentBlock occurrence occurrence.sourceVertical true physical)
    (forward : occurrence.sourceForward = true)
    (start : physical.lower = SourceIntervals.axisCoordinate occurrence.sourceVertical occurrence.start) :
    block.index.val = 0 ∧ block.firstParameter = 0 := by
  have endpoint := _root_.le_antisymm (block.physical_inside.1.trans_eq start) (block.parent_bounds forward).1
  refine ⟨ParentCache.parent_at_start occurrence.compared.entered.cache (SourceIntervals.axisCoordinate
    occurrence.sourceVertical)
    (fun parent member => ?_) block.index endpoint,
    block.first_parameter_of_parent_endpoint (start.trans endpoint.symm)⟩
  have ordered := BoundaryAxisLocation.source_parent_ordered occurrence member
  simpa only [forward, SourceBlockParameters.signedAxis, if_pos (rfl : true = true), if_neg Bool.false_ne_true,
    -eq_self, -iff_self] using ordered

/-- A physical block ending at the occurrence finish exhausts the parent bank and ends at parameter one. -/
theorem at_occurrence_finish
    (block : ParentBlocks.ParentBlock occurrence occurrence.sourceVertical true physical)
    (forward : occurrence.sourceForward = true)
    (finish : physical.upper = SourceIntervals.axisCoordinate occurrence.sourceVertical occurrence.finish) :
    block.index.val + 1 = occurrence.compared.entered.cache.parents.length ∧ block.lastParameter = 1 := by
  have endpoint := _root_.le_antisymm (block.parent_bounds forward).2
    (finish.symm.trans_le block.physical_inside.2)
  refine ⟨ParentCache.parent_at_finish occurrence.compared.entered.cache (SourceIntervals.axisCoordinate
    occurrence.sourceVertical)
    (fun parent member => ?_) block.index endpoint,
    block.last_parameter_of_parent_endpoint (finish.trans endpoint.symm)⟩
  have ordered := BoundaryAxisLocation.source_parent_ordered occurrence member
  simpa only [forward, SourceBlockParameters.signedAxis, if_pos (rfl : true = true), if_neg Bool.false_ne_true,
    -eq_self, -iff_self] using ordered

/-- The original reversed occurrence span bounds the selected parent endpoints in physical-coordinate order. -/
private theorem reverse_parent_bounds {physical : PreparedAxisPartitions.Interval}
    (block : ParentBlocks.ParentBlock occurrence occurrence.sourceVertical false physical)
    (backward : occurrence.sourceForward = false) :
    SourceIntervals.axisCoordinate occurrence.sourceVertical ((ParentBlocks.cacheParent occurrence
      block.index).edge.point 0) ≤
      SourceIntervals.axisCoordinate occurrence.sourceVertical occurrence.start ∧
    SourceIntervals.axisCoordinate occurrence.sourceVertical occurrence.finish ≤
      SourceIntervals.axisCoordinate occurrence.sourceVertical ((ParentBlocks.cacheParent occurrence
        block.index).edge.point 1) := by
  have bounds := ParentCache.parent_bounds occurrence.compared.entered.cache
    (SourceBlockParameters.signedAxis occurrence.sourceVertical false) (fun parent member => by
      have ordered := BoundaryAxisLocation.source_parent_ordered occurrence member
      simpa only [backward, -eq_self, -iff_self] using ordered.le) block.index
  have first := Fraction.Order.Arithmetic.neg_le_neg_direct bounds.1
  have last := Fraction.Order.Arithmetic.neg_le_neg_direct bounds.2
  simp only [SourceBlockParameters.signedAxis, if_neg Bool.false_ne_true, neg_neg, -eq_self, -iff_self] at first last
  exact ⟨first, last⟩

/-- The low physical endpoint of a reversed occurrence starts at the last source parent and parameter one. -/
theorem reverse_at_physical_start {physical : PreparedAxisPartitions.Interval}
    (block : ParentBlocks.ParentBlock occurrence occurrence.sourceVertical false physical)
    (backward : occurrence.sourceForward = false)
    (start : physical.lower = SourceIntervals.axisCoordinate occurrence.sourceVertical occurrence.finish) :
    block.index.val + 1 = occurrence.compared.entered.cache.parents.length ∧ block.firstParameter = 1 := by
  have endpoint := _root_.le_antisymm (block.physical_inside.1.trans_eq start) (block.reverse_parent_bounds backward).2
  refine ⟨ParentCache.parent_at_finish occurrence.compared.entered.cache (SourceBlockParameters.signedAxis
    occurrence.sourceVertical false)
    (fun parent member => ?_) block.index (congrArg (fun value : InverseRootPolynomial.Coordinate => -value) endpoint),
    block.first_parameter_of_parent_endpoint (start.trans endpoint.symm)⟩
  have ordered := BoundaryAxisLocation.source_parent_ordered occurrence member
  simpa only [backward, -eq_self, -iff_self] using ordered

/-- The high physical endpoint of a reversed occurrence ends at source parent zero and parameter zero. -/
theorem reverse_at_physical_finish {physical : PreparedAxisPartitions.Interval}
    (block : ParentBlocks.ParentBlock occurrence occurrence.sourceVertical false physical)
    (backward : occurrence.sourceForward = false)
    (finish : physical.upper = SourceIntervals.axisCoordinate occurrence.sourceVertical occurrence.start) :
    block.index.val = 0 ∧ block.lastParameter = 0 := by
  have endpoint := _root_.le_antisymm (block.reverse_parent_bounds backward).1
    (finish.symm.trans_le block.physical_inside.2)
  refine ⟨ParentCache.parent_at_start occurrence.compared.entered.cache (SourceBlockParameters.signedAxis
    occurrence.sourceVertical false)
    (fun parent member => ?_) block.index (congrArg (fun value : InverseRootPolynomial.Coordinate => -value) endpoint),
    block.last_parameter_of_parent_endpoint (finish.trans endpoint.symm)⟩
  have ordered := BoundaryAxisLocation.source_parent_ordered occurrence member
  simpa only [backward, -eq_self, -iff_self] using ordered

end ParentBlock

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
