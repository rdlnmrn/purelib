module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Riemann.Integration.PreparedParentAxisLocation
import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Riemann.Integration.RectangularAxisParameterRange
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentRefinement
import Purelib.Riemann.Paths.RectangularSegmentSplitting
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
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Geometry

open Purelib.Riemann

@[expose] public section

/-! Locate canonical physical intervals in the original exterior parent cache. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks

open Purelib.Riemann.Normalization

open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}

/-- Read a parent at its retained original cache index. -/
def cacheParent (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    (index : Fin occurrence.compared.entered.cache.parents.length) :=
  Integration.PreparedParentSplitSelection.parentAt occurrence.compared.entered.cache.parents index

set_option genInjectivity false in
/-- The original parent, retained split and executable parameter interval for a physical mesh block.

The signed endpoint order, physical-axis correspondence and located subinterval share that exact cached parent. -/
structure ParentBlock (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    (vertical forward : Bool) (physical : Rectangle.Partition.PreparedAxisPartitions.Interval) where
  /-- The selected parent's original finite cache index. -/ index : Fin occurrence.compared.entered.cache.parents.length
  /-- The retained splitting certificate for that exact original cached parent. -/ split :
    Integration.PreparedParentSplitSelection.Selected occurrence.compared.entered.mesh.splits
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence index)
  /-- The original parent endpoints increase strictly in the signed traversal direction. -/ ordered :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward
    ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence index).edge.point 0) <
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence index).edge.point 1)
  /-- The executable parameter range for the signed physical block. -/ parameters :
    Integration.RectangularAxisParameterRange.AxisParameterRange
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward
    ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence index).edge.point 0))
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence index).edge.point 1))
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward physical)
  /-- The retained parameter range has the actual physical-axis correspondence. -/ correspondence :
    Rectangle.SourceIntervals.AxisCorrespondence vertical
    ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence index).edge.point 0)
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence index).edge.point 1)
      parameters.range physical
  /-- The same parameter range is located in the original retained parent split. -/ located :
    Paths.RectangularSegmentRefinement.Subinterval split.split parameters.range

constructive_injectivity ParentBlock

/-- A retained mesh cut lies outside a physical interval in the selected signed orientation. -/
private theorem signed_outside {columns rows : Nat} {geometry : Normalization.RectangularInverseModels.Geometry columns
  rows}
    {cuts : Paths.RectangularSegmentSplitting.GridCuts geometry} {meshBox : Rational.Box}
    (mesh : Meshes.RectangularObservationMesh.ObservationMesh cuts meshBox) (vertical forward : Bool)
    {physical : Rectangle.Partition.PreparedAxisPartitions.Interval} (member : physical ∈
      Rectangle.SourceIntervals.axisIntervals mesh vertical)
    {point : Normalization.InverseRootPolynomial.Gaussian} (present : point ∈ mesh.points) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward point ≤
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward physical).lower ∨
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward physical).upper ≤
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward point := open
        Purelib.Data.Rat in by
  have outside := Rectangle.SourceIntervals.axis_cut_outside mesh vertical member present
  cases forward with
  | true => exact outside
  | false =>
    exact outside.elim (fun bound => Or.inr (Fraction.Order.Arithmetic.neg_le_neg_direct bound))
      (fun bound => Or.inl (Fraction.Order.Arithmetic.neg_le_neg_direct bound))

/-- A retained physical mesh cut cannot lie strictly inside the corresponding signed side block. -/
theorem signed_outside_for_block {columns rows : Nat} {geometry : Normalization.RectangularInverseModels.Geometry
  columns rows}
    {cuts : Paths.RectangularSegmentSplitting.GridCuts geometry} {meshBox : Rational.Box}
    (mesh : Meshes.RectangularObservationMesh.ObservationMesh cuts meshBox) (vertical forward : Bool)
    {physical : Rectangle.Partition.PreparedAxisPartitions.Interval} (member : physical ∈
      Rectangle.SourceIntervals.axisIntervals mesh vertical)
    {point : Normalization.InverseRootPolynomial.Gaussian} (present : point ∈ mesh.points) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward point ≤
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward physical).lower ∨
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward physical).upper ≤
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward point := open
        Purelib.Data.Rat in by
  have outside := Rectangle.SourceIntervals.axis_cut_outside mesh vertical member present
  cases forward with
  | true => exact outside
  | false =>
    exact outside.elim (fun bound => Or.inr (Fraction.Order.Arithmetic.neg_le_neg_direct bound))
      (fun bound => Or.inl (Fraction.Order.Arithmetic.neg_le_neg_direct bound))

/-- Remove simultaneous negation from the retained affine parameter identity. -/
private theorem unneg_affine {first last parameter value : Normalization.InverseRootPolynomial.Coordinate}
    (equal : -first + parameter * (-last - -first) = -value) :
    first + parameter * (last - first) = value :=
  (show first + parameter * (last - first) = -(-first + parameter * (-last - -first)) by ring1).trans
    ((congrArg Neg.neg equal).trans (neg_neg value))

/-- Convert a negated affine endpoint identity to its original physical-coordinate identity. -/
theorem unneg_affine_for_block {first last parameter value : Normalization.InverseRootPolynomial.Coordinate}
    (equal : -first + parameter * (-last - -first) = -value) :
    first + parameter * (last - first) = value :=
  (show first + parameter * (last - first) = -(-first + parameter * (-last - -first)) by ring1).trans
    ((congrArg Neg.neg equal).trans (neg_neg value))

/-- Locate by the original cache index, preserving repeated parents and the
shared mesh's retained split. No numerical source evaluation is required. -/
def ParentBlock.build
    {prepared :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
      regular domains differential} {previous :
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
    (selected : SourceCuts prepared previous) (member :
      occurrence ∈ prepared.occurrences)
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet} {meshTarget :
      Normalization.InverseRootPolynomial.Coordinate}
    (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet
      coarseDepth) fixed meshTarget)
    (sheet : Fin 2) (position : Fin base.faces.regulars.length)
    (vertical forward : Bool) (physical : Rectangle.Partition.PreparedAxisPartitions.Interval)
    (present : physical ∈ Rectangle.SourceIntervals.axisIntervals
      ((request.entries.get sheet).meshes.entries.get position) vertical)
    (lower : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward
      occurrence.start ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.blockMidpoint forward
      physical)
    (upper : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.blockMidpoint forward physical <
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward occurrence.finish) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock occurrence vertical forward physical :=
      open Purelib.Data.Rat in by
  let found := Integration.PreparedParentAxisLocation.ParentCache.locateAxis occurrence.compared.entered.cache
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.blockMidpoint forward physical) lower upper
  let split := Integration.PreparedParentSplitSelection.select
    occurrence.compared.entered.mesh.splits found.index
  have firstPoint := Paths.RectangularSegmentRefinement.coordinate_point_mem split.split split.split.partition.lower_mem
  have lastPoint := Paths.RectangularSegmentRefinement.coordinate_point_mem split.split split.split.partition.upper_mem
  rw [Rectangle.Partition.PreparedSegmentCuts.point_zero] at firstPoint
  rw [Rectangle.Partition.PreparedSegmentCuts.point_one] at lastPoint
  have firstOutside := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.signed_outside_for_block
    ((request.entries.get sheet).meshes.entries.get position) vertical forward present
    (selected.requested_split_points request sheet position member split.member firstPoint)
  have lastOutside := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.signed_outside_for_block
    ((request.entries.get sheet).meshes.entries.get position) vertical forward present
    (selected.requested_split_points request sheet position member split.member lastPoint)
  have between := Rectangle.Partition.PreparedSegmentCuts.midpoint_bounds
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward physical)
  have firstBound : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward
    ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence found.index).edge.point 0) ≤
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward physical).lower := by
    rcases firstOutside with bound | bound
    · exact bound
    · exact (not_lt_of_ge (bound.trans found.lower) between.2).elim
  have lastBound : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward
    physical).upper ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward
        ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence found.index).edge.point
        1) := by
    rcases lastOutside with bound | bound
    · exact (not_lt_of_ge (bound.trans between.1.le) found.upper).elim
    · exact bound
  have ordered := found.lower.trans_lt found.upper
  let parameters := Integration.RectangularAxisParameterRange.AxisParameterRange.build _ _ _ ordered ⟨firstBound,
    lastBound⟩
  have correspondence : Rectangle.SourceIntervals.AxisCorrespondence vertical
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence found.index).edge.point 0)
        ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence found.index).edge.point
        1)
      parameters.range physical := by
    cases forward with
    | true => exact Or.inl ⟨Fraction.Order.Arithmetic.sub_pos_direct ordered, parameters.first_eq, parameters.last_eq⟩
    | false =>
      have reverse := Fraction.Order.Arithmetic.neg_lt_neg_direct ordered
      change -(-Rectangle.SourceIntervals.axisCoordinate vertical
        ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence found.index).edge.point
        1)) <
        -(-Rectangle.SourceIntervals.axisCoordinate vertical
          ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence
          found.index).edge.point 0)) at reverse
      rw [neg_neg, neg_neg] at reverse
      have negative := Fraction.Order.Arithmetic.sub_lt_sub_right_direct reverse
        (Rectangle.SourceIntervals.axisCoordinate vertical
        ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence found.index).edge.point
        0))
      rw [sub_self] at negative
      exact Or.inr ⟨negative, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.unneg_affine_for_block
        parameters.first_eq, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.unneg_affine_for_block
        parameters.last_eq⟩
  exact ⟨found.index, split, ordered, parameters, correspondence,
    selected.locateInterval request sheet position member split.split split.member vertical physical present
      parameters.range parameters.within correspondence⟩

/-- The selected parent block retains an actual member of the original occurrence's parent cache. -/
theorem ParentBlock.member {vertical forward : Bool} {physical : Rectangle.Partition.PreparedAxisPartitions.Interval}
    (block : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock occurrence vertical forward
      physical) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence block.index ∈
      occurrence.compared.entered.cache.parents := List.getElem_mem block.index.isLt

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
