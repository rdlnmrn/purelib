module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Classification
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Fraction
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
public import Purelib.Data.List.DependentProduct

/-! # Original parent and interval occurrences in cached grid-fragment banks

The readers follow the same bounded parent/interval positions through the
original dependent spines. Every complete cell and regular/hole payload
is read from those caches, without another grid lookup or classification.
-/

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces LocatedCell)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {differential : Differential genus} {axes : PrimitiveAxes bank.grid}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits

variable {ambient : Geometry.Rational.Box}
variable {grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial ambient}
variable {localAxes : PrimitiveAxes grid}

universe u

/-- Read the whole original axis partition at a literal bounded parent occurrence. -/
@[expose] def partitionAt : {parents : List (CenteredEdge curve differential)} →
    (splits : PrimitiveSplits localAxes parents) → (index : Fin parents.length) →
      AxisPartition 0 1 (localAxes.parameters (parents[index.val]'index.isLt))
  | [], .nil, index => Fin.elim0 index
  | _, .cons partition _, ⟨0, _⟩ => partition
  | _, .cons _ remaining, ⟨index + 1, bounded⟩ =>
      partitionAt remaining ⟨index, Nat.lt_of_succ_lt_succ bounded⟩

/-- The cached split count is the exact sum of original stored interval counts, independently of entry payloads. -/
theorem count_eq_sum : {parents : List (CenteredEdge curve differential)} →
    (splits : PrimitiveSplits localAxes parents) → {family : Fin parents.length → Type u} →
    (entries : Data.List.DependentProduct parents family) →
    Data.List.DependentProduct.sum parents
      (fun index _actual => (splits.partitionAt index).intervals.length) entries = splits.count
  | [], .nil, _, _ => rfl
  | _ :: parents, .cons partition tail, _, entries => by
      change partition.intervals.length + Data.List.DependentProduct.sum parents
        (fun index _actual => (tail.partitionAt index).intervals.length) entries.2 = partition.count + tail.count
      exact (congrArg (fun count => count + Data.List.DependentProduct.sum parents
        (fun index _actual => (tail.partitionAt index).intervals.length) entries.2) partition.count_eq.symm).trans
        (congrArg (Nat.add partition.count) (count_eq_sum tail entries.2))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

namespace PrimitiveFragmentCell

section Partitions

variable {ambient : Geometry.Rational.Box}
variable {grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial ambient}
variable {localAxes : PrimitiveAxes grid} {parent : CenteredEdge curve differential}
variable {cuts : List Data.Rat.Fraction.Rational}
variable {partition : AxisPartition 0 1 cuts} {interval : PreparedAxisPartitions.Interval}

/-- Every fraction in this retained interval lies in its actual cached cell, by affine endpoint containment. -/
theorem point_inside (fragment : PrimitiveFragmentCell localAxes parent partition interval)
    (parameter : Data.Rat.Fraction.Rational) (inside : interval.lower ≤ parameter ∧ parameter ≤ interval.upper) :
    fragment.cell.box.Contains (parent.edge.point parameter) := by
  let fraction := interval.fraction parameter
  have first := (Riemann.Integration.PreparedParentSplitting.prepared_point_eq parent interval.lower).symm.trans
    fragment.first_eq.symm
  have last := (Riemann.Integration.PreparedParentSplitting.prepared_point_eq parent interval.upper).symm.trans
    fragment.last_eq.symm
  have normalized := congrArg (PreparedSegmentCuts.point (parent.edge.point 0) (parent.edge.point 1))
    (interval.fraction_eq parameter).symm
  have affine := PreparedSegmentCuts.point_affine (parent.edge.point 0) (parent.edge.point 1)
    interval.lower interval.upper fraction
  have same := (Riemann.Integration.PreparedParentSplitting.prepared_point_eq parent parameter).trans
    (normalized.trans (affine.trans (congrArg₂ (fun first last => PreparedSegmentCuts.point first last fraction)
      first last)))
  have contained := Geometry.Rational.Box.contains_line fragment.first_inside fragment.last_inside
    (interval.fraction_inside inside)
  exact (same.trans (PreparedSegmentCuts.point_eq_line fragment.first fragment.last fraction)).symm ▸ contained

/-- Restrict one actual cached cell to an interval in a supplied retained partition.

The child membership and subinterval bounds are geometric incidence.
Both new oriented endpoints follow from the original affine containment;
the same complete grid cell and its membership are reused. The returned
property records that cell identity without exposing the constructor.
-/
def restrict (original : PrimitiveFragmentCell localAxes parent partition interval)
    {newCuts : List Data.Rat.Fraction.Rational} (refined : AxisPartition 0 1 newCuts)
    (child : PreparedAxisPartitions.Interval) (member : child ∈ refined.intervals)
    (inside : interval.lower ≤ child.lower ∧ child.upper ≤ interval.upper) :
    {value : PrimitiveFragmentCell localAxes parent refined child // value.cell = original.cell} :=
  let firstInside : interval.lower ≤ child.lower ∧ child.lower ≤ interval.upper :=
    ⟨inside.1, child.ordered.1.trans inside.2⟩
  let lastInside : interval.lower ≤ child.upper ∧ child.upper ≤ interval.upper :=
    ⟨inside.1.trans child.ordered.1, inside.2⟩
  let value : PrimitiveFragmentCell localAxes parent refined child :=
    ⟨member, original.cell, original.cell_member, parent.edge.point child.lower, rfl,
      parent.edge.point child.upper, rfl, original.point_inside child.lower firstInside,
      original.point_inside child.upper lastInside⟩
  ⟨value, rfl⟩

end Partitions

end PrimitiveFragmentCell

namespace PrimitiveFragmentCells

variable {parent : CenteredEdge curve differential}
variable {partition : AxisPartition 0 1 (axes.parameters parent)}

/-- Read the complete original located fragment at the bounded interval occurrence. -/
@[expose] def fragmentAt : {intervals : List PreparedAxisPartitions.Interval} →
    (located : PrimitiveFragmentCells axes parent partition intervals) → (index : Fin intervals.length) →
      PrimitiveFragmentCell axes parent partition (intervals[index.val]'index.isLt)
  | [], .nil, index => Fin.elim0 index
  | _, .cons first _, ⟨0, _⟩ => first
  | _, .cons _ remaining, ⟨index + 1, bounded⟩ =>
      fragmentAt remaining ⟨index, Nat.lt_of_succ_lt_succ bounded⟩

/-- Read the identical already classified regular/hole payload at that same bounded fragment occurrence. -/
@[expose] def classificationAt (faces : PuncturedFaces bank) :
    {intervals : List PreparedAxisPartitions.Interval} →
    (located : PrimitiveFragmentCells axes parent partition intervals) → Classifications faces located →
    (index : Fin intervals.length) →
      LocatedCell faces.regulars faces.holes (located.fragmentAt index).cell
  | [], .nil, _, index => Fin.elim0 index
  | _, .cons _ _, classified, ⟨0, _⟩ => classified.1
  | _, .cons _ remaining, classified, ⟨index + 1, bounded⟩ =>
      classificationAt faces remaining classified.2 ⟨index, Nat.lt_of_succ_lt_succ bounded⟩

end PrimitiveFragmentCells

namespace LocatedPrimitiveSplits

/-- Read the same complete fragment-location spine at the original bounded parent occurrence. -/
@[expose] def fragmentsAt : {parents : List (CenteredEdge curve differential)} →
    {splits : PrimitiveSplits axes parents} → (located : LocatedPrimitiveSplits axes splits) →
    (index : Fin parents.length) →
      PrimitiveFragmentCells axes (parents[index.val]'index.isLt) (splits.partitionAt index)
        (splits.partitionAt index).intervals
  | [], _, .nil, index => Fin.elim0 index
  | _, _, .cons first _, ⟨0, _⟩ => first
  | _, _, .cons _ remaining, ⟨index + 1, bounded⟩ =>
      fragmentsAt remaining ⟨index, Nat.lt_of_succ_lt_succ bounded⟩

/-- Read the identical complete regular/hole product at that same original parent occurrence. -/
@[expose] def classificationsAt (faces : PuncturedFaces bank) :
    {parents : List (CenteredEdge curve differential)} → {splits : PrimitiveSplits axes parents} →
    (located : LocatedPrimitiveSplits axes splits) → Classifications faces located →
    (index : Fin parents.length) → PrimitiveFragmentCells.Classifications faces (located.fragmentsAt index)
  | [], _, .nil, _, index => Fin.elim0 index
  | _, _, .cons _ _, classified, ⟨0, _⟩ => classified.1
  | _, _, .cons _ remaining, classified, ⟨index + 1, bounded⟩ =>
      classificationsAt faces remaining classified.2 ⟨index, Nat.lt_of_succ_lt_succ bounded⟩

end LocatedPrimitiveSplits
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

end
