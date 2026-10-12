module
import Purelib.Data.List.Map
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
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
meta import Mathlib.Tactic.Linter.Lint
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockJunctions
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Geometry.Rectangle

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedParentAxisLocation

open Purelib

public section

/-! Full source-run endpoints follow from the retained physical span. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits (indexedEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder (indexed_parent_at_start
  indexed_parent_at_finish)
open Purelib.Geometry.Rectangle.SourceIntervals (axisCoordinate)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence SurfacePreparation)
open
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
open
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison
open Purelib.Riemann.Normalization
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

section SourceBlockParameters
variable {evaluated :
  ParentEvaluation
  plan sample otherSample fine}
  {physical : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}

/-- The original forward occurrence endpoints bound both endpoints of every retained physical block's selected source
parent. -/
private theorem parent_bounds
    (block : SourceBlockParameters evaluated occurrence.sourceVertical true physical)
    (forward : occurrence.sourceForward = true) :
    SourceIntervals.axisCoordinate occurrence.sourceVertical occurrence.start ≤
      SourceIntervals.axisCoordinate occurrence.sourceVertical ((IndexedSourceSplits.indexedEntry evaluated
        block.index).plan.parent.edge.point 0) ∧
    SourceIntervals.axisCoordinate occurrence.sourceVertical ((IndexedSourceSplits.indexedEntry evaluated
      block.index).plan.parent.edge.point 1) ≤
      SourceIntervals.axisCoordinate occurrence.sourceVertical occurrence.finish := by
  have lengths := congrArg List.length (Evaluation.source_parents evaluated)
  rw [Data.List.Map.length_map] at lengths
  let index : Fin occurrence.compared.entered.cache.parents.length :=
    ⟨block.index.val, block.index.isLt.trans_eq lengths⟩
  have read := PreparedParentSplitSelection.mapped_read evaluated.retained
    (fun entry => entry.plan.parent) (Evaluation.source_parents evaluated) block.index index.isLt
  have bounds := ParentCache.parent_bounds occurrence.compared.entered.cache
    (SourceIntervals.axisCoordinate occurrence.sourceVertical) (fun parent member => by
      have ordered := BoundaryAxisLocation.source_parent_ordered occurrence member
      have weak := ordered.le
      simpa only [-eq_self, -iff_self, forward, SourceBlockParameters.signedAxis, if_pos rfl] using weak) index
  rw [read] at bounds
  exact bounds

/-- A physical block beginning at the occurrence start is in parent zero and begins at parameter zero. -/
theorem at_occurrence_start
    (block : SourceBlockParameters evaluated occurrence.sourceVertical true physical)
    (forward : occurrence.sourceForward = true)
    (start : physical.lower = SourceIntervals.axisCoordinate occurrence.sourceVertical occurrence.start) :
    block.index.val = 0 ∧ block.firstParameter = 0 := by
  have endpoint := le_antisymm (block.physical_inside.1.trans_eq start) (block.parent_bounds forward).1
  refine ⟨indexed_parent_at_start evaluated (SourceIntervals.axisCoordinate occurrence.sourceVertical)
    (fun parent member => ?_) block.index endpoint,
    block.first_parameter_of_parent_endpoint (start.trans endpoint.symm)⟩
  have ordered := BoundaryAxisLocation.source_parent_ordered occurrence member
  simpa only [-eq_self, -iff_self, forward, SourceBlockParameters.signedAxis, if_pos rfl] using ordered

/-- A physical block ending at the occurrence finish exhausts the parent bank and ends at parameter one. -/
theorem at_occurrence_finish
    (block : SourceBlockParameters evaluated occurrence.sourceVertical true physical)
    (forward : occurrence.sourceForward = true)
    (finish : physical.upper = SourceIntervals.axisCoordinate occurrence.sourceVertical occurrence.finish) :
    block.index.val + 1 = evaluated.retained.length ∧ block.lastParameter = 1 := by
  have endpoint := le_antisymm (block.parent_bounds forward).2
    (finish.symm.trans_le block.physical_inside.2)
  refine ⟨indexed_parent_at_finish evaluated (SourceIntervals.axisCoordinate occurrence.sourceVertical)
    (fun parent member => ?_) block.index endpoint,
    block.last_parameter_of_parent_endpoint (finish.trans endpoint.symm)⟩
  have ordered := BoundaryAxisLocation.source_parent_ordered occurrence member
  simpa only [-eq_self, -iff_self, forward, SourceBlockParameters.signedAxis, if_pos rfl] using ordered

end SourceBlockParameters
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
