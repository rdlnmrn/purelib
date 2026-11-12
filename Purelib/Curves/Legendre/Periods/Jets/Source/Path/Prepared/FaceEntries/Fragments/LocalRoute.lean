module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.FaceEntries.Fragments
public import
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Comparison.Endpoints.CommonReadings.Entries
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk

/-! # The cached physical endpoints in their same local signed row bank

Two existing PointLift caches retain the actual physical Points, local
stems, selections and corner occurrences. Their original Entry sheets
identify one old-domain sheet. The corresponding inverse/forward target
maps then certify the literal through-anchor local walk. Neither Point,
row bank, source selection, crop nor observation is reconstructed.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.FragmentSamples.FaceEntries

open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells (PrimitiveFragmentCell)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.PrimitiveFragmentCell (RegularRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.PrimitiveFragmentCell.RegularRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularLocation)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent}
variable {physicalCount floor : Nat}
variable {covered : (patch.neighborhood physicalCount).box.Contains (parent.edge.point 1)}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}
variable {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {bank : BranchCellBank (Fibre.frameCurve frame) branches higher} {faces : PuncturedFaces bank}
variable {frames : RootFrames bank.grid} {axes : PrimitiveAxes bank.grid}
variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts} {interval : PreparedAxisPartitions.Interval}
variable {prepared : PreparedParent patch physicalCount floor covered targets}
variable {fragment : PrimitiveFragmentCell axes parent partition interval}
variable {samples : FragmentSamples prepared fragment}
variable {localCount : Nat} {localTolerance : Rational} {request : LocalRequest parent localCount localTolerance}
variable {domains : FaceDomainBank frames faces.regulars} {location : RegularLocation faces.regulars fragment.cell}
variable {regular : RegularRequest domains request fragment location} {upper : regular.UpperEndpoint}
variable {query : PreparedEdge.Query parent.edge interval.lower fragment.lower_inside}
variable (entries : samples.FaceEntries regular upper query)
variable {parentSheet : Fin 2}
variable {lower : CoveredTracedPath regular.compared.acquired.inward.path
  (regular.compared.acquired.pointFrame.owners regular.compared.acquired.selected.index)}
variable {forward : CoveredTracedPath upper.acquired.outward.path
  (upper.acquired.faceFrame.owners upper.acquired.entry.sheet)}
variable {lowerParents : ParentCache lower basis parentSheet} {upperParents : ParentCache forward basis parentSheet}
variable {tolerance : Rational} {positive : 0 < tolerance}
variable {common : UpperEndpoint.CommonReadings.Preparation
  (lowerParents := lowerParents) (upperParents := upperParents) tolerance positive}
variable {old : RootEdgeBank frames} {coarse : frames.CellRestriction location.face.cell location.face.member}
variable (cached : common.LocalRows old coarse) (vertices : VertexBank cached.rows.grid)

/-- The original first PointLift type at the literal physical fraction, on the unchanged common point bank.

This is an exact alias of the existing nominal cache. Its memberships are
derived by the fragment coordinate readback. No Point or classifier
factory occurs in the alias or any later reader.
-/
abbrev FirstSource :=
  cached.PointLift
    (Eq.mpr (congrArg (fun point : Canonical => point ∈ common.points) fragment.first_eq.symm) common.first_mem)
    (first_inside (fragment := fragment) location) samples.first entries.first.entry vertices

/-- The separate original last PointLift retains its independent physical Point and Entry on the SAME local rows. -/
abbrev LastSource :=
  cached.PointLift
    (Eq.mpr (congrArg (fun point : Canonical => point ∈ common.points) fragment.last_eq.symm) common.last_mem)
    (last_inside (fragment := fragment) location) samples.last entries.last.entry vertices

variable {entries cached vertices}
variable (first : entries.FirstSource cached vertices) (last : entries.LastSource cached vertices)

/-- All four signed corner Entries from the cached first physical Point retain the old numerical domain's sheet. -/
theorem firstCorners_sheets :
    first.lifted.entries.1.sheet = regular.compared.acquired.entry.sheet ∧
    first.lifted.entries.2.1.sheet = regular.compared.acquired.entry.sheet ∧
    first.lifted.entries.2.2.1.sheet = regular.compared.acquired.entry.sheet ∧
    first.lifted.entries.2.2.2.sheet = regular.compared.acquired.entry.sheet := by
  have known := first.sheet_eq.trans entries.first_sheet
  have corners := first.lifted.entries_sheets
  exact ⟨corners.1.trans known, corners.2.1.trans known,
    corners.2.2.1.trans known, corners.2.2.2.trans known⟩

/-- The independent last physical Point's four signed corner Entries preserve that SAME retained old-domain sheet. -/
theorem lastCorners_sheets :
    last.lifted.entries.1.sheet = regular.compared.acquired.entry.sheet ∧
    last.lifted.entries.2.1.sheet = regular.compared.acquired.entry.sheet ∧
    last.lifted.entries.2.2.1.sheet = regular.compared.acquired.entry.sheet ∧
    last.lifted.entries.2.2.2.sheet = regular.compared.acquired.entry.sheet := by
  have known := last.sheet_eq.trans entries.last_sheet
  have corners := last.lifted.entries_sheets
  exact ⟨corners.1.trans known, corners.2.1.trans known,
    corners.2.2.1.trans known, corners.2.2.2.trans known⟩

/-- Retain the actual through-anchor local walk and derive its endpoint target from both cached physical Entries.

Only reverse/append metadata and retained two-sheet maps are inspected.
The original first/last PointLift caches remain supplied whole inputs.
The resulting signed target agreement is not an oriented deformation of
the physical crop or a payment for any newly joined root observations.
-/
def localRoute :
    {walk : Walks.Walk cached.rows.grid (parent.edge.point interval.lower) (parent.edge.point interval.upper) //
      walk = first.stem.reverse.append last.stem ∧
      EdgeBank.RootEdgeBank.target cached.rows.edges walk first.classified.selected.index =
        last.classified.selected.index} :=
  let walk := first.stem.reverse.append last.stem
  have sameSheet : first.classified.entry.sheet = last.classified.entry.sheet :=
    (first.sheet_eq.trans entries.first_sheet).trans (last.sheet_eq.trans entries.last_sheet).symm
  have atAnchor : EdgeBank.RootEdgeBank.target cached.rows.edges first.stem.reverse
      first.classified.selected.index = last.classified.entry.sheet :=
    first.classified.source_sheet.symm.trans sameSheet
  have final : EdgeBank.RootEdgeBank.target cached.rows.edges walk first.classified.selected.index =
      last.classified.selected.index :=
    (EdgeBank.RootEdgeBank.target_append cached.rows.edges first.stem.reverse last.stem
      first.classified.selected.index).trans
      ((congrArg (EdgeBank.RootEdgeBank.target cached.rows.edges last.stem) atAnchor).trans
        last.classified.target_from_sheet)
  ⟨walk, rfl, final⟩

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.FragmentSamples.FaceEntries

end
