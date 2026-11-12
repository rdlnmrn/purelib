module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.BlockInputs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure

open Purelib.Curves

open Purelib.Geometry

open Purelib.Riemann

@[expose] public section

/-! Exact numerical ownership for fragments sharing a retained parent. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

/-- Selection depends only on the retained occurrence and parent position. -/
def parentInput (retained : Preparation.CommonBasisPreparation
  prepared) {index : Nat}
    (inputs : retained.Inputs index) (outer : Fin prepared.occurrences.length)
    (position : Fin (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) :
    Charts.Reciprocal.Disk.Basis.NumericalSelection.SelectedInput
      (ParentBlocks.cacheParent
      (ParentIndices.occurrenceAt prepared.occurrences outer)
      position) index :=
  Eq.mp (congrArg (fun parent => Charts.Reciprocal.Disk.Basis.NumericalSelection.SelectedInput parent
    index) (ParentIndices.parentIndex_read prepared outer position))
    (Charts.Reciprocal.Disk.Basis.NumericalSelection.NumericalBank.select retained.anchors
      retained.sources inputs (ParentIndices.parentIndex prepared
      outer position))

/-- A block's selected numerical input is exactly the input at its original retained parent position. -/
theorem blockInput_eq_parentInput (retained :
  Preparation.CommonBasisPreparation prepared) {index : Nat}
    (inputs : retained.Inputs index) (outer : Fin prepared.occurrences.length)
    {vertical forward : Bool} {physical : Rectangle.Partition.PreparedAxisPartitions.Interval}
    (block : ParentBlocks.ParentBlock
      (ParentIndices.occurrenceAt prepared.occurrences outer) vertical
      forward physical) :
    BlockInputs.blockInput retained inputs outer block =
      ParentInputs.parentInput retained inputs outer block.index :=
      rfl

/-- Even blocks with different intervals or orientations use the same original
numerical payload when their retained parent positions agree. -/
theorem blockInput_same_parent (retained :
  Preparation.CommonBasisPreparation prepared) {index : Nat}
    (inputs : retained.Inputs index) (outer : Fin prepared.occurrences.length)
    {vertical forward otherVertical otherForward : Bool}
    {physical otherPhysical : Rectangle.Partition.PreparedAxisPartitions.Interval}
    (before : ParentBlocks.ParentBlock
      (ParentIndices.occurrenceAt prepared.occurrences outer) vertical
      forward physical)
    (after : ParentBlocks.ParentBlock
      (ParentIndices.occurrenceAt prepared.occurrences outer)
      otherVertical otherForward otherPhysical)
    (same : before.index = after.index) :
    Eq.mp (congrArg (fun position => Charts.Reciprocal.Disk.Basis.NumericalSelection.SelectedInput
      (ParentBlocks.cacheParent
        (ParentIndices.occurrenceAt prepared.occurrences outer)
        position) index) same)
      (BlockInputs.blockInput retained inputs outer before) =
        BlockInputs.blockInput retained inputs outer after := by
  change Eq.mp _ (ParentInputs.parentInput retained inputs outer
    before.index) =
    ParentInputs.parentInput retained inputs outer after.index
  generalize before.index = first at same ⊢
  generalize after.index = last at same ⊢
  cases same
  rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
