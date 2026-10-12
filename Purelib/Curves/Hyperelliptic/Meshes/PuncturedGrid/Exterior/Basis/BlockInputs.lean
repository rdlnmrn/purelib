module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure

open Purelib.Curves

open Purelib.Geometry

open Purelib.Riemann

@[expose] public section

/-! Read canonical mesh-block inputs from the component's retained bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.BlockInputs

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

/-- Transport only the positional parent identity; preserve the selected
covers, primitive polynomials and cell samples from the original input bank. -/
def blockInput (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation
  prepared) {index : Nat} (inputs : retained.Inputs index)
    (outer : Fin prepared.occurrences.length)
    {vertical forward : Bool} {physical : Rectangle.Partition.PreparedAxisPartitions.Interval}
    (block : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) vertical
      forward physical) :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection.SelectedInput
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer)
      block.index) index :=
  Eq.mp (congrArg (fun parent => Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection.SelectedInput parent
    index) (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.blockIndex_read prepared outer block))
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection.NumericalBank.select retained.anchors
      retained.sources inputs (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.blockIndex prepared outer
      block))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.BlockInputs
