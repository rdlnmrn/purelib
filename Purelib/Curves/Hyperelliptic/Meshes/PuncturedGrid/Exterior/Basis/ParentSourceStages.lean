module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceStageReadback
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Curves

open Purelib.Riemann

@[expose] public section

/-! Static parent source ownership survives numerical stage synchronization. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentSourceStages

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

/-- Selecting the same original parent at different numerical stages retains exactly the same source covers.

Both selections use the original occurrence and parent position, including their exact parent transport. -/
theorem parentInput_sources_eq (retained :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared) {firstIndex lastIndex :
  Nat}
    (first : retained.Inputs firstIndex) (last : retained.Inputs lastIndex)
    (outer : Fin prepared.occurrences.length)
    (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) :
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained first outer position).sources =
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained last outer position).sources
      := by
  have left := Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceStageReadback.SelectedInput.cast_sources
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.parentIndex_read prepared outer position)
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection.NumericalBank.select retained.anchors
      retained.sources first (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.parentIndex prepared outer
      position))
  have right := Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceStageReadback.SelectedInput.cast_sources
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.parentIndex_read prepared outer position)
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection.NumericalBank.select retained.anchors
      retained.sources last (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.parentIndex prepared outer
      position))
  have middle := congrArg (Eq.mp (congrArg (fun parent =>
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.parentIndex_read prepared outer position)))
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceStageReadback.NumericalBank.select_sources_eq retained.anchors
      retained.sources first last (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.parentIndex prepared
      outer position))
  exact left.trans (middle.trans right.symm)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentSourceStages
