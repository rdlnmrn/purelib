module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentSourceStages
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Curves

open Purelib.Riemann

@[expose] public section

/-! Preserve the source magnitude when advancing the numerical input stage. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitudeStages

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

namespace CommonBasisRequest.Sampled

variable (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared)
  {firstIndex lastIndex : Nat}
  (first : retained.Inputs firstIndex) (last : retained.Inputs lastIndex)

/-- Changing the numerical input stage preserves the finite list of original parent source slopes. -/
theorem sourceSlopes_eq :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude.CommonBasisRequest.Sampled.sourceSlopes retained
  first = Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude.CommonBasisRequest.Sampled.sourceSlopes
  retained last := open Purelib in by
  apply congrArg List.flatten
  apply Data.List.OfFn.Basic.ofFn_congr
  intro outer
  apply Data.List.OfFn.Basic.ofFn_congr
  intro position
  exact congrArg Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentSourceStages.parentInput_sources_eq retained first last
      outer position)

/-- Changing the numerical input stage preserves the magnitude computed from the original parent source slopes. -/
theorem parentMagnitude_eq :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude retained
  first = Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude
  retained last :=
  congrArg (fun slopes : List Normalization.InverseRootPolynomial.Coordinate => 2 * (1 +
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum id slopes))
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitudeStages.CommonBasisRequest.Sampled.sourceSlopes_eq
    retained first last)

end CommonBasisRequest.Sampled
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitudeStages
