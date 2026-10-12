module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Curves

open Purelib.Riemann

@[expose] public section

/-! Retain computed requests across an equal physical fragment capacity. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentCapacityTransport

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

namespace CommonBasisPreparation.ParentRunSchedule
variable {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared}
  {index : Nat} {inputs : retained.Inputs index}
  {outer : Fin prepared.occurrences.length} {first last minimum : Nat} {requested :
    Normalization.InverseRootPolynomial.Coordinate}

/-- This is equality transport of the retained data, not request reacquisition. -/
def castCapacity (equal : first = last)
    (schedule :
      ParentRunSchedule
      retained inputs outer first requested minimum) :
    ParentRunSchedule
      retained inputs outer last requested minimum :=
  Eq.mp (congrArg (fun capacity =>
    ParentRunSchedule
    retained inputs outer capacity requested minimum) equal) schedule

/-- Transporting the retained schedule across equal capacities preserves its refinement depth. -/
theorem castCapacity_depth (equal : first = last)
    (schedule :
      ParentRunSchedule
      retained inputs outer first requested minimum) :

      (castCapacity
      equal schedule).depth = schedule.depth := by
  cases equal
  rfl

/-- Transporting the retained schedule across equal capacities preserves its source stage. -/
theorem castCapacity_sourceIndex (equal : first = last)
    (schedule :
      ParentRunSchedule
      retained inputs outer first requested minimum) :

      (castCapacity
      equal schedule).sourceIndex = schedule.sourceIndex := by
  cases equal
  rfl

/-- Transporting the retained schedule across equal capacities preserves its source magnitude. -/
theorem castCapacity_magnitude (equal : first = last)
    (schedule :
      ParentRunSchedule
      retained inputs outer first requested minimum) :

      (castCapacity
      equal schedule).magnitude = schedule.magnitude := by
  cases equal
  rfl

end CommonBasisPreparation.ParentRunSchedule
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentCapacityTransport
