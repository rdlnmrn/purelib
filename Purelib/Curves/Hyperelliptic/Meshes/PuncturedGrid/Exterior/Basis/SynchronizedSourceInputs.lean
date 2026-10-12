module
meta import Purelib.Elab.ConstructiveInjectivity
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Curves

open Purelib.Riemann

@[expose] public section

/-! Acquire a numerical bank at the computed source stage and retain its certified requests. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SynchronizedSourceInputs

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

namespace CommonBasisPreparation

open Purelib.Data.Rat.Fraction.Compatibility

namespace ParentRunSchedules.SourceStage

variable {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared}
  {index laterIndex : Nat} {inputs : retained.Inputs index}
  {capacities : Fin prepared.occurrences.length → Nat} {requested : Normalization.InverseRootPolynomial.Coordinate}
    {minimum : Nat}
  {schedules :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules
    retained inputs capacities requested minimum}
  (selected :
    RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules.SourceStage
    schedules) (later : selected.stage ≤ laterIndex)

/-- Certify that the retained request vector is the equality transport of the original schedules to these later inputs.
-/
def RequestsReadback (laterInputs : retained.Inputs laterIndex)
    (requests :
      RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules
      retained laterInputs capacities requested minimum) : Prop :=
  requests =
    RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules.SourceStage.atInputs
    selected laterInputs later

set_option genInjectivity false in
/-- Retain the actual later numerical input bank and the transported request
bank. Their defining equalities certify precisely this acquisition. -/
structure Acquisition where
  /-- The actual numerical input bank acquired at the supplied later stage. -/ inputs : retained.Inputs laterIndex
  /-- The stored inputs are exactly the original preparation acquired at that stage. -/ inputs_eq : inputs =
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation.inputs retained laterIndex
  /-- The original computed requests transported to the exact acquired input bank. -/ requests :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules
    retained inputs capacities requested minimum
  /-- The stored requests are exactly the certified source-stage transport of the original schedule vector. -/
    requests_eq :
    RequestsReadback
    selected later inputs requests

constructive_injectivity Acquisition

/-- Primitive cells and originals are acquired once at the computed stage.
The old request calculations are retained through the source-cover readbacks. -/
def acquire :
  Acquisition
  selected later :=
  let inputs := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation.inputs retained
    laterIndex
  let requests :=
    RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules.SourceStage.atInputs
    selected inputs later
  ⟨inputs, rfl, requests, rfl⟩

namespace Acquisition
variable {selected later} (acquired :
  SourceStage.Acquisition
  selected later)

/-- Every retained acquired request threshold is paid by the acquisition stage. -/
theorem source_paid (outer : Fin prepared.occurrences.length) :
    (acquired.requests.get outer).sourceIndex ≤ laterIndex :=
  (congrArg (fun requests :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules
    retained acquired.inputs capacities requested minimum =>
    (requests.get outer).sourceIndex) acquired.requests_eq).trans_le

        (RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules.SourceStage.atInputs_source_paid
        selected acquired.inputs later outer)

/-- Acquisition preserves each original occurrence refinement depth. -/
theorem depth_readback (outer : Fin prepared.occurrences.length) :
    (acquired.requests.get outer).depth = (schedules.get outer).depth :=
  (congrArg (fun requests :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules
    retained acquired.inputs capacities requested minimum =>
    (requests.get outer).depth) acquired.requests_eq).trans

        (RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules.SourceStage.atInputs_depth
        selected acquired.inputs later outer)

/-- Acquisition preserves each original occurrence source magnitude. -/
theorem magnitude_readback (outer : Fin prepared.occurrences.length) :
    (acquired.requests.get outer).magnitude = (schedules.get outer).magnitude :=
  (congrArg (fun requests :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules
    retained acquired.inputs capacities requested minimum =>
    (requests.get outer).magnitude) acquired.requests_eq).trans

        (RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules.SourceStage.atInputs_magnitude
        selected acquired.inputs later outer)

end Acquisition
end ParentRunSchedules.SourceStage
end CommonBasisPreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SynchronizedSourceInputs
