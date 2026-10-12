module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSourceStages
import Purelib.Data.Nat.Order
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Curves

open Purelib

open Purelib.Riemann

public section

/-! Compute and certify one numerical source stage for every retained occurrence request. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization

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

variable (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared)
  {index : Nat} (inputs : retained.Inputs index)
  (capacities : Fin prepared.occurrences.length → Nat) (requested : Normalization.InverseRootPolynomial.Coordinate)
    (minimum : Nat)

/-- Capacities are fixed by the geometry before numerical acquisition. -/
@[expose] def ParentRunSchedules :=
  Data.Vector.DependentVector (fun outer : Fin prepared.occurrences.length =>
    ParentRunSchedule
      retained inputs outer (capacities outer) requested minimum)

variable {retained inputs capacities requested minimum}

namespace ParentRunSchedules

set_option genInjectivity false in
/-- A common numerical source stage for the entire retained dependent schedule vector.

The stage is certified to equal the maximum of the input index and all original schedule thresholds. -/
structure SourceStage (schedules :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules
  retained inputs capacities requested minimum) where
  /-- The common numerical stage selected for the original schedule vector. -/ stage : Nat
  /-- The selected stage is exactly the maximum of the input index and schedule thresholds. -/ stage_eq : stage = max
    index (schedules.maximum (fun _ schedule => schedule.sourceIndex))

constructive_injectivity SourceStage

namespace SourceStage
variable (schedules :
  CommonBasisPreparation.ParentRunSchedules
  retained inputs capacities requested minimum)

/-- Compute the maximum stage paying the original input and every retained occurrence schedule. -/
@[expose] def build :
  ParentRunSchedules.SourceStage
  schedules :=
  ⟨max index (schedules.maximum (fun _ schedule => schedule.sourceIndex)), rfl⟩

variable {schedules} (selected :
  ParentRunSchedules.SourceStage
  schedules)

/-- The original input index is bounded by the synchronized source stage.

The selected stage retains the maximum of that index and the original
schedule thresholds, so its left maximum bound preserves the input index. -/
theorem index_le : index ≤ selected.stage := by
  rw [selected.stage_eq, Data.Nat.Order.max_eq_natMax]
  exact Data.Nat.Order.le_max_left _ _

/-- Each retained occurrence source threshold is bounded by the synchronized source stage.

The original dependent vector bounds each retained schedule by its maximum.
The selected stage retains that same maximum as its right argument. -/
theorem source_le (outer : Fin prepared.occurrences.length) : (schedules.get outer).sourceIndex ≤ selected.stage := by
  have maximumLe : schedules.maximum (fun _ schedule => schedule.sourceIndex) ≤ selected.stage := by
    rw [selected.stage_eq, Data.Nat.Order.max_eq_natMax]
    exact Data.Nat.Order.le_max_right _ _
  exact (schedules.get_le_maximum (fun _ schedule => schedule.sourceIndex) outer).trans maximumLe

/-- The acquired inputs use the computed stage. Each request is transported
without repeating its finite query or refinement calculations. -/
@[expose] def atInputs {laterIndex : Nat} (laterInputs : retained.Inputs laterIndex) (later : selected.stage ≤
  laterIndex) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules
      retained laterInputs capacities requested minimum :=
  Data.Vector.DependentVector.ofFn (fun outer =>
    ParentRunSourceStages.CommonBasisPreparation.ParentRunSchedule.atInputs
    (schedules.get outer) laterInputs ((selected.source_le outer).trans later))

/-- Every transported schedule is paid at the supplied later numerical input stage. -/
theorem atInputs_source_paid {laterIndex : Nat} (laterInputs : retained.Inputs laterIndex) (later : selected.stage ≤
  laterIndex)
    (outer : Fin prepared.occurrences.length) :
    ((selected.atInputs laterInputs later).get outer).sourceIndex ≤ laterIndex := by
  dsimp only
    [atInputs]
  rw [Data.Vector.DependentVector.ofFn_get]
  exact
    (ParentRunSourceStages.CommonBasisPreparation.ParentRunSchedule.atInputs_sourceIndex
    (schedules.get outer) laterInputs ((selected.source_le outer).trans later)).le

/-- Synchronizing numerical input data preserves each retained occurrence refinement depth. -/
theorem atInputs_depth {laterIndex : Nat} (laterInputs : retained.Inputs laterIndex) (later : selected.stage ≤
  laterIndex)
    (outer : Fin prepared.occurrences.length) :
    ((selected.atInputs laterInputs later).get outer).depth = (schedules.get outer).depth := by
  dsimp only
    [atInputs]
  rw [Data.Vector.DependentVector.ofFn_get]
  exact
    ParentRunSourceStages.CommonBasisPreparation.ParentRunSchedule.atInputs_depth
    (schedules.get outer) laterInputs ((selected.source_le outer).trans later)

/-- Synchronizing numerical input data preserves each retained occurrence source magnitude. -/
theorem atInputs_magnitude {laterIndex : Nat} (laterInputs : retained.Inputs laterIndex) (later : selected.stage ≤
  laterIndex)
    (outer : Fin prepared.occurrences.length) :
    ((selected.atInputs laterInputs later).get outer).magnitude = (schedules.get outer).magnitude := by
  dsimp only
    [atInputs]
  rw [Data.Vector.DependentVector.ofFn_get]
  exact
    ParentRunSourceStages.CommonBasisPreparation.ParentRunSchedule.atInputs_magnitude
    (schedules.get outer) laterInputs ((selected.source_le outer).trans later)

end SourceStage
end ParentRunSchedules
end CommonBasisPreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization
