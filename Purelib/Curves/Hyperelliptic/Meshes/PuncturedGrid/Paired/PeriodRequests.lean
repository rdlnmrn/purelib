module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Riemann

@[expose] public section

/-!
# Synchronized primitive requests for the actual corrected A/B family

Prepare each row's primitive requests and certified decay tail, choose the
maximum of the cached thresholds, and only then evaluate the A/B samples.
All samples refer to one stage of the same `PeriodData`. These comparisons
retain the individual primitive requests; agreement with a common global
surface primitive remains a separate geometric obligation.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}

set_option genInjectivity false in
/-- The two original controlled period requests for one paired row.

Keep each request's own initial parents and certified period tail. -/
structure RequestRow (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (differential
  : Fin genus) (target : Readings.PreparedPrimitiveRequests.Coordinate)
    (minimumStage : Nat) (index : Fin genus) where
  /-- The original A-period controlled request on its exact initial parents. -/ a :
    Readings.PreparedControlledPrimitiveRequests.ControlledSumRequest ((prepared.aWalk index).initial.state.parents.map
    (Integration.PreparedEdgeRecasting.recastCenteredEdge (Periods.PeriodMatrix.standardDifferential differential)))
      genus target
  /-- The original corrected B-period controlled request on its exact initial parents. -/ b :
    Readings.PreparedControlledPrimitiveRequests.ControlledSumRequest ((prepared.bWalk index).initial.state.parents.map
    (Integration.PreparedEdgeRecasting.recastCenteredEdge (Periods.PeriodMatrix.standardDifferential differential)))
      genus target
  /-- The certified original A-period tail for the retained A request. -/ aTail :
    Periods.PreparedPeriodPrimitiveRequests.PeriodTail (prepared.aWalk index).initial
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
    (Periods.PeriodMatrix.standardDifferential differential) a minimumStage
  /-- The certified original B-period tail for the retained B request. -/ bTail :
    Periods.PreparedPeriodPrimitiveRequests.PeriodTail (prepared.bWalk index).initial
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
    (Periods.PeriodMatrix.standardDifferential differential) b minimumStage

constructive_injectivity RequestRow

namespace RequestRow

/-- Acquire both original controlled requests and their corresponding certified tails. -/
def acquire (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (differential : Fin
  genus) (target : Readings.PreparedPrimitiveRequests.Coordinate) (positive : 0 < target)
    (minimumStage : Nat) (index : Fin genus) : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.RequestRow
      prepared differential target minimumStage index :=
  let a := (prepared.aWalk index).primitiveRequest differential target positive
  let b := (prepared.bWalk index).primitiveRequest differential target positive
  ⟨a, b, Periods.PreparedPeriodPrimitiveRequests.PeriodTail.acquire (prepared.aWalk index).initial
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
    (Periods.PeriodMatrix.standardDifferential differential) a minimumStage,
    Periods.PreparedPeriodPrimitiveRequests.PeriodTail.acquire (prepared.bWalk index).initial
      (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
      (Periods.PeriodMatrix.standardDifferential differential) b minimumStage⟩

/-- Take the maximum of the two retained original tail stages. -/
def threshold {prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired} {differential : Fin
  genus} {target : Readings.PreparedPrimitiveRequests.Coordinate}
    {minimumStage : Nat} {index : Fin genus} (row : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.RequestRow
      prepared differential target minimumStage index) : Nat :=
  max row.aTail.stage row.bTail.stage

end RequestRow

set_option genInjectivity false in
/-- The global finite stage is tied to the thresholds in the retained rows.
The empty family is permitted and uses the supplied minimum stage. -/
structure Requests (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (differential :
  Fin genus) (target : Readings.PreparedPrimitiveRequests.Coordinate) (minimumStage : Nat) where
  /-- The actual dependent original paired request rows. -/ rows : Data.Vector.DependentVector (fun index : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.RequestRow prepared differential target minimumStage index)
  /-- The cached common sampling stage. -/ stage : Nat
  /-- The stage equals the maximum of the requested floor and all original row thresholds. -/ stage_eq : stage = max
    minimumStage (rows.maximum (fun _ row => row.threshold))

constructive_injectivity Requests

namespace Requests

variable {prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired} {differential : Fin
  genus} {target : Readings.PreparedPrimitiveRequests.Coordinate} {minimumStage : Nat}

/-- Acquire every original paired request and cache a stage meeting the supplied floor and all row thresholds. -/
def acquire (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (differential : Fin
  genus) (target : Readings.PreparedPrimitiveRequests.Coordinate) (positive : 0 < target)
    (minimumStage : Nat) : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.Requests prepared differential
      target minimumStage :=
  let rows := Data.Vector.DependentVector.ofFn
    (Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.RequestRow.acquire prepared differential target positive
    minimumStage)
  ⟨rows, max minimumStage (rows.maximum (fun _ row => row.threshold)), rfl⟩

/-- The retained common sampling stage meets the original requested floor. -/
theorem stage_ge (requests : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.Requests prepared differential
  target minimumStage) : minimumStage ≤ requests.stage := by
  rw [requests.stage_eq]
  exact Nat.Order.le_max_left _ _

/-- Each original A tail is ready at the retained common sampling stage. -/
theorem a_stage_le (requests : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.Requests prepared differential
  target minimumStage) (index : Fin genus) :
    (requests.rows.get index).aTail.stage ≤ requests.stage := by
  rw [requests.stage_eq]
  exact (Nat.Order.le_max_left _ _).trans
    ((requests.rows.get_le_maximum (fun _ row => row.threshold) index).trans (Nat.Order.le_max_right _ _))

/-- Each original B tail is ready at the retained common sampling stage. -/
theorem b_stage_le (requests : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.Requests prepared differential
  target minimumStage) (index : Fin genus) :
    (requests.rows.get index).bTail.stage ≤ requests.stage := by
  rw [requests.stage_eq]
  exact (Nat.Order.le_max_right _ _).trans
    ((requests.rows.get_le_maximum (fun _ row => row.threshold) index).trans (Nat.Order.le_max_right _ _))

set_option genInjectivity false in
/-- The two actual original period samples of a retained row at the shared global stage. -/
structure SampleRow (requests : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.Requests prepared differential
  target minimumStage) (index : Fin genus) where
  /-- The actual original A-period sample. -/ a : Periods.PreparedPeriodPrimitiveRequests.PeriodSample (prepared.aWalk
    index).initial (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
    (Periods.PeriodMatrix.standardDifferential differential) (requests.rows.get index).a minimumStage
  /-- The actual original corrected B-period sample. -/ b : Periods.PreparedPeriodPrimitiveRequests.PeriodSample
    (prepared.bWalk index).initial (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
    (Periods.PeriodMatrix.standardDifferential differential) (requests.rows.get index).b minimumStage
  /-- The original A sample uses the retained common stage. -/ a_stage : a.stage = requests.stage
  /-- The original B sample uses the retained common stage. -/ b_stage : b.stage = requests.stage

constructive_injectivity SampleRow

/-- Read both original certified tails at the common stage and retain their exact stage identities. -/
def SampleRow.build (requests : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.Requests prepared differential
  target minimumStage) (index : Fin genus) : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.Requests.SampleRow
  requests index :=
  ⟨(requests.rows.get index).aTail.sampleAt
    (Integration.PreparedRefinementProgramCore.standardDifferential_mem_standardDifferentials differential)
      requests.stage (requests.a_stage_le index),
    (requests.rows.get index).bTail.sampleAt
      (Integration.PreparedRefinementProgramCore.standardDifferential_mem_standardDifferentials differential)
      requests.stage (requests.b_stage_le index), rfl, rfl⟩

set_option genInjectivity false in
/-- The dependent bank of original paired samples at the retained common stage. -/
structure Samples (requests : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.Requests prepared differential
  target minimumStage) where
  /-- The actual original sample pair for every retained row. -/ rows : Data.Vector.DependentVector (fun index : Fin
    genus => Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.Requests.SampleRow requests index)

constructive_injectivity Samples

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.Requests in
/-- Sample every original certified pair at the retained common stage. -/
def samples (requests : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.Requests prepared differential target
  minimumStage) : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.Requests.Samples requests :=
  ⟨Data.Vector.DependentVector.ofFn (Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.Requests.SampleRow.build
    requests)⟩

namespace Samples

variable {requests : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.Requests prepared
  differential target minimumStage} (samples :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.Requests.Samples requests)

/-- Read the retained original A sample of the selected row. -/
def a (index : Fin genus) : Gaussian := (samples.rows.get index).a.sample

/-- Read the retained original corrected B sample of the selected row. -/
def b (index : Fin genus) : Gaussian := (samples.rows.get index).b.sample

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.Requests.Samples
/-- The cached A reading equals the original period model at the common stage. -/
theorem a_eq (index : Fin genus) : samples.a index =
    ((prepared.periodData.aProgram differential index).integral.model requests.stage).integralSample := by
  rw [a, (samples.rows.get index).a.sample_eq, (samples.rows.get index).a_stage, prepared.aProgram_model]
  exact (Periods.PreparedRootSafePeriodPrograms.RootClosedState.sample_eq_flat (prepared.aWalk index).initial
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
    (Periods.PeriodMatrix.standardDifferential differential) requests.stage).symm

/-- The cached B reading equals the original period model at the common stage. -/
theorem b_eq (index : Fin genus) : samples.b index =
    ((prepared.periodData.bProgram differential index).integral.model requests.stage).integralSample := by
  rw [b, (samples.rows.get index).b.sample_eq, (samples.rows.get index).b_stage, prepared.bProgram_model]
  exact (Periods.PreparedRootSafePeriodPrograms.RootClosedState.sample_eq_flat (prepared.bWalk index).initial
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
    (Periods.PeriodMatrix.standardDifferential differential) requests.stage).symm

end

/-- The original A sample is within its own request's target of its retained primitive sum. -/
theorem a_accurate (index : Fin genus) : Data.Gaussian.Norm.Basic.normSq ((requests.rows.get index).a.primitiveSum -
  samples.a index) < target := by
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  exact (samples.rows.get index).a.accurate

/-- The original B sample is within its own request's target of its retained primitive sum. -/
theorem b_accurate (index : Fin genus) : Data.Gaussian.Norm.Basic.normSq ((requests.rows.get index).b.primitiveSum -
  samples.b index) < target := by
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  exact (samples.rows.get index).b.accurate

end Samples

/-- The certificate remains valid on the entire synchronized tail, including
later stages chosen by another differential or an inverse/energy request. -/
theorem a_accurate_later (requests : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.Requests prepared
  differential target minimumStage)
    (index : Fin genus) (stage : Nat) (later : requests.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq ((requests.rows.get index).a.primitiveSum -
      ((prepared.periodData.aProgram differential index).integral.model stage).integralSample) < target := by
  rw [prepared.aProgram_model, Periods.PreparedGridPeriodPrograms.PeriodWalk.state,
    Periods.PreparedRootSafePeriodPrograms.RootClosedState.sample_eq_flat (prepared.aWalk index).initial
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus) (Periods.PeriodMatrix.standardDifferential
    differential) stage]
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  exact (requests.rows.get index).aTail.accurate
    (Integration.PreparedRefinementProgramCore.standardDifferential_mem_standardDifferentials differential)
    stage ((requests.a_stage_le index).trans later)

/-- Every later original B-period reading remains within its own retained request's target. -/
theorem b_accurate_later (requests : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests.Requests prepared
  differential target minimumStage)
    (index : Fin genus) (stage : Nat) (later : requests.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq ((requests.rows.get index).b.primitiveSum -
      ((prepared.periodData.bProgram differential index).integral.model stage).integralSample) < target := by
  rw [prepared.bProgram_model, Periods.PreparedGridPeriodPrograms.PeriodWalk.state,
    Periods.PreparedRootSafePeriodPrograms.RootClosedState.sample_eq_flat (prepared.bWalk index).initial
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus) (Periods.PeriodMatrix.standardDifferential
    differential) stage]
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  exact (requests.rows.get index).bTail.accurate
    (Integration.PreparedRefinementProgramCore.standardDifferential_mem_standardDifferentials differential)
    stage ((requests.b_stage_le index).trans later)

end Requests
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests
