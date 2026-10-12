module
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Riemann

@[expose] public section

/-!
# Actual exterior period samples from the shared segment caches

The whole-component allowances are chosen before the segment requests.
Assembly reuses those requests, polynomial increments and integral samples.
The original period's scheduler then supplies a certified later sample on
its exact retained parents, separately for every exterior component.
-/

open Purelib.Data.Rat

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation (SampledEntry)

open Purelib.Riemann.Normalization

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {index depth readingIndex : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
  {localTarget localArea target : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

namespace AllSurfacePreparation.SampledEntry

/-- One quarter of a nonnegative rational allowance is at most that allowance. -/
public theorem quarter_le {value : Normalization.InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ value) : value /
  4 ≤ value :=
  open Purelib.Data.Rat in Fraction.Order.Field.divide_le_self nonnegative (by decide)

/-- The retained source primitive sum equals the total of the original sampled left path. -/
theorem source_sum
    (value : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry (regular :=
      regular) sample shared depth readingIndex localTarget localArea floor) :
    value.evaluated.source.primitiveSum = value.evaluated.left.total := by
  have same := value.evaluated.reference.value_eq
  rw [value.evaluated.source_eq, value.evaluated.value_eq] at same
  exact same.symm

/-- Reuse the original segment cache and increment as a period request part under the supplied local and coefficient
allowances. -/
def periodPart
    (value : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry (regular :=
      regular) sample shared depth readingIndex localTarget localArea floor)
    (localBound coefficientBound : Normalization.InverseRootPolynomial.Coordinate) (localLe : localTarget ≤ localBound)
      (coefficientLe : localTarget ≤ coefficientBound) :
    Readings.PreparedPrimitiveRequestBatches.RequestPart curve differential genus localBound coefficientBound
      localTarget := open Purelib.Data.Rat in by
  have positive := value.entry.request.positive
  have firstPositive := Fraction.Order.Field.div_pos_direct positive (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)
  have secondPositive := Fraction.Order.Field.div_pos_direct firstPositive (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)
  have secondLe : (localTarget / 4) / 4 ≤ localTarget :=
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.AllSurfacePreparation.SampledEntry.quarter_le
    firstPositive.le).trans
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.AllSurfacePreparation.SampledEntry.quarter_le
    positive.le)
  have thirdLe : ((localTarget / 4) / 4) / 4 ≤ localTarget :=
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.AllSurfacePreparation.SampledEntry.quarter_le
    secondPositive.le).trans secondLe
  refine ⟨value.entry.occurrence.compared.entered.cache.parents, _, value.evaluated.source, value.increment,
    value.evaluated.source.localTarget_le.trans (thirdLe.trans localLe),
    value.evaluated.source.coefficient_accurate.trans_le
      (value.evaluated.source.coefficientTarget_le.trans (thirdLe.trans coefficientLe)), ?_⟩
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.AllSurfacePreparation.SampledEntry.source_sum value]
  exact value.source_close.le.trans secondLe

end AllSurfacePreparation.SampledEntry

namespace SampledComponent

/-- Retain one period request part for every original sampled occurrence, preserving its order. -/
def periodParts
    (localBound coefficientBound : Normalization.InverseRootPolynomial.Coordinate) (localLe : localTarget ≤ localBound)
      (coefficientLe : localTarget ≤ coefficientBound) :
    List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry (regular :=
      regular) sample shared depth readingIndex localTarget localArea floor) →
      List (Readings.PreparedPrimitiveRequestBatches.RequestPart curve differential genus localBound coefficientBound
        localTarget)
  | [] => []
  | value :: values =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.AllSurfacePreparation.SampledEntry.periodPart value
    localBound coefficientBound localLe coefficientLe ::
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.SampledComponent.periodParts localBound
        coefficientBound localLe coefficientLe values

/-- The assembled request parts retain exactly the concatenated original occurrence-parent lists. -/
theorem periodParts_parents
    (localBound coefficientBound : Normalization.InverseRootPolynomial.Coordinate) (localLe : localTarget ≤ localBound)
      (coefficientLe : localTarget ≤ coefficientBound)
    (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry
      (regular := regular) sample shared depth readingIndex localTarget localArea floor)) :
    Readings.PreparedPrimitiveRequestBatches.RequestBatch.parents
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.SampledComponent.periodParts localBound
      coefficientBound localLe coefficientLe values) =
      (values.map (fun value => value.entry.occurrence.compared.entered.cache.parents)).flatten := by
  induction values with
  | nil => rfl
  | cons value values ih => exact congrArg (List.append _) ih

/-- The assembled request parts retain exactly the original sampled increments. -/
theorem periodParts_values
    (localBound coefficientBound : Normalization.InverseRootPolynomial.Coordinate) (localLe : localTarget ≤ localBound)
      (coefficientLe : localTarget ≤ coefficientBound)
    (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry
      (regular := regular) sample shared depth readingIndex localTarget localArea floor)) :
    Readings.PreparedPrimitiveRequestBatches.RequestBatch.values
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.SampledComponent.periodParts localBound
      coefficientBound localLe coefficientLe values) = values.map SampledEntry.increment := by
  induction values with
  | nil => rfl
  | cons value values ih => exact congrArg (List.cons _) ih

/-- The request-part list has one entry per original sampled occurrence. -/
theorem periodParts_length
    (localBound coefficientBound : Normalization.InverseRootPolynomial.Coordinate) (localLe : localTarget ≤ localBound)
      (coefficientLe : localTarget ≤ coefficientBound)
    (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry
      (regular := regular) sample shared depth readingIndex localTarget localArea floor)) :
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.SampledComponent.periodParts localBound coefficientBound
      localLe coefficientLe values).length = values.length := by
  induction values with
  | nil => rfl
  | cons value values ih => exact congrArg Nat.succ ih

set_option genInjectivity false in
/-- Retain the assembled request and its numerical link to this component's
existing shared-triangle sum. Each request part is an original segment cache. -/
structure PeriodSource
    (group : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent (regular := regular) sample
      shared depth readingIndex localTarget localArea floor)
    (plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlan group.component target) where
  /-- The actual request parts reusing the original segment caches. -/ parts : List
    (Readings.PreparedPrimitiveRequestBatches.RequestPart curve differential genus plan.localTarget plan.coefficient
    localTarget)
  /-- The request parts retain exactly the original component program's parent list. -/ parents_eq :
    Readings.PreparedPrimitiveRequestBatches.RequestBatch.parents parts = group.component.program.cache.parents
  /-- The request-part values are exactly the component's original sampled increments. -/ values_eq :
    Readings.PreparedPrimitiveRequestBatches.RequestBatch.values parts = group.values.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry.increment
  /-- There is exactly one request part per original sampled occurrence. -/ count_eq : parts.length =
    group.values.length
  /-- The assembled controlled sum request on the same original component parents. -/ request :
    Readings.PreparedControlledPrimitiveRequests.ControlledSumRequest group.component.program.cache.parents genus target
  /-- The assembled primitive sum is exactly the sum of the retained request parts. -/ sum_eq : request.primitiveSum =
    Readings.PreparedPrimitiveRequestBatches.RequestBatch.primitiveSum parts
  /-- The original component surface total approximates the assembled primitive sum within the paid finite occurrence
    bound. -/ accurate : Data.Gaussian.Norm.Basic.normSq (group.surface.total - request.primitiveSum) ≤
    (group.values.length : Normalization.InverseRootPolynomial.Coordinate) * ((group.values.length :
      Normalization.InverseRootPolynomial.Coordinate) * localTarget)

constructive_injectivity PeriodSource

namespace PeriodSource

/-- Assemble the original segment request parts on the exact retained component parents and certify their
shared-triangle error bound. -/
def build (group : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent (regular := regular)
  sample shared depth readingIndex localTarget localArea floor)
    (plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlan group.component target)
    (localLe : localTarget ≤ plan.localTarget) (coefficientLe : localTarget ≤ plan.coefficient) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.SampledComponent.PeriodSource group plan := by
  let parts := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.SampledComponent.periodParts plan.localTarget
    plan.coefficient localLe coefficientLe group.values
  have parentsEq : Readings.PreparedPrimitiveRequestBatches.RequestBatch.parents parts =
    group.component.program.cache.parents := by
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.SampledComponent.periodParts_parents]
    have same := congrArg (fun occurrences : List
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
      regular domains differential) =>
      (occurrences.map (fun occurrence => occurrence.compared.entered.cache.parents)).flatten) group.occurrences_eq
    simp only [List.Map.map_map, Function.comp_def] at same
    exact same.trans group.component.prepared.parents_eq
  have valuesEq := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.SampledComponent.periodParts_values
    plan.localTarget plan.coefficient localLe coefficientLe group.values
  have countEq := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.SampledComponent.periodParts_length
    plan.localTarget plan.coefficient localLe coefficientLe group.values
  let assembled := Readings.PreparedPrimitiveRequestBatches.RequestBatch.assemble parts target plan.positive
    (by rw [parentsEq]; exact plan.localTarget_eq) plan.mass (by rw [parentsEq]; exact plan.mass_eq)
    plan.coefficient_eq plan.coefficient_positive
  let request := Readings.PreparedPrimitiveRequestBatches.ControlledSumRequest.castParents assembled parentsEq
  have sumEq : request.primitiveSum = Readings.PreparedPrimitiveRequestBatches.RequestBatch.primitiveSum parts :=
    Readings.PreparedPrimitiveRequestBatches.ControlledSumRequest.castParents_primitiveSum assembled parentsEq
  have estimate := Readings.PreparedPrimitiveRequestBatches.RequestBatch.error_le parts
  rw [valuesEq, countEq, ← sumEq, ← group.surface.total_eq] at estimate
  exact ⟨parts, parentsEq, valuesEq, countEq, request, sumEq, estimate⟩

end PeriodSource
end SampledComponent

set_option genInjectivity false in
/-- Prepare the original numerical period's all-later certificate before
any numerical period sample is evaluated. -/
structure ComponentPeriodTail
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains)
    (depth readingIndex : Nat) (localTarget localArea : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat)
      (target : Normalization.InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The original sampled exterior component. -/ group :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent (regular := regular) sample shared
    depth readingIndex localTarget localArea floor
  /-- The allowances selected for this exact original component before period sampling. -/ plan :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlan group.component target
  /-- The assembled request from the component's retained original segment caches. -/ source :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.SampledComponent.PeriodSource group plan
  /-- The controlled request on the original period's recast parent list. -/ request :
    Readings.PreparedControlledPrimitiveRequests.ControlledSumRequest
    (group.component.program.period.initial.state.parents.map
    (Integration.PreparedEdgeRecasting.recastCenteredEdge (Periods.PeriodMatrix.standardDifferential
      differential.index))) genus target
  /-- The period request retains exactly the assembled source primitive sum. -/ source_eq : request.primitiveSum =
    source.request.primitiveSum
  /-- The original period's all-later certificate above the supplied minimum stage. -/ tail :
    Periods.PreparedPeriodPrimitiveRequests.PeriodTail group.component.program.period.initial
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
    (Periods.PeriodMatrix.standardDifferential differential.index) request minimum

constructive_injectivity ComponentPeriodTail

namespace ComponentPeriodTail

/-- Acquire the original period's all-later certificate from the component's retained segment request parts and supplied
stage floor. -/
def build (group : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent (regular := regular)
  sample shared depth readingIndex localTarget localArea floor)
    (plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlan group.component target)
    (localLe : localTarget ≤ plan.localTarget) (coefficientLe : localTarget ≤ plan.coefficient) (minimum : Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTail (regular := regular) sample shared
      depth readingIndex localTarget localArea floor target minimum :=
  let source := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.SampledComponent.PeriodSource.build group plan
    localLe coefficientLe
  let request := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.periodRequest
    group.component.program source.request
  let tail := Periods.PreparedPeriodPrimitiveRequests.PeriodTail.acquire group.component.program.period.initial
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
    (Periods.PeriodMatrix.standardDifferential differential.index) request minimum
  ⟨group, plan, source, request,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.periodRequest_sum group.component.program
    source.request, tail⟩

variable {minimum : Nat}

/-- Every sufficiently late original period sample approximates the retained component surface total within the combined
occurrence and period bound. -/
theorem accurate
    (prepared : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTail (regular := regular)
      sample shared depth readingIndex localTarget localArea floor target minimum)
    (stage : Nat) (later : prepared.tail.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (prepared.group.surface.total -
      ((prepared.group.component.program.period.program differential.index).integral.model stage).integralSample) <
      2 * ((prepared.group.values.length : Normalization.InverseRootPolynomial.Coordinate) *
        ((prepared.group.values.length : Normalization.InverseRootPolynomial.Coordinate) * localTarget) + target) :=
        open Purelib.Data.Rat in by
  have close := prepared.tail.accurate
    (Integration.PreparedRefinementProgramCore.standardDifferential_mem_standardDifferentials differential.index) stage
      later
  have programEq : ((prepared.group.component.program.period.program differential.index).integral.model
    stage).integralSample =
      (Periods.PreparedRootSafePeriodPrograms.RootClosedState.flatModel prepared.group.component.program.period.initial
        (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
        (Periods.PeriodMatrix.standardDifferential differential.index) stage).integralSample := by
    rw [prepared.group.component.program.period.program_model]
    exact Periods.PreparedRootSafePeriodPrograms.RootClosedState.sample_eq_flat
      prepared.group.component.program.period.initial
      (Integration.PreparedRefinementProgramCore.standardDifferentials genus) (Periods.PeriodMatrix.standardDifferential
        differential.index) stage
  rw [prepared.source_eq, ← programEq] at close
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at close
  exact (Gaussian.Norm.Bounds.normSq_sub_le_via prepared.group.surface.total prepared.source.request.primitiveSum
    (((prepared.group.component.program.period.program differential.index).integral.model
      stage).integralSample)).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 2)
      ((add_le_add prepared.source.accurate le_rfl).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_left_direct close _)))

end ComponentPeriodTail

set_option genInjectivity false in
/-- Every sample is evaluated at the already selected common stage. -/
structure ComponentPeriodSample
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains)
    (depth readingIndex : Nat) (localTarget localArea : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat)
      (target : Normalization.InverseRootPolynomial.Coordinate) (minimum stage : Nat)
    extends Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTail (regular := regular) sample
      shared depth readingIndex localTarget localArea floor target minimum where
  /-- The common stage meets the original retained tail certificate. -/ tail_stage_le : tail.stage ≤ stage
  /-- The actual original period sample at the common stage. -/ period :
    Periods.PreparedPeriodPrimitiveRequests.PeriodSample group.component.program.period.initial
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
    (Periods.PeriodMatrix.standardDifferential differential.index) request minimum
  /-- The retained sample uses exactly the chosen common stage. -/ stage_eq : period.stage = stage
  /-- The sample is exactly the original period program's integral reading. -/ program_sample : period.sample =
    ((group.component.program.period.program differential.index).integral.model stage).integralSample
  /-- The actual period sample meets the original component comparison bound. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq (group.surface.total - period.sample) <
    2 * ((group.values.length : Normalization.InverseRootPolynomial.Coordinate) * ((group.values.length :
      Normalization.InverseRootPolynomial.Coordinate) * localTarget) + target)

constructive_injectivity ComponentPeriodSample

namespace ComponentPeriodSample

variable {minimum : Nat}

/-- Sample the original numerical period at the supplied common stage using its retained all-later certificate. -/
def ofTail
    (prepared : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTail (regular := regular)
      sample shared depth readingIndex localTarget localArea floor target minimum)
    (stage : Nat) (later : prepared.tail.stage ≤ stage) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodSample (regular := regular) sample shared
      depth readingIndex localTarget localArea floor target minimum stage := by
  let period := prepared.tail.sampleAt
    (Integration.PreparedRefinementProgramCore.standardDifferential_mem_standardDifferentials differential.index) stage
    later
  have programEq : period.sample = ((prepared.group.component.program.period.program differential.index).integral.model
    stage).integralSample := by
    rw [period.sample_eq, prepared.group.component.program.period.program_model]
    exact (Periods.PreparedRootSafePeriodPrograms.RootClosedState.sample_eq_flat
      prepared.group.component.program.period.initial
      (Integration.PreparedRefinementProgramCore.standardDifferentials genus) (Periods.PeriodMatrix.standardDifferential
        differential.index) stage).symm
  exact ⟨prepared, later, period, rfl, programEq, programEq ▸ prepared.accurate stage later⟩

end ComponentPeriodSample

set_option genInjectivity false in
/-- The retained all-later period certificates for an ordered list of original exterior component samples. -/
structure ComponentPeriodTails
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains)
    (depth readingIndex : Nat) (localTarget localArea : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat)
    (groups : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent (regular := regular)
      sample shared depth readingIndex localTarget localArea floor))
    (target : Normalization.InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The retained original component period-tail certificates in order. -/ values : List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTail (regular := regular) sample shared
    depth readingIndex localTarget localArea floor target minimum)
  /-- The retained tail certificates belong to exactly the original component sample list. -/ groups_eq : values.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTail.group = groups

constructive_injectivity ComponentPeriodTails

namespace ComponentPeriodTails

/-- Acquire one retained period tail for every original component and its corresponding pre-sampling allowance plan. -/
def build (minimum : Nat) :
    (groups : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent (regular := regular)
      sample shared depth readingIndex localTarget localArea floor)) →
    {components : List
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
      regular domains differential)} →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlans target components) →
      groups.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent.component = components →
    localTarget ≤ plans.localMinimum → localTarget ≤ plans.coefficientMinimum →
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTails sample shared depth readingIndex
        localTarget localArea floor groups target minimum
  | [], _, .nil, _, _, _ => ⟨[], rfl⟩
  | [], _, .cons _ _, equal, _, _ => by cases equal
  | _ :: _, _, .nil, equal, _, _ => by cases equal
  | group :: groups, _, .cons plan plans, equal, localLe, coefficientLe => by
      have equalities := List.cons.inj equal
      cases equalities.1
      let head := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTail.build group plan
        (localLe.trans (Fraction.Order.Basic.min_le_left _ _))
        (coefficientLe.trans (Fraction.Order.Basic.min_le_left _ _)) minimum
      let tail := Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTails.build
        minimum groups plans equalities.2 (localLe.trans (Fraction.Order.Basic.min_le_right _ _))
        (coefficientLe.trans (Fraction.Order.Basic.min_le_right _ _))
      exact ⟨head :: tail.values, congrArg (List.cons group) tail.groups_eq⟩

variable {minimum : Nat}

/-- The maximum retained period-tail stage, with the supplied minimum for an empty list. -/
def maximum : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTail (regular := regular)
  sample shared depth readingIndex localTarget localArea floor target minimum) → Nat
  | [] => minimum
  | head :: tail => max head.tail.stage
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTails.maximum tail)

/-- Every original retained period-tail stage is bounded by the computed common maximum. -/
theorem stage_le (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTail (regular
  := regular) sample shared depth readingIndex localTarget localArea floor target minimum)) :
    ∀ value ∈ values, value.tail.stage ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTails.maximum values := by
  induction values with
  | nil => intro value member; cases member
  | cons head tail ih =>
      intro value member
      rcases List.Membership.mem_cons.mp member with rfl | member
      · exact Nat.Order.le_max_left _ _
      · exact (ih value member).trans (Nat.Order.le_max_right _ _)

/-- Evaluate all retained original period tails at the supplied common sufficient stage. -/
def sampleMany (stage : Nat) :
    (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTail (regular := regular)
      sample shared depth readingIndex localTarget localArea floor target minimum)) →
    (∀ value ∈ values, value.tail.stage ≤ stage) →
      List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodSample (regular := regular) sample
        shared depth readingIndex localTarget localArea floor target minimum stage)
  | [], _ => []
  | head :: tail, later => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodSample.ofTail head
    stage (later head List.mem_cons_self) ::
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTails.sampleMany stage
        tail (fun value member => later value (List.mem_cons_of_mem head member))

/-- The evaluated period samples retain exactly the original ordered tail certificates. -/
theorem sampleMany_sources (stage : Nat) :
    (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTail (regular := regular)
      sample shared depth readingIndex localTarget localArea floor target minimum)) →
    (later : ∀ value ∈ values, value.tail.stage ≤ stage) →
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTails.sampleMany stage values later).map
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodSample.toComponentPeriodTail = values
  | [], _ => rfl
  | head :: tail, later => congrArg (List.cons head)
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTails.sampleMany_sources
        stage tail (fun value member => later value (List.mem_cons_of_mem head member)))

end ComponentPeriodTails

set_option genInjectivity false in
/-- The original exterior component period samples evaluated at one cached common sufficient stage. -/
structure ComponentPeriodSamples
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains)
    (depth readingIndex : Nat) (localTarget localArea : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat)
    (groups : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent (regular := regular)
      sample shared depth readingIndex localTarget localArea floor))
    (target : Normalization.InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The original retained all-later component certificates. -/ tails :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTails sample shared depth readingIndex
    localTarget localArea floor groups target minimum
  /-- The cached common sufficient period-sampling stage. -/ stage : Nat
  /-- The common stage is the maximum of the original retained tail stages. -/ stage_eq : stage =
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTails.maximum tails.values
  /-- The actual original component period samples at that common stage. -/ values : List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodSample (regular := regular) sample shared
    depth readingIndex localTarget localArea floor target minimum stage)
  /-- The samples retain exactly the original ordered tail certificates. -/ tails_eq : values.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodSample.toComponentPeriodTail = tails.values
  /-- The samples belong to exactly the original ordered component sample list. -/ groups_eq : values.map (fun value =>
    value.group) = groups

constructive_injectivity ComponentPeriodSamples

namespace ComponentPeriodSamples

/-- Acquire all original component tails once, compute their common stage and sample each retained period there. -/
def build (minimum : Nat)
    (groups : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent (regular := regular)
      sample shared depth readingIndex localTarget localArea floor))
    {components : List
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
      regular domains differential)}
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlans target components)
      (componentsEq : groups.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent.component
      = components)
    (localLe : localTarget ≤ plans.localMinimum) (coefficientLe : localTarget ≤ plans.coefficientMinimum) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodSamples sample shared depth readingIndex
      localTarget localArea floor groups target minimum := by
  let tails := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTails.build minimum groups plans
    componentsEq localLe coefficientLe
  let stage := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTails.maximum tails.values
  let values := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTails.sampleMany stage
    tails.values (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTails.stage_le tails.values)
  have tailsEq := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTails.sampleMany_sources
    stage tails.values (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTails.stage_le
    tails.values)
  have groupsEq := congrArg (List.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodTail.group) tailsEq
  simp only [List.Map.map_map, Function.comp_def] at groupsEq
  exact ⟨tails, stage, rfl, values, tailsEq, groupsEq.trans tails.groups_eq⟩

end ComponentPeriodSamples

namespace AllSurfacePreparation.Request.Evaluation

variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {areaTarget : Normalization.InverseRootPolynomial.Coordinate}
  {request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared target
    areaTarget floor}

/-- Consume the retained component grouping and the pre-sampling allowances
of this exact original request. All period samples share one computed stage. -/
def periodSamples (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.Evaluation request sample
  shared depth readingIndex)
    (groups : ComponentSamples sample shared depth
      readingIndex request.localTarget request.budget.areaTarget floor
      prepared.components evaluated.samples.values) (minimum : Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodSamples sample shared depth readingIndex
      request.localTarget request.budget.areaTarget floor groups.groups target minimum :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.ComponentPeriodSamples.build minimum groups.groups
    request.periods groups.components_eq request.local_period_le request.coefficient_period_le

end AllSurfacePreparation.Request.Evaluation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples
