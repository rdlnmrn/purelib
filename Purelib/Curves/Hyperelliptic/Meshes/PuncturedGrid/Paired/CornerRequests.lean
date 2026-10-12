module
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Approximation.Budget.PreparedPrimitiveBatchBudget
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

public section

/-!
# Shared face-corner requests for corrected ordered periods

Both sides consume the retained segment banks of the corrected row, including
the preceding A prefix in B. Scalar budgets are selected before the common
face primitive bank. The final bounds concern the actual period programs on
their entire certified tails; no equality to the former raw tours is used.
-/

section

open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds

open Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

/-- Internal side selection shares one proof between the two retained walks. -/
@[expose] def cornerWalk
  (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (index : Fin genus) (bSide :
  Bool) :=
  if bSide then prepared.bWalk index else prepared.aWalk index

/-- Read the actual retained A or corrected B segment bank selected by the supplied side. -/
@[expose] def cornerSegments
  (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (index : Fin genus) (bSide :
  Bool) :
    Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (prepared.cornerWalk index bSide) :=
  match bSide with
  | false => (prepared.row index).faces.a.segments
  | true => (prepared.row index).faces.bSegments

/-- Read the retained boundary geometry for the selected original period word. -/
@[expose] def cornerGeometry
  (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (index : Fin genus) (bSide :
  Bool) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces lifted.mesh
      (prepared.cornerWalk index bSide).closed.walk
      (lifted.vertices.owner lifted.frames
        (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet))
        :=
  match bSide with
  | false => (prepared.row index).faces.a.geometry
  | true => (prepared.row index).faces.b

/-- Read the exact segment assignment for the selected original period word and its retained prefix. -/
@[expose] def cornerAssigned
  (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (index : Fin genus) (bSide :
  Bool) :=
  (prepared.cornerGeometry index bSide).assign (prepared.cornerSegments index bSide).pieces

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons in
set_option genInjectivity false in
/-- Cache the actual parent comparisons and movement mass once. -/
structure CornerBank (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (differential index : Fin genus) (bSide : Bool) where
  /-- The actual comparisons of the original retained segment parents. -/ compared :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons
    (Periods.PeriodMatrix.standardDifferential differential) 0 (prepared.cornerAssigned index bSide)
  /-- The comparison parents share the retained domain of the selected period program. -/ shared :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.UsesDomains domains
    (Periods.PeriodMatrix.standardDifferential differential) 0
    (prepared.cornerAssigned index bSide) compared
  /-- The cached original parent list. -/ parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve
    (Periods.PeriodMatrix.standardDifferential differential))
  /-- The cached parents equal the exact retained comparison projection. -/ parents_eq : parents =
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.parents
    (Periods.PeriodMatrix.standardDifferential differential) 0
    (prepared.cornerAssigned index bSide) compared
  /-- The cached movement mass of the original parent list. -/ mass : Readings.PreparedPrimitiveChargeBounds.Coordinate
  /-- The movement mass equals the original comparison-bank reading. -/ mass_eq : mass =
    Integration.PreparedRefinementMovement.movementMass parents

constructive_injectivity CornerBank

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerRequests

section

variable {prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired} {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {differential index : Fin genus} {bSide : Bool}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerRequests.CornerBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons in
/-- Cache the original segment-parent comparisons, shared domain identity and exact movement mass. -/
@[expose] def build (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (differential index : Fin genus) (bSide : Bool) :
      CornerRequests.CornerBank prepared domains differential index bSide :=
  let segments := prepared.cornerSegments index bSide
  let geometry := prepared.cornerGeometry index bSide
  let caches := segments.parentCaches (Periods.PeriodMatrix.standardDifferential differential)
  let compared := geometry.comparisons segments.pieces domains _ 0 caches
  let parents := Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.parents _
    0 (prepared.cornerAssigned index bSide) compared
  ⟨compared, geometry.comparisons_shared segments.pieces domains _ 0 caches,
    parents, rfl, Integration.PreparedRefinementMovement.movementMass parents, rfl⟩

/-- The cached parents are exactly the original period program's transported initial parents. -/
theorem original_parents (comparison : CornerRequests.CornerBank prepared
  domains differential index bSide) :
    comparison.parents = (prepared.cornerWalk index bSide).initial.state.parents.map
      (Integration.PreparedEdgeRecasting.recastCenteredEdge (Periods.PeriodMatrix.standardDifferential differential)) :=
  comparison.parents_eq.trans
    ((Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.parents_eq _ _ _
    _).trans
    ((prepared.cornerSegments index bSide).parents_eq _))

/-- The cached parent count agrees with the original selected period program. -/
theorem parentCount_eq (comparison : CornerRequests.CornerBank prepared
  domains differential index bSide) :
    (prepared.cornerSegments index bSide).parentCount = comparison.parents.length := by
  rw [comparison.original_parents, List.Map.length_map]
  exact (prepared.cornerSegments index bSide).parentCount_eq_initial

set_option genInjectivity false in
/-- Scalar payment for the original corner bank.

Retain the count-and-mass allocation, each original parent budget and their exact common minimum stage. -/
structure ScalarRequest (comparison : CornerRequests.CornerBank prepared
  domains differential index bSide) (target : Readings.PreparedPrimitiveChargeBounds.Coordinate) where
  /-- The original error allocation for the actual counts and movement mass. -/ allocation :
    Budget.PreparedPrimitiveBatchBudget.BatchAllocation target (prepared.cornerSegments index bSide).parentCount
    (prepared.cornerSegments index bSide).count comparison.mass
  /-- The scalar budgets attached to the exact original parent comparisons. -/ budgets :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets.Budgets (Periods.PeriodMatrix.standardDifferential
    differential) 0 allocation.pieceTarget
    (prepared.cornerAssigned index bSide) comparison.compared
  /-- The cached minimum stage sufficient for every original budget. -/ minimum : Nat
  /-- The cached minimum equals the exact maximum of the original budget stages. -/ minimum_eq : minimum =
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets.Budgets.maximum (Periods.PeriodMatrix.standardDifferential
    differential) 0
    (prepared.cornerAssigned index bSide) comparison.compared budgets

constructive_injectivity ScalarRequest

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerRequests.CornerBank

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerRequests.CornerBank.ScalarRequest

/-- Allocate the positive target over the actual parent count, segment count and movement mass, then prepare each
original budget. -/
@[expose] def build (comparison : CornerRequests.CornerBank prepared domains
  differential index bSide) (target : Readings.PreparedPrimitiveChargeBounds.Coordinate)
    (positive : 0 < target) : CornerBank.ScalarRequest
      comparison target :=
  let allocation := Budget.PreparedPrimitiveBatchBudget.BatchAllocation.build target positive (prepared.cornerSegments
    index bSide).parentCount
    (prepared.cornerSegments index bSide).count comparison.mass
    (comparison.mass_eq ▸ Integration.PreparedRefinementMovement.movementMass_nonnegative comparison.parents)
  let budgets := Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets.Budgets.build _ 0 allocation.pieceTarget
    allocation.pieceTarget_positive
    (prepared.cornerAssigned index bSide) comparison.compared
  ⟨allocation, budgets, Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets.Budgets.maximum _ 0
    (prepared.cornerAssigned index bSide) comparison.compared budgets, rfl⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerRequests.CornerBank.ScalarRequest

variable {comparison : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerRequests.CornerBank prepared
  domains differential index bSide} {target : Readings.PreparedPrimitiveChargeBounds.Coordinate}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerRequests.CornerBank.ScalarRequest

/-- Advance the supplied original numerical bank beyond all retained scalar-budget stages. -/
@[expose] def synchronize (scalar : CornerBank.ScalarRequest
  comparison target) {numericalIndex : Nat}
    (later : scalar.minimum ≤ numericalIndex)
    (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains) :=
  Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives.AssignedSegments.Comparisons.Synchronized.ofShared _ 0
    (prepared.cornerAssigned index bSide) comparison.compared comparison.shared scalar.budgets
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets.Budgets.indicesBelow_of_maximum_le _ _ numericalIndex
      (prepared.cornerAssigned index bSide)
      comparison.compared scalar.budgets (scalar.minimum_eq ▸ later)) numerics

set_option genInjectivity false in
/-- The request retains its actual primitive batch and the original program's
tail. Its corner value is tied to the supplied shared bank, not recomputed. -/
structure Requested (scalar : CornerBank.ScalarRequest
  comparison target) {numericalIndex : Nat}
    (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains)
    (minimumStage : Nat) where
  /-- The actual original parent comparison readings obtained from the shared bank. -/ parts : List
    (Readings.PreparedPrimitiveRequestBatches.RequestPart curve (Periods.PeriodMatrix.standardDifferential differential)
    genus
    scalar.allocation.localTarget scalar.allocation.coefficientTarget scalar.allocation.errorBound)
  /-- The controlled-sum request on the original period program's exact initial parents. -/ request :
    Readings.PreparedControlledPrimitiveRequests.ControlledSumRequest ((prepared.cornerWalk index
    bSide).initial.state.parents.map
    (Integration.PreparedEdgeRecasting.recastCenteredEdge (Periods.PeriodMatrix.standardDifferential differential)))
      genus scalar.allocation.periodTarget
  /-- The controlled request's primitive sum equals the retained original comparison sum. -/ primitiveSum_eq :
    request.primitiveSum = Readings.PreparedPrimitiveRequestBatches.RequestBatch.primitiveSum parts
  /-- The cached corner reading of the selected original period word. -/ value : Gaussian.Basic.Canonical
  /-- The cached value equals the actual corner reading from the retained numerical bank. -/ value_eq : value =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests.AssignedSegments.cornerIncrements numerics
    (prepared.cornerAssigned index bSide))
  /-- The original local corner-minus-primitive error is within its allocated quarter target. -/ localError :
    Data.Gaussian.Norm.Basic.normSq (value - request.primitiveSum) < scalar.allocation.periodTarget
  /-- The certified tail of the original period program for this exact controlled request. -/ tail :
    Periods.PreparedPeriodPrimitiveRequests.PeriodTail (prepared.cornerWalk index bSide).initial
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
    (Periods.PeriodMatrix.standardDifferential differential) request minimumStage

constructive_injectivity Requested

/-- Acquire the original parent sums from the shared numerical bank and retain the matching period tail and corner
reading. -/
@[expose] def requestWith (scalar : CornerBank.ScalarRequest
  comparison target) {numericalIndex : Nat}
    (later : scalar.minimum ≤ numericalIndex)
    (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains)
    (minimumStage : Nat) : scalar.Requested numerics minimumStage := by
  let locals := scalar.synchronize later numerics
  let allocation := scalar.allocation
  let parts := Cut.CornerRequests.parts _
    0 numerics allocation.piece_local_le allocation.piece_coefficient_le allocation.piece_error_le
    (prepared.cornerAssigned index bSide) comparison.compared comparison.shared locals.requested locals.usesPrimitives
  have parentsEq : Readings.PreparedPrimitiveRequestBatches.RequestBatch.parents parts = comparison.parents :=
    (Cut.CornerRequests.parts_parents _ _
      _ _ _ _ _ _ _ _ _).trans comparison.parents_eq.symm
  have lengthEq : parts.length = (prepared.cornerSegments index bSide).count :=
    (Cut.CornerRequests.parts_length _ _
      _ _ _ _ _ _ _ _ _).trans (prepared.cornerSegments index bSide).count_eq.symm
  have localEq : allocation.localTarget = Rational.Budget.Aggregate.perTerm allocation.periodTarget
    (Readings.PreparedPrimitiveRequestBatches.RequestBatch.parents parts).length := by
    rw [parentsEq, ← comparison.parentCount_eq]
    exact allocation.localTarget_eq
  let assembled := Readings.PreparedPrimitiveRequestBatches.RequestBatch.assemble parts allocation.periodTarget
    allocation.periodTarget_positive localEq
    comparison.mass (comparison.mass_eq.trans (congrArg Integration.PreparedRefinementMovement.movementMass
      parentsEq.symm))
    allocation.coefficientTarget_eq allocation.coefficientTarget_positive
  let combined := Readings.PreparedPrimitiveRequestBatches.ControlledSumRequest.castParents assembled (parentsEq.trans
    comparison.original_parents)
  have primitiveEq : combined.primitiveSum = Readings.PreparedPrimitiveRequestBatches.RequestBatch.primitiveSum parts :=
    Readings.PreparedPrimitiveRequestBatches.ControlledSumRequest.castParents_primitiveSum assembled _
  let value := Data.Gaussian.Norm.Sum.Basic.gaussianSum (Readings.PreparedPrimitiveRequestBatches.RequestBatch.values
    parts)
  have valueEq : value = Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests.AssignedSegments.cornerIncrements numerics
    (prepared.cornerAssigned index bSide)) :=
    congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (Cut.CornerRequests.parts_values _
      _ _ _ _ _ _ _ _ _ _)
  have localError : Data.Gaussian.Norm.Basic.normSq (value - combined.primitiveSum) < allocation.periodTarget := by
    rw [primitiveEq]
    have bounded := Readings.PreparedPrimitiveRequestBatches.RequestBatch.error_le parts
    rw [lengthEq] at bounded
    exact bounded.trans_lt allocation.error_lt
  exact ⟨parts, combined, primitiveEq, value, valueEq, localError,
    Periods.PreparedPeriodPrimitiveRequests.PeriodTail.acquire (prepared.cornerWalk index bSide).initial
      (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
      (Periods.PeriodMatrix.standardDifferential differential) combined minimumStage⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerRequests.CornerBank.ScalarRequest

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerRequests.CornerBank.ScalarRequest.Requested

/-- Every sufficiently late original period reading is within the target of the retained corner value. -/
theorem accurate {scalar : CornerBank.ScalarRequest
  comparison target} {numericalIndex minimumStage : Nat}
    {numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains}
    (result : scalar.Requested numerics minimumStage) (stage : Nat) (later : result.tail.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (result.value - (((prepared.cornerWalk index bSide).program
      differential).integral.model stage).integralSample) < target := by
  have period : Data.Gaussian.Norm.Basic.normSq (result.request.primitiveSum -
      (((prepared.cornerWalk index bSide).program differential).integral.model stage).integralSample) <
        scalar.allocation.periodTarget := by
    rw [Periods.PreparedGridPeriodPrograms.PeriodWalk.program_model,
      Periods.PreparedGridPeriodPrograms.PeriodWalk.state,
      Periods.PreparedRootSafePeriodPrograms.RootClosedState.sample_eq_flat (prepared.cornerWalk index bSide).initial
        (Integration.PreparedRefinementProgramCore.standardDifferentials genus)]
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    exact result.tail.accurate (Integration.PreparedRefinementProgramCore.standardDifferential_mem_standardDifferentials
      differential) stage later
  have split : result.value - (((prepared.cornerWalk index bSide).program differential).integral.model
    stage).integralSample =
      (result.value - result.request.primitiveSum) + (result.request.primitiveSum -
        (((prepared.cornerWalk index bSide).program differential).integral.model stage).integralSample) := by ring1
  rw [split]
  have paid := Fraction.Order.Arithmetic.add_lt_add_direct
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide : (0 : Readings.PreparedPrimitiveChargeBounds.Coordinate) < 2) result.localError)
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide : (0 : Readings.PreparedPrimitiveChargeBounds.Coordinate) < 2) period)
  have total : 2 * scalar.allocation.periodTarget + 2 * scalar.allocation.periodTarget = target := by
    rw [scalar.allocation.periodTarget_eq]
    rw [show 2 * (target / 4) + 2 * (target / 4) = (target / 4) * 4 by ring1]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    ((show 2 * (Data.Gaussian.Norm.Basic.normSq (result.value - result.request.primitiveSum) +
      Data.Gaussian.Norm.Basic.normSq (result.request.primitiveSum -
      (((prepared.cornerWalk index bSide).program differential).integral.model stage).integralSample)) =
      2 * Data.Gaussian.Norm.Basic.normSq (result.value - result.request.primitiveSum) + 2 *
        Data.Gaussian.Norm.Basic.normSq (result.request.primitiveSum -
      (((prepared.cornerWalk index bSide).program differential).integral.model stage).integralSample) by ring1) ▸
        paid.trans_eq total)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerRequests.CornerBank.ScalarRequest.Requested

end
end
end
