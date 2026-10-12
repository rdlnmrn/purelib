module
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Approximation.Budget.PreparedPrimitiveBatchBudget
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches
import Purelib.Riemann.Topology.PreparedRefinementRootChains
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Budget

open Purelib.Approximation.Budget.PreparedPrimitiveBatchBudget

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives.AssignedSegments

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives.AssignedSegments.Comparisons

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData

open Purelib.Data.Rat

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests

open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms

open Purelib.Riemann.Readings

open Purelib.Riemann.Topology

open Purelib.Riemann.Topology.PreparedRootSafeCycleStates

public section

/-!
# Whole-cut-cycle local primitive comparison with the actual period program

A fixed bank retains the original parents, local face domains and movement
mass. Every positive request computes local numerical data, pays all segment
errors globally, and selects an arbitrarily late sample of the original
root-safe cut-period program. Repeated face/sheet occurrences use exactly one
shared primitive, anchor, offset and corner cache. There is no numerical-success
hypothesis or fixed error floor. The value is a sum of fixed face-corner
increments, with mesh-owner discrepancies paid; the global jump identity
remains separate.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutCycleProgram)
open Purelib.Approximation.Budget.PreparedPrimitiveBatchBudget (BatchAllocation)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches (RequestPart)
open Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches
open Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches.ControlledSumRequest
open Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests (PeriodSample)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_nonnegative)
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (standardDifferentials
  standardDifferential_mem_standardDifferentials)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks (FaceBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments (Comparisons)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets (Budgets)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives.AssignedSegments.Comparisons
  (Synchronized)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {source :
    Differential genus} {prepared :
    CutCycleProgram lifted source}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons in
set_option genInjectivity false in
/-- Geometry and expensive mass calculations are shared by all later accuracy and minimum-stage requests for this
differential. -/
structure PrimitiveBank (bank : FaceBanks.FaceBank prepared) (differential : Fin genus) where
  /-- The original shared regular face-domain bank. -/ domains : DomainBanks.FaceDomainBank lifted.frames
    base.faces.regulars
  /-- The actual segment comparisons for the retained standard differential and original assigned segments. -/ compared
    : AssignedSegments.Comparisons (PeriodMatrix.standardDifferential differential) 0 bank.assigned
  /-- Every actual segment comparison uses the retained original shared face-domain bank. -/ sharedDomains :
    Comparisons.UsesDomains domains (PeriodMatrix.standardDifferential differential) 0 bank.assigned compared
  /-- The cached original comparison-parent list recast to the retained differential. -/ parents : List
    (PreparedSubdivisionModelCore.CenteredEdge curve (PeriodMatrix.standardDifferential differential))
  /-- The cached parents are exactly the actual assigned-segment comparison parents. -/ parents_eq : parents =
    Comparisons.parents (PeriodMatrix.standardDifferential differential) 0 bank.assigned compared
  /-- The cached movement mass of the original retained parents. -/ mass : PreparedPrimitiveChargeBounds.Coordinate
  /-- The mass cache is exactly the original movement-mass calculation on these retained parents. -/ mass_eq : mass =
    PreparedRefinementMovement.movementMass parents

constructive_injectivity PrimitiveBank

namespace PrimitiveBank

variable {bank : FaceBank prepared} {differential : Fin
  genus}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons in
/-- Cache the actual shared-domain comparisons, original recast parents and their movement mass once for this standard
differential. -/
@[expose] def build (bank : FaceBanks.FaceBank prepared) (domains : DomainBanks.FaceDomainBank lifted.frames
  base.faces.regulars)
    (differential : Fin genus) : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank
      bank differential :=
  let compared := FaceBank.comparisons bank domains (PeriodMatrix.standardDifferential differential)
  let parents := Comparisons.parents (PeriodMatrix.standardDifferential differential) 0 bank.assigned compared
  ⟨domains, compared, FaceBank.comparisons_sharedDomains bank domains _, parents, rfl,
    PreparedRefinementMovement.movementMass parents, rfl⟩

/-- The comparison parents are exactly the original period initial parents recast to this standard differential. -/
theorem original_parents (comparison :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential) :
    comparison.parents = prepared.period.initial.state.parents.map (PreparedEdgeRecasting.recastCenteredEdge
      (PeriodMatrix.standardDifferential differential)) :=
  comparison.parents_eq.trans ((Comparisons.parents_eq _ _ _ _).trans (bank.parents_eq _))

/-- The retained segment bank's original parent count equals the actual comparison-parent list length. -/
theorem parentCount_eq (comparison :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential) :
    bank.segments.parentCount = comparison.parents.length := by
  rw [comparison.original_parents, Data.List.Map.length_map]
  exact bank.parentCount_eq_initial

/-- Retain both the per-segment numerical witnesses and the assembled request. Its sample is indexed by the original
cut-period initial state. -/
@[expose] def RequestedAllocation (comparison :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential) (target :
  PreparedPrimitiveChargeBounds.Coordinate) :=
  PreparedPrimitiveBatchBudget.BatchAllocation target bank.segments.parentCount bank.segments.count comparison.mass

/-- Synchronized actual local primitives on the retained shared face-domain bank at the allocation's piece target. -/
@[expose] def RequestedLocals (comparison :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential) {target :
  PreparedPrimitiveChargeBounds.Coordinate}
    (allocation :
      RequestedAllocation
      comparison target) :=
  Comparisons.Synchronized comparison.domains (PeriodMatrix.standardDifferential differential) 0
    bank.assigned comparison.compared comparison.sharedDomains allocation.pieceTarget

/-- The original finite request-part list with the allocation's retained local, coefficient and error bounds. -/
@[expose] def RequestedParts (comparison :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential) {target :
  PreparedPrimitiveChargeBounds.Coordinate}
    (allocation :
      RequestedAllocation
      comparison target) :=
  List (PreparedPrimitiveRequestBatches.RequestPart curve (PeriodMatrix.standardDifferential differential) genus
    allocation.localTarget allocation.coefficientTarget allocation.errorBound)

/-- The retained parts are exactly those assembled from the supplied synchronized local primitives and original assigned
segments. -/
@[expose] def RequestedPartsEq (comparison :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential) {target :
  PreparedPrimitiveChargeBounds.Coordinate}
    (allocation :
      RequestedAllocation
      comparison target)
    (locals : RequestedLocals
      comparison allocation)
    (parts : RequestedParts
      comparison allocation) : Prop :=
  parts = CornerRequests.parts _ _ locals.numerics allocation.piece_local_le
    allocation.piece_coefficient_le allocation.piece_error_le bank.assigned
    comparison.compared comparison.sharedDomains locals.requested locals.usesPrimitives

/-- The controlled sum request on the original period initial parents recast to the retained standard differential. -/
@[expose] def RequestedSumRequest (comparison :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential) {target :
  PreparedPrimitiveChargeBounds.Coordinate}
    (allocation :
      RequestedAllocation
      comparison target) :=
  PreparedControlledPrimitiveRequests.ControlledSumRequest
    (prepared.period.initial.state.parents.map
      (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential differential)))
    genus allocation.periodTarget

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank
/-- The assembled request's primitive sum is exactly the sum of the retained actual request parts. -/
@[expose] def RequestedPrimitiveSumEq (comparison :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential) {target :
  PreparedPrimitiveChargeBounds.Coordinate}
    (allocation :
      RequestedAllocation
      comparison target)
    (parts : RequestedParts
      comparison allocation)
    (request : RequestedSumRequest
      comparison allocation) : Prop :=
  request.primitiveSum = RequestBatch.primitiveSum parts

/-- A sufficiently late sample of the original root-safe cut-period program for this exact retained sum request. -/
@[expose] def RequestedSample (comparison :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential) {target :
  PreparedPrimitiveChargeBounds.Coordinate}
    (allocation :
      RequestedAllocation
      comparison target)
    (request : RequestedSumRequest
      comparison allocation) (minimumStage : Nat) :=
  PreparedPeriodPrimitiveRequests.PeriodSample prepared.period.initial
    (PreparedRefinementProgramCore.standardDifferentials genus)
    (PeriodMatrix.standardDifferential differential) request minimumStage

end

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank in
set_option genInjectivity false in
/-- The actual synchronized local request and an accurate late sample of the original cut-period program.

All allocations, parts, numerical values and ownership equations remain tied to the original parent and domain banks. -/
structure RequestedPeriod (comparison :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential) (target :
  PreparedPrimitiveChargeBounds.Coordinate) (minimumStage : Nat) where
  /-- The cached scalar allocation for the original target, counts and movement mass. -/ allocation :
    RequestedAllocation comparison
    target
  /-- The retained synchronized numerical witnesses on the actual original shared domains. -/ locals :
    RequestedLocals comparison
    allocation
  /-- The cached ordered original primitive request parts. -/ parts :
    RequestedParts comparison
    allocation
  /-- The cached parts are exactly those derived from the retained synchronized local witnesses. -/ parts_eq :
    RequestedPartsEq comparison
    allocation locals parts
  /-- The assembled controlled sum request on the actual original period parents. -/ request :
    RequestedSumRequest comparison
    allocation
  /-- The assembled primitive sum equals that of the exact retained original parts. -/ primitiveSum_eq :
    RequestedPrimitiveSumEq
    comparison allocation parts request
  /-- The cached Gaussian sum of actual retained local primitive readings. -/ value : Data.Gaussian.Basic.Canonical
  /-- The value cache is exactly the sum of the original request-part readings. -/ value_eq : value =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (RequestBatch.values parts)
  /-- The retained sufficiently late sample of the actual original root-safe period program. -/ sample :
    RequestedSample comparison
    allocation request minimumStage
  /-- The cached local value and original period sample satisfy the requested squared-norm target. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq (value - sample.sample) < target

constructive_injectivity RequestedPeriod

set_option genInjectivity false in
/-- All scalar allocations and the polynomial floor are cached before any numerical primitive is constructed. A larger
finite bank can select their common maximum, including a separately computed surface-refinement floor. -/
structure ScalarRequest (comparison :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential) (target :
  PreparedPrimitiveChargeBounds.Coordinate) where
  /-- The cached scalar allocation for the original target, counts and movement mass. -/ allocation :
    PreparedPrimitiveBatchBudget.BatchAllocation target bank.segments.parentCount bank.segments.count comparison.mass
  /-- The cached scalar piece budgets on every original assigned segment comparison. -/ budgets :
    PrimitiveBudgets.Budgets (PeriodMatrix.standardDifferential differential) 0 allocation.pieceTarget bank.assigned
    comparison.compared
  /-- The retained common sufficient polynomial stage selected before constructing local numerics. -/ minimum : Nat
  /-- The cached stage is exactly the maximum of the original segment budgets. -/ minimum_eq : minimum = Budgets.maximum
    (PeriodMatrix.standardDifferential differential) 0 bank.assigned comparison.compared budgets

constructive_injectivity ScalarRequest

namespace ScalarRequest

/-- Allocate the original target using the cached parent mass and counts, then cache every scalar segment budget and its
exact common polynomial floor. -/
@[expose] def build (comparison : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank
  bank differential) (target : PreparedPrimitiveChargeBounds.Coordinate) (positive : 0 < target) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank.ScalarRequest comparison target
  :=
  let allocation := BatchAllocation.build target positive bank.segments.parentCount bank.segments.count comparison.mass
    (comparison.mass_eq ▸ PreparedRefinementMovement.movementMass_nonnegative comparison.parents)
  let budgets := Budgets.build (PeriodMatrix.standardDifferential differential) 0 allocation.pieceTarget
    allocation.pieceTarget_positive bank.assigned comparison.compared
  ⟨allocation, budgets, Budgets.maximum (PeriodMatrix.standardDifferential differential) 0 bank.assigned
    comparison.compared budgets, rfl⟩

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank in
/-- Reuse the supplied shared face-primitive bank at a sufficient stage to satisfy every original segment budget. -/
@[expose] def synchronize {comparison :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential} {target :
  PreparedPrimitiveChargeBounds.Coordinate} (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank.ScalarRequest comparison target)
    {index : Nat} (later : request.minimum ≤ index)
    (numerics : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) index
      comparison.domains) :
    Comparisons.Synchronized comparison.domains (PeriodMatrix.standardDifferential differential) 0 bank.assigned
      comparison.compared
      comparison.sharedDomains request.allocation.pieceTarget :=
  Synchronized.ofShared _ _ bank.assigned comparison.compared comparison.sharedDomains request.budgets
    (Budgets.indicesBelow_of_maximum_le _ _ index bank.assigned comparison.compared request.budgets (request.minimum_eq
      ▸ later)) numerics

end ScalarRequest

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank
/-- Substitute the root name already retained by the period preparation. Using its type-level grid-vertex expression
here would reexecute the cut polygon calculation just to recover the same root-name argument. -/
@[expose] def sampleAtCachedRoot {count : Nat} {root : PreparedRefinementRootChains.Named} (cachedRoot :
  PreparedRefinementRootChains.Named) (rootEq : cachedRoot = root)
    (initial : PreparedRefinementRootEndpoints.RootClosedState curve source root) (targets : List
      (Differentials.Basic.Differential genus)) (differential : Differentials.Basic.Differential genus)
    (member : differential ∈ targets) {target : PreparedPrimitiveChargeBounds.Coordinate}
    (request : PreparedControlledPrimitiveRequests.ControlledSumRequest (initial.state.parents.map
      (PreparedEdgeRecasting.recastCenteredEdge differential)) count target) (minimumStage : Nat) :
    PreparedPeriodPrimitiveRequests.PeriodSample initial targets differential request minimumStage := by
  subst root
  exact PeriodSample.acquire initial targets differential member request minimumStage

/-- Acquire the original period sample using its already cached root owner and owner equality. -/
@[expose] def sampleAtCachedRoot_for_request {count : Nat} {root : PreparedRefinementRootChains.Named} (cachedRoot :
  PreparedRefinementRootChains.Named) (rootEq : cachedRoot = root)
    (initial : PreparedRefinementRootEndpoints.RootClosedState curve source root) (targets : List
      (Differentials.Basic.Differential genus)) (differential : Differentials.Basic.Differential genus)
    (member : differential ∈ targets) {target : PreparedPrimitiveChargeBounds.Coordinate}
    (request : PreparedControlledPrimitiveRequests.ControlledSumRequest (initial.state.parents.map
      (PreparedEdgeRecasting.recastCenteredEdge differential)) count target) (minimumStage : Nat) :
    PreparedPeriodPrimitiveRequests.PeriodSample initial targets differential request minimumStage := by
  subst root
  exact PeriodSample.acquire initial targets differential member request minimumStage

end

/-- Assemble an already synchronized request. A larger caller may supply one shared numerical bank for several cycles
and a surface without this constructor choosing a new index or rebuilding any local primitive. -/
@[expose] def ofSynchronized (comparison :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential) {target :
  PreparedPrimitiveChargeBounds.Coordinate}
    (allocation : PreparedPrimitiveBatchBudget.BatchAllocation target bank.segments.parentCount bank.segments.count
      comparison.mass)
    (locals : Comparisons.Synchronized comparison.domains (PeriodMatrix.standardDifferential differential) 0
      bank.assigned comparison.compared
      comparison.sharedDomains allocation.pieceTarget) (minimumStage : Nat) :
    RequestedPeriod comparison
      target minimumStage := by
  let requested := locals.requested
  let parts := CornerRequests.parts _ _ locals.numerics allocation.piece_local_le allocation.piece_coefficient_le
    allocation.piece_error_le
    bank.assigned comparison.compared comparison.sharedDomains requested locals.usesPrimitives
  have parentsEq : RequestBatch.parents parts = comparison.parents :=
    (CornerRequests.parts_parents _ _ _ _ _ _ _ _ _ _ _).trans comparison.parents_eq.symm
  have lengthEq : parts.length = bank.segments.count :=
    (CornerRequests.parts_length _ _ _ _ _ _ _ _ _ _ _).trans bank.segments.count_eq.symm
  have localEq : allocation.localTarget = Aggregate.perTerm allocation.periodTarget (RequestBatch.parents parts).length
    := by
    rw [parentsEq, ← comparison.parentCount_eq]
    exact allocation.localTarget_eq
  let assembled := RequestBatch.assemble parts allocation.periodTarget allocation.periodTarget_positive localEq
    comparison.mass (comparison.mass_eq.trans (congrArg PreparedRefinementMovement.movementMass parentsEq.symm))
    allocation.coefficientTarget_eq allocation.coefficientTarget_positive
  let combined := ControlledSumRequest.castParents
    assembled (parentsEq.trans comparison.original_parents)
  have primitiveEq : combined.primitiveSum = RequestBatch.primitiveSum parts :=
    ControlledSumRequest.castParents_primitiveSum assembled _
  let value := Data.Gaussian.Norm.Sum.Basic.gaussianSum (RequestBatch.values parts)
  have localError : Data.Gaussian.Norm.Basic.normSq (value - combined.primitiveSum) < allocation.periodTarget
    := by
    rw [primitiveEq]
    have bounded := RequestBatch.error_le parts
    rw [lengthEq] at bounded
    exact bounded.trans_lt allocation.error_lt
  let sample :=
    sampleAtCachedRoot_for_request
    prepared.period.closed.firstRoot prepared.period.closed.firstRoot_eq prepared.period.initial
    (PreparedRefinementProgramCore.standardDifferentials genus) (PeriodMatrix.standardDifferential differential)
    (PreparedRefinementProgramCore.standardDifferential_mem_standardDifferentials differential) combined minimumStage
  have accurate : Data.Gaussian.Norm.Basic.normSq (value - sample.sample) < target := by
    have split : value - sample.sample = (value - combined.primitiveSum) + (combined.primitiveSum - sample.sample) := by
      ring1
    rw [split]
    have bounded := Data.Gaussian.Norm.Bounds.normSq_add_le_two (value - combined.primitiveSum) (combined.primitiveSum -
      sample.sample)
    have sampleAccurate := sample.accurate
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at sampleAccurate
    have paid := Fraction.Order.Arithmetic.add_lt_add_direct
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
          decide : (0 : PreparedPrimitiveChargeBounds.Coordinate) < 2) localError)
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
          decide : (0 : PreparedPrimitiveChargeBounds.Coordinate) < 2) sampleAccurate)
    have total : 2 * allocation.periodTarget + 2 * allocation.periodTarget = target := by
      rw [allocation.periodTarget_eq]
      rw [show 2 * (target / 4) + 2 * (target / 4) = (target / 4) * 4 by ring1]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
    apply bounded.trans_lt
    calc
      2 * (Data.Gaussian.Norm.Basic.normSq (value - combined.primitiveSum) +
        Data.Gaussian.Norm.Basic.normSq (combined.primitiveSum - sample.sample)) =
          2 * Data.Gaussian.Norm.Basic.normSq (value - combined.primitiveSum) + 2 *
            Data.Gaussian.Norm.Basic.normSq (combined.primitiveSum - sample.sample) := by ring1
      _ < target := paid.trans_eq total
  exact ⟨allocation, locals, parts, rfl, combined, primitiveEq, value, rfl, sample, accurate⟩

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank in
/-- Supplied numerical data are retained exactly, not replaced by a new bank at an independently selected index. -/
@[expose] def ScalarRequest.requestWith {comparison :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential} {target :
  PreparedPrimitiveChargeBounds.Coordinate}
    (request : ScalarRequest
      comparison target) {index : Nat} (later : request.minimum ≤ index)
    (numerics : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) index
      comparison.domains)
    (minimumStage : Nat) :
      RequestedPeriod comparison
      target minimumStage :=
  comparison.ofSynchronized request.allocation (request.synchronize later numerics) minimumStage

/-- The assembled controlled sum request on the actual original period parents. -/
@[expose] def request (comparison :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential) (target :
  PreparedPrimitiveChargeBounds.Coordinate) (positive : 0 < target) (minimumStage : Nat) :
    RequestedPeriod comparison
      target minimumStage :=
  let scalar :=
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank.ScalarRequest.build comparison
    target positive
  let numerics := FacePrimitiveBank.build (PeriodMatrix.standardDifferential differential) scalar.minimum
    comparison.domains
  scalar.requestWith (Nat.le_refl _) numerics minimumStage

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank
/-- Assembly preserves the exact polynomial index of the supplied shared numerical bank. -/
theorem ScalarRequest.requestWith_index {comparison :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential} {target :
  PreparedPrimitiveChargeBounds.Coordinate}
    (request : ScalarRequest
      comparison target) {index : Nat} (later : request.minimum ≤ index)
    (numerics : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) index
      comparison.domains)
    (minimumStage : Nat) : (request.requestWith later numerics minimumStage).locals.index = index := rfl

/-- Assembly retains the supplied shared numerical bank itself under erased dependent transport. -/
theorem ScalarRequest.requestWith_numerics {comparison :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential} {target :
  PreparedPrimitiveChargeBounds.Coordinate}
    (request : ScalarRequest
      comparison target) {index : Nat} (later : request.minimum ≤ index)
    (numerics : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) index
      comparison.domains)
    (minimumStage : Nat) : HEq (request.requestWith later numerics minimumStage).locals.numerics numerics := HEq.rfl

end

/-- Assembly retains the supplied synchronized local certificate exactly. -/
theorem ofSynchronized_locals (comparison :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential) {target :
  PreparedPrimitiveChargeBounds.Coordinate}
    (allocation : PreparedPrimitiveBatchBudget.BatchAllocation target bank.segments.parentCount bank.segments.count
      comparison.mass)
    (locals : Comparisons.Synchronized comparison.domains (PeriodMatrix.standardDifferential differential) 0
      bank.assigned comparison.compared
      comparison.sharedDomains allocation.pieceTarget) (minimumStage : Nat) :
    (comparison.ofSynchronized allocation locals minimumStage).locals = locals := rfl

namespace RequestedPeriod

variable {comparison : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank
  bank differential} {target : Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds.Coordinate} {minimumStage : Nat}

/-- The comparison uses one fixed four-value bank on each face/sheet, including every repeated occurrence and its
original orientation. -/
theorem value_eq_corners (result :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank.RequestedPeriod comparison
  target minimumStage) :
    result.value = Data.Gaussian.Norm.Sum.Basic.gaussianSum (AssignedSegments.cornerIncrements
      result.locals.numerics bank.assigned) := by
  rw [result.value_eq, result.parts_eq, CornerRequests.parts_values]

/-- The retained sample is exactly the integral sample of the original prepared period program at its selected stage. -/
theorem sample_eq_program (result :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank.RequestedPeriod comparison
  target minimumStage) :
    result.sample.sample = ((prepared.program differential).integral.model result.sample.stage).integralSample := by
  rw [result.sample.sample_eq]
  exact (RootClosedState.sample_eq_flat
    prepared.period.initial (PreparedRefinementProgramCore.standardDifferentials genus)
      (PeriodMatrix.standardDifferential differential) _).symm

/-- No independently chosen surrogate period is used in the final bound. -/
theorem program_accurate (result :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank.RequestedPeriod comparison
  target minimumStage) :
    Data.Gaussian.Norm.Basic.normSq (result.value - ((prepared.program differential).integral.model
      result.sample.stage).integralSample) < target := by
  rw [← result.sample_eq_program]
  exact result.accurate

end RequestedPeriod
end PrimitiveBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
