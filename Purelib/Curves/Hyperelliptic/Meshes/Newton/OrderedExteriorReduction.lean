module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons
import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate
import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.NewtonRequestedCutComparison
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.LocalPairedPeriodComparison
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.CorrectionAggregate
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.HoleCancellation
public import Purelib.Riemann.RootContinuation.NewtonRetainedExteriorBound
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedLocalBoundary
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Branches.NewtonRequestedCutBudget
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.NewtonRequestedFullHoleAggregate
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Budget

open Purelib.Data.Rat.Fraction.Order

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

open Purelib

public section

/-! On the actual requested cut cache, all regular and branch/hole
corrections are paid. Only the ordered exterior expression remains beside
the determinant of the corrected resplit A/B programs. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedExteriorReduction

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} (prepared :
    PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
  {target radius : Fraction.Rational} {i j : Fin genus} {floor : Nat}

/-- The exterior expression accompanying the corrected ordered resplit period determinant.

Its two physical contributions and actual exterior correction use the same retained cut cache, ordered bank and sheet.
-/
@[expose] def exteriorPeriodResidual (newSheet : Fin 2)
    (boundary : RootContinuation.NewtonRequestedBoundary.BoundaryPreparation preparation i j target radius floor)
    {stage : Nat} {cache : PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
      boundary.domains stage}
    (readings : PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings boundary.paid.cut
      cache) : Gaussian :=
  let grid := boundary.fine.family.single.grid
  let current := boundary.lifted
  let exterior := PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
    coefficient =>
    let value := PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
      (PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.left.values)
      (PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.right.values)
      coefficient
    current.edges.chainArea current.vertices value (grid.shrunk.included.resplit base.bank.exterior
      (PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet -
      PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
        grid.shrunk.included current.edges current.vertices newSheet value)
  let physical := exterior + LocalPairedPeriodComparison.resplitWordDeterminant
    prepared (current := current) newSheet
    (PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.left.values)
      (PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.right.values)
  physical + physical + PuncturedGrid.PhysicalComponentCorrection.physicalComponentCorrection
    readings.normalized readings.neighbors readings.left readings.right .exterior

/-- Prepare a common stage bounding the original ordered exterior period residual by 180 times the target.

The retained regular, branch, hole, contact and sewing requests contribute their actual thresholds. Every later shared
cut cache preserves the same geometry and corrected period readings. -/
@[expose] def exteriorPeriodRequest (newSheet : Fin 2)
    (boundary : RootContinuation.NewtonRequestedBoundary.BoundaryPreparation preparation i j target radius floor)
      (minimum : Nat) :
    {threshold : Nat // minimum ≤ threshold ∧
      ∀ stage (cache : PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics boundary.domains
        stage)
        (readings : PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings boundary.paid.cut
          cache)
        (_cached : Branches.NewtonRequestedCutComparison.CutAnnularReadings boundary.comparison readings),
        threshold ≤ stage → Gaussian.Norm.Basic.normSq
          (OrderedExteriorReduction.exteriorPeriodResidual prepared newSheet boundary
          readings) < 180 * target} := open Algebra in by
  let grid := boundary.fine.family.single.grid
  let current := boundary.lifted
  let domains := boundary.domains
  have positive : 0 < target := (Arithmetic.mul_pos_direct boundary.fine.positive (by
      decide : (0 : Fraction.Rational) < 4)).trans_eq
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  let first := PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank.build domains
    (Periods.PeriodMatrix.standardDifferential i)
  let second := PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank.build domains
    (Periods.PeriodMatrix.standardDifferential j)
  let reference := fun point member => (PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
    grid.punctured.bank.toBranchCellBank point member).toLoop
  let compiled :=
    PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
    grid.shrunk.included current.edges current.vertices
    reference (PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
      ordered.prepared.partition newSheet
  have quarterPositive := Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  let part := Aggregate.perTerm (target / 4 / 4) 2
  have regionPositive := Field.div_pos_direct quarterPositive (by decide : (0 : Fraction.Rational) < 4)
  have partPositive := Aggregate.perTerm_positive regionPositive 2
  let regular := PairedRegularAggregate.PairedRegularRequests.build first second
    (Aggregate.perTerm part compiled.regulars.length)
    (Aggregate.perTerm_positive partPositive _) minimum compiled.regulars
  let branch := PairedBranchAggregate.PairedBranchRequests.build bank
    (OrderedBranchPolygons.branchSheet ordered newSheet) first second
    (Aggregate.perTerm part boundary.excision.entries.length)
      (Aggregate.perTerm_positive partPositive _) minimum boundary.excision.entries
  let corrections := PuncturedGrid.Inclusion.PolarizedCorrections.PolarizedCorrectionRequest.build
    (paired := paired) grid.shrunk.included compiled first second
    (target / 4 / 16) (Field.div_pos_direct quarterPositive (by decide : (0 : Fraction.Rational) < 16))
      minimum
  let contacts := Topology.Surface.Sewing.SewnPrimitiveContacts.ContactBank.build current.cutPolygon.patch.assembly
  let sewingPreparation : PuncturedGrid.SewnBilinearRequest.BilinearPreparation current.cutPolygon
    domains i j :=
    ⟨first, second, contacts, PuncturedGrid.ContactBanks.ContactPreparations.ofAssembly contacts
      (Periods.PeriodMatrix.standardDifferential i) domains,
      PuncturedGrid.ContactBanks.ContactPreparations.ofAssembly contacts
        (Periods.PeriodMatrix.standardDifferential j) domains⟩
  let sewing := PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request.build
    sewingPreparation (target / 4) quarterPositive minimum
  let localThreshold := max (max (max regular.index branch.index) (corrections.index minimum)) sewing.index
  let regularCorrection := Regular.CorrectionAggregate.correctionRequest
    sewingPreparation regular target positive minimum
  let branchHole := Branch.HoleCancellation.branchHoleRequest
    (prepared := boundary) branch sewingPreparation minimum
  let threshold := max (max localThreshold boundary.index) (max regularCorrection.val branchHole.val)
  refine ⟨threshold, regularCorrection.property.1.trans ((Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_right _
    _)), ?_⟩
  intro stage cache readings cached later
  have originalLater := (Nat.Order.le_max_left _ _).trans ((Nat.Order.le_max_left _ _).trans later)
  have boundaryLater := (Nat.Order.le_max_right _ _).trans ((Nat.Order.le_max_left _ _).trans later)
  have correctionLater := (Nat.Order.le_max_right _ _).trans later
  let regularSamples := PairedRegularAggregate.PairedRegularRequests.Samples.build
    readings.left readings.right readings.leftSurface readings.rightSurface regular
  let branchSamples := PairedBranchAggregate.PairedBranchRequests.Samples.build
    readings.left readings.right readings.leftSurface readings.rightSurface branch
  have localBound := (LocalPairedPeriodComparison.local_paired_period_accurate prepared
    newSheet boundary.excision first second target positive minimum).2
    stage cache readings.left readings.right readings.leftSurface readings.rightSurface originalLater
  have regularBound := regularCorrection.property.2 stage cache readings.left readings.right readings.leftSurface
    readings.rightSurface
    regularSamples ((Nat.Order.le_max_left _ _).trans correctionLater)
  have branchBound := branchHole.property.2 stage cache readings cached branchSamples ((Nat.Order.le_max_right _
    _).trans correctionLater)
  have boundaryBound := PuncturedGrid.SelectedLocalBoundary.local_boundary_bound
    readings ((Nat.Order.le_max_left _ _).trans boundaryLater)
  rw [PuncturedGrid.SelectedLocalBoundary.all_side_remainder_eq_physical readings] at boundaryBound
  have boundarySmall := boundaryBound.trans ((Field.divide_le_self boundary.paid.positive.le (by
      decide : (1 : Fraction.Rational) ≤ 4)).trans
    (boundary.paid.cutTarget_le.trans (Field.divide_le_self positive.le (by
        decide : (1 : Fraction.Rational) ≤ 4))))
  let triangles := FiniteSum.Fin.sumFin
    (PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea readings.left readings.right)
  let exterior := PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
    coefficient =>
    let value := PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
      (PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.left.values)
      (PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.right.values)
      coefficient
    current.edges.chainArea current.vertices value (grid.shrunk.included.resplit base.bank.exterior
      (PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet -
      PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
        grid.shrunk.included current.edges current.vertices newSheet value)
  let physical := exterior + LocalPairedPeriodComparison.resplitWordDeterminant prepared
    (current := current) newSheet
    (PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.left.values)
      (PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.right.values)
  change Gaussian.Norm.Basic.normSq (triangles - (regularSamples.corrections + branchSamples.corrections) -
    (physical + physical)) < target at localBound
  have full := (Gaussian.Norm.Bounds.normSq_sub_le_two (triangles + readings.physical)
      (triangles - (regularSamples.corrections + branchSamples.corrections) - (physical + physical))).trans_lt
    (Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      ((Arithmetic.add_le_add_direct boundarySmall (le_refl _)).trans_lt
        (Arithmetic.add_lt_add_left_direct localBound target)))
  have removed := (Gaussian.Norm.Bounds.normSq_add_le_two regularSamples.corrections
      (branchSamples.corrections + boundary.fullHoleRemainder readings)).trans_lt
    (Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Arithmetic.add_lt_add_direct regularBound branchBound))
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_two
      ((triangles + readings.physical) - (triangles - (regularSamples.corrections + branchSamples.corrections) -
        (physical + physical)))
      (regularSamples.corrections + (branchSamples.corrections + boundary.fullHoleRemainder readings))).trans_lt
    (Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Arithmetic.add_lt_add_direct full removed))
  have equal : (triangles + readings.physical) -
      (triangles - (regularSamples.corrections + branchSamples.corrections) - (physical + physical)) -
      (regularSamples.corrections + (branchSamples.corrections + boundary.fullHoleRemainder readings)) =
      OrderedExteriorReduction.exteriorPeriodResidual prepared newSheet boundary readings :=
        by
    rw [boundary.fullHoleRemainder_eq_physical readings]
    change _ = physical + physical + _
    ring1
  exact (congrArg Gaussian.Norm.Basic.normSq equal).symm.trans_lt (estimate.trans_eq (by ring1))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedExteriorReduction
