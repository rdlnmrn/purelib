module
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
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.LocalPairedPeriodComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedLocalBoundary
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
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
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Tactic.Ring
import Purelib.Data.Nat.Order

open Purelib

open Purelib.Algebra

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles

open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate

open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests

open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate

open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest

open Purelib.Data.Rat

open Purelib.Riemann.Periods

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

@[expose] public section

/-! Pay the local triangle error on the same resplit period sample.
The remaining physical side, exterior and original cut corrections are explicit. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBoundaryCorrection

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate (PairedRegularRequests)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate (PairedBranchRequests)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks (ContactPreparations)
open Purelib.Topology.Mesh.RetracingWords (AreaTerm)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (extract mix)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (ContactBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections (PolarizedCorrectionRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal (resplitPhysicalExteriorCorrection)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings (bilinearArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    (prepared : Prepared paired)
  {preparation : NewtonPreparation
    base.bank.toBranchCellBank} {target radius : Rational}
  {grid : NewtonGrid preparation target radius}
    {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {firstIndex secondIndex : Fin genus}

/-- The determinant plus its complete boundary correction is small. The correction itself still requires a geometric
cancellation estimate. -/
theorem paired_boundary_correction_accurate (cuts : RegularMeshes.CommonCuts domains) (newSheet : Fin 2) (excision :
  Excision.AllHoleExcision grid current)
    (first : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential firstIndex))
    (second : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential secondIndex))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    let reference := fun point member => (BranchCellBank.referenceAt grid.punctured.bank.toBranchCellBank point
      member).toLoop
    let compiled := CircuitPartition.compileResplit grid.shrunk.included current.edges current.vertices
      reference (FramedBranchCellBank.baseMember base.bank) ordered.prepared.partition newSheet
    let quarterPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
    let localPositive := Fraction.Order.Field.div_pos_direct quarterPositive (by decide : (0 : Fraction.Rational) < 4)
    let part := Aggregate.perTerm (error / 4 / 4 / 4) 2
    let regionPositive := Fraction.Order.Field.div_pos_direct localPositive (by decide : (0 : Fraction.Rational) < 4)
    let partPositive := Aggregate.perTerm_positive regionPositive 2
    let regular := PairedRegularRequests.build first second (Aggregate.perTerm part compiled.regulars.length)
      (Aggregate.perTerm_positive partPositive _) floor compiled.regulars
    let branch := PairedBranchRequests.build bank (OrderedBranchPolygons.branchSheet ordered newSheet) first second
      (Aggregate.perTerm part excision.entries.length)
      (Aggregate.perTerm_positive partPositive _) floor excision.entries
    let corrections := PolarizedCorrectionRequest.build (paired := paired) grid.shrunk.included compiled first second
      (error / 4 / 4 / 16) (Fraction.Order.Field.div_pos_direct localPositive (by
          decide : (0 : Fraction.Rational) < 16)) floor
    let contacts := ContactBank.build current.cutPolygon.patch.assembly
    let sewingPreparation : SewnBilinearRequest.BilinearPreparation current.cutPolygon domains firstIndex secondIndex :=
      ⟨first, second, contacts, ContactPreparations.ofAssembly contacts (PeriodMatrix.standardDifferential firstIndex)
        domains,
        ContactPreparations.ofAssembly contacts (PeriodMatrix.standardDifferential secondIndex) domains⟩
    let sewing := BilinearPreparation.Request.build sewingPreparation (error / 4 / 4) localPositive floor
    let localThreshold := max (max (max regular.index branch.index) (corrections.index floor)) sewing.index
    let cut := CutPairingRequest.build current domains cuts firstIndex secondIndex error positive floor
    let threshold := max localThreshold cut.index
    floor ≤ threshold ∧
    ∀ stage (cache : RegularMeshes.Numerics domains stage)
      (leftReadings : TrianglePrimitiveReadings.TriangleReadings (cache.get firstIndex) current.mesh) (rightReadings :
        TrianglePrimitiveReadings.TriangleReadings (cache.get secondIndex) current.mesh)
      (leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch leftReadings.values) (rightSurface :
        SewnPrimitiveSamples.CachedSample current.cutPolygon.patch rightReadings.values),
      threshold ≤ stage →
      let regularSamples := Samples.build leftReadings rightReadings leftSurface rightSurface regular
      let branchSamples := Samples.build leftReadings rightReadings leftSurface rightSurface branch
      let exterior := BilinearPolarization.extract (fun coefficient =>
        let value := BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values)
          (CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values) coefficient
        current.edges.chainArea current.vertices value (grid.shrunk.included.resplit base.bank.exterior
          (FramedBranchCellBank.baseMember base.bank)) newSheet -
          ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired) grid.shrunk.included current.edges
            current.vertices newSheet value)
      let physical := exterior + LocalPairedPeriodComparison.resplitWordDeterminant prepared (current := current)
        newSheet
        (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values)
        (CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
      let boundaryReadings := Readings.buildWith cut cache leftReadings rightReadings
      Data.Gaussian.Norm.Basic.normSq (physical + physical + (regularSamples.corrections +
        branchSamples.corrections) +
        boundaryReadings.physical) < error := by
  intro reference compiled quarterPositive localPositive part regionPositive partPositive regular branch corrections
    contacts sewingPreparation sewing localThreshold cut threshold
  constructor
  · exact cut.floor_le.trans (Data.Nat.Order.le_max_right _ _)
  intro stage cache leftReadings rightReadings leftSurface rightSurface later regularSamples branchSamples exterior
    physical boundaryReadings
  have localBound := (LocalPairedPeriodComparison.local_paired_period_accurate prepared newSheet excision first second
    (error / 4) quarterPositive floor).2 stage cache leftReadings rightReadings leftSurface rightSurface
      ((Data.Nat.Order.le_max_left _ _).trans later)
  have boundaryBound := SelectedLocalBoundary.local_boundary_bound boundaryReadings ((Data.Nat.Order.le_max_right _
    _).trans later)
  rw [SelectedLocalBoundary.all_side_remainder_eq_physical boundaryReadings] at boundaryBound
  let triangles := FiniteSum.Fin.sumFin (TriangleReadings.bilinearArea leftReadings rightReadings)
  let correction := regularSamples.corrections + branchSamples.corrections
  let sides := boundaryReadings.physical
  change Data.Gaussian.Norm.Basic.normSq (triangles - correction - (physical + physical)) < error / 4
    at localBound
  change Data.Gaussian.Norm.Basic.normSq (triangles + sides) ≤ error / 4 at boundaryBound
  change Data.Gaussian.Norm.Basic.normSq (physical + physical + correction + sides) < error
  have equal : physical + physical + correction + sides =
      (triangles + sides) - (triangles - correction - (physical + physical)) := by ring1
  rw [equal]
  have sumBound := (Fraction.Order.Arithmetic.add_le_add_direct boundaryBound (le_refl
    (Data.Gaussian.Norm.Basic.normSq (triangles - correction - (physical + physical))))).trans_lt
    (Fraction.Order.Arithmetic.add_lt_add_left_direct localBound (error / 4))
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      sumBound).trans_eq
      ((by ring1 : 2 * (error / 4 + error / 4) = error / 4 * 4).trans
        (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBoundaryCorrection
