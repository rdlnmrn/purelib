module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedRegion
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedPhysicalPeriodComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Riemann.Periods.BilinearBoundaryReadback
import Init.Prelude
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
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles

open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate

open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests

open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate

open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular

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

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest

open Purelib.Data.Rat

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.Bilinear.Samples
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear

open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

public section

open Purelib.Data

/-! The resplit period comparison on the actual local triangle wedges.
A shared sewing request transports the paired cut boundary without removing
its retained correction terms. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.LocalPairedPeriodComparison

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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks (ContactPreparations)
open Purelib.Topology.Mesh.RetracingWords (AreaTerm)
open Purelib.Topology.Polygon.Stokes (OrientedEdge edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (extract mix)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (ContactBank)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections (PolarizedCorrectionRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedRegion (pairedValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal (resplitPhysicalExteriorCorrection)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea (resplitPeriodArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings (bilinearArea)
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

/-- The determinant of the actual resplit corrected A/B word readings. -/
@[expose] def resplitWordDeterminant (newSheet : Fin 2)
    (first second : Stokes.OrientedEdge current.vertices.count → Data.Gaussian.Basic.Canonical) : Gaussian :=
  FiniteSum.Fin.sumFin (fun index : Fin genus =>
    SewingRetraction.wordValue first (current.edges.indexedEdges current.vertices
      (grid.shrunk.included.resplit (prepared.aWalk index).closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet)
        *
    SewingRetraction.wordValue second (current.edges.indexedEdges current.vertices
      (grid.shrunk.included.resplit (prepared.bWalk index).closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet)
        -
    SewingRetraction.wordValue first (current.edges.indexedEdges current.vertices
      (grid.shrunk.included.resplit (prepared.bWalk index).closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet)
        *
    SewingRetraction.wordValue second (current.edges.indexedEdges current.vertices
      (grid.shrunk.included.resplit (prepared.aWalk index).closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet))

/-- Polarization of the original resplit period area is the determinant of its actual corrected A/B word readings. -/
theorem extract_resplitPeriodArea (newSheet : Fin 2)
    (first second : Stokes.OrientedEdge current.vertices.count → Data.Gaussian.Basic.Canonical) :
    BilinearPolarization.extract (fun coefficient =>
      Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included
      current.edges current.vertices newSheet
      (BilinearPolarization.mix first second coefficient)) =
        resplitWordDeterminant prepared (current
        := current) newSheet first second := by
  unfold OriginalPeriodArea.resplitPeriodArea
    resplitWordDeterminant
  rw [BilinearPolarization.extract_sum]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  exact (BilinearPolarization.extract_congr (fun coefficient => by
    rw [BilinearPolarization.word_mix, BilinearPolarization.word_mix]
    rfl)).trans
      (BilinearPolarization.extract_area _ _ _ _)

/-- The physical-period and sewing requests share the same magnitude banks, triangle readings and sewn surfaces. All
original cut corrections survive. -/
theorem local_paired_period_accurate (newSheet : Fin 2) (excision : Excision.AllHoleExcision grid current)
    (first : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential firstIndex))
    (second : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential secondIndex))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    let reference := fun point member => (BranchCellBank.referenceAt grid.punctured.bank.toBranchCellBank point
      member).toLoop
    let compiled := CircuitPartition.compileResplit grid.shrunk.included current.edges current.vertices
      reference (FramedBranchCellBank.baseMember base.bank) ordered.prepared.partition newSheet
    let quarterPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
    let part := Aggregate.perTerm (error / 4 / 4) 2
    let regionPositive := Fraction.Order.Field.div_pos_direct quarterPositive (by decide : (0 : Fraction.Rational) < 4)
    let partPositive := Aggregate.perTerm_positive regionPositive 2
    let regular := PairedRegularRequests.build first second (Aggregate.perTerm part compiled.regulars.length)
      (Aggregate.perTerm_positive partPositive _) floor compiled.regulars
    let branch := PairedBranchRequests.build bank (OrderedBranchPolygons.branchSheet ordered newSheet) first second
      (Aggregate.perTerm part excision.entries.length)
      (Aggregate.perTerm_positive partPositive _) floor excision.entries
    let corrections := PolarizedCorrectionRequest.build (paired := paired) grid.shrunk.included compiled first second
      (error / 4 / 16) (Fraction.Order.Field.div_pos_direct quarterPositive (by decide : (0 : Fraction.Rational) < 16))
        floor
    let contacts := ContactBank.build current.cutPolygon.patch.assembly
    let sewingPreparation : SewnBilinearRequest.BilinearPreparation current.cutPolygon domains firstIndex secondIndex :=
      ⟨first, second, contacts, ContactPreparations.ofAssembly contacts (PeriodMatrix.standardDifferential firstIndex)
        domains,
        ContactPreparations.ofAssembly contacts (PeriodMatrix.standardDifferential secondIndex) domains⟩
    let sewing := BilinearPreparation.Request.build sewingPreparation (error / 4) quarterPositive floor
    let threshold := max (max (max regular.index branch.index) (corrections.index floor)) sewing.index
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
      let physical := exterior + resplitWordDeterminant
        prepared (current := current) newSheet
        (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values)
        (CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
      Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (TriangleReadings.bilinearArea leftReadings
        rightReadings) -
        (regularSamples.corrections + branchSamples.corrections) - (physical + physical)) < error := by
  intro reference compiled quarterPositive part regionPositive partPositive regular branch corrections contacts
    sewingPreparation sewing threshold
  constructor
  · exact sewing.floor_le.trans (Nat.Order.le_max_right _ _)
  intro stage cache leftReadings rightReadings leftSurface rightSurface later regularSamples branchSamples exterior
    physical
  let boundary := Stokes.edgeListArea (PairedRegion.pairedValues leftSurface rightSurface)
    current.cutPolygon.patch.cut.boundary
  let cutCorrection := regularSamples.corrections + branchSamples.corrections
  let bilinear := Bilinear.build leftSurface rightSurface
  let values := fun coefficient => BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation current.mesh
    leftReadings.values)
    (CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values) coefficient
  have physicalRead : BilinearPolarization.extract (fun coefficient =>
      current.edges.chainArea current.vertices (values coefficient) (grid.shrunk.included.resplit base.bank.exterior
        (FramedBranchCellBank.baseMember base.bank)) newSheet +
        OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges current.vertices newSheet
          (values coefficient) -
        ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired) grid.shrunk.included current.edges
          current.vertices newSheet (values coefficient)) = physical := by
    calc
      _ = exterior + BilinearPolarization.extract (fun coefficient => OriginalPeriodArea.resplitPeriodArea prepared
        grid.shrunk.included current.edges current.vertices newSheet (values coefficient)) := by
        unfold exterior values BilinearPolarization.extract
        ring1
      _ = physical := congrArg (exterior + ·)
        (extract_resplitPeriodArea prepared newSheet
        (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values) (CanonicalEdgeValues.edgeValuation
          current.mesh rightReadings.values))
  have periodBound : Data.Gaussian.Norm.Basic.normSq (boundary - cutCorrection - (physical + physical)) < error
    / 4 := by
    have bound := (PairedPhysicalPeriodComparison.paired_physical_period_accurate prepared newSheet excision first
      second (error / 4) quarterPositive floor).2
      stage (cache.get firstIndex) (cache.get secondIndex) leftReadings rightReadings leftSurface rightSurface
        ((Nat.Order.le_max_left _ _).trans later)
    exact (congrArg (fun value => Data.Gaussian.Norm.Basic.normSq (boundary - cutCorrection - (value + value)))
      physicalRead.symm).trans_lt bound
  have sewn := sewing.accurate ((Nat.Order.le_max_right _ _).trans later) leftReadings rightReadings bilinear
  have boundaryRead : bilinear.boundaryArea = boundary :=
    BilinearBoundaryReadback.boundary_eq_raw bilinear
  rw [boundaryRead] at sewn
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two (boundary - cutCorrection - (physical + physical))
    (boundary - FiniteSum.Fin.sumFin (TriangleReadings.bilinearArea leftReadings rightReadings))).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
        (Fraction.Order.Arithmetic.add_lt_add_direct periodBound sewn))
  have read : FiniteSum.Fin.sumFin (TriangleReadings.bilinearArea leftReadings rightReadings) - cutCorrection -
    (physical + physical) =
      (boundary - cutCorrection - (physical + physical)) - (boundary - FiniteSum.Fin.sumFin
        (TriangleReadings.bilinearArea leftReadings rightReadings)) := by ring1
  exact (congrArg Data.Gaussian.Norm.Basic.normSq read).trans_lt (estimate.trans_eq
    ((by ring1 : 2 * (error / 4 + error / 4) = error / 4 * 4).trans (Fraction.Field.div_mul_cancel_of_ne _ _ (by
      decide))))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.LocalPairedPeriodComparison
