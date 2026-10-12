module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateBranchAggregate
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalConjugateRegionsComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea
import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate
import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePeriodArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateCorrections
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
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
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles

open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateBranchAggregate.PairedBranchRequests

open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate.PairedRegularRequests

open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate

open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateCorrections

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib.Data.Rat

open Purelib.Riemann.Periods

open Purelib.Topology.Mesh.RetracingWords

open Purelib.Topology.Surface.Sewing

public section

/-! The conjugate Newton surface comparison after paying terminal and connector
errors. Its actual physical exterior and sewn cut corrections remain explicit. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalPeriodComparison

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Topology.Mesh.RetracingWords (AreaTerm)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnConjugateSamples (ConjugatePair)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (extract mix)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank (CircuitPartition)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate (PairedRegularRequests)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate (PairedBranchRequests)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections (PolarizedCorrectionRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal (resplitPhysicalExteriorCorrection)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea (resplitPeriodArea resplitEndCorrection)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons (branchSheet)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
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

/-- The shared threshold is above the caller floor. Terminal and connector errors are paid without assuming any
smallness of the physical exterior. -/
theorem conjugate_physical_period_accurate (newSheet : Fin 2) (excision : Excision.AllHoleExcision grid current)
    (first : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential firstIndex))
    (second : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential secondIndex))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    let reference := fun point member => (BranchCellBank.referenceAt grid.punctured.bank.toBranchCellBank point
      member).toLoop
    let compiled := CircuitPartition.compileResplit grid.shrunk.included current.edges current.vertices
      reference (FramedBranchCellBank.baseMember base.bank) ordered.prepared.partition newSheet
    let quarterPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
    let part := Aggregate.perTerm (error / 4) 2
    let partPositive := Aggregate.perTerm_positive quarterPositive 2
    let regular := PairedRegularRequests.build first second (Aggregate.perTerm part compiled.regulars.length)
      (Aggregate.perTerm_positive partPositive _) floor compiled.regulars
    let branch := PairedBranchRequests.build bank (OrderedBranchPolygons.branchSheet ordered newSheet) first second
      (Aggregate.perTerm part excision.entries.length)
      (Aggregate.perTerm_positive partPositive _) floor excision.entries
    let corrections := PolarizedCorrectionRequest.build (paired := paired) grid.shrunk.included compiled first second
      (error / 16) (Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 16)) floor
    let threshold := max (max regular.index branch.index) (corrections.index floor)
    floor ≤ threshold ∧
    ∀ stage (leftBank : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential firstIndex) stage domains)
      (rightBank : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential secondIndex) stage domains)
      (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh) (rightReadings :
        TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh)
      (leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch leftReadings.values) (rightSurface :
        SewnPrimitiveSamples.CachedSample current.cutPolygon.patch rightReadings.values)
      (pair : SewnConjugateSamples.ConjugatePair leftSurface rightSurface),
      threshold ≤ stage →
      let regularSamples := ConjugateSamples.build leftReadings rightReadings leftSurface rightSurface pair regular
      let branchSamples := ConjugateSamples.build leftReadings rightReadings leftSurface rightSurface pair branch
      let physical := BilinearPolarization.extract (fun coefficient =>
        let value := BilinearPolarization.mix (fun edge => Data.Gaussian.Basic.conj
          (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values edge))
          (CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values) coefficient
        current.edges.chainArea current.vertices value (grid.shrunk.included.resplit base.bank.exterior
          (FramedBranchCellBank.baseMember base.bank)) newSheet +
          OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges current.vertices newSheet
            value -
          ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired) grid.shrunk.included current.edges
            current.vertices newSheet value)
      Data.Gaussian.Norm.Basic.normSq (pair.boundaryArea -
        (regularSamples.corrections + branchSamples.corrections) - (physical + physical)) < error := by
  intro reference compiled quarterPositive part partPositive regular branch corrections threshold
  constructor
  · exact (corrections.minimum_le floor).trans (Data.Nat.Order.le_max_right _ _)
  intro stage leftBank rightBank leftReadings rightReadings leftSurface rightSurface pair later regularSamples
    branchSamples physical
  let values := fun coefficient => BilinearPolarization.mix (fun edge => Data.Gaussian.Basic.conj
    (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values edge))
    (CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values) coefficient
  let geometric := pair.boundaryArea -
    (regularSamples.corrections + branchSamples.corrections)
  let uncorrected := BilinearPolarization.extract (fun coefficient =>
    current.edges.chainArea current.vertices (values coefficient) (grid.shrunk.included.resplit base.bank.exterior
      (FramedBranchCellBank.baseMember base.bank)) newSheet +
      OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges current.vertices newSheet (values
        coefficient) -
      OriginalPeriodArea.resplitEndCorrection (paired := paired) grid.shrunk.included current.edges current.vertices
        newSheet (values coefficient) -
      AreaTerm.total (values coefficient) compiled.connectorTerms)
  let delta := BilinearPolarization.extract (fun coefficient =>
    OriginalPeriodArea.resplitEndCorrection (paired := paired) grid.shrunk.included current.edges current.vertices
      newSheet (values coefficient) +
      AreaTerm.total (values coefficient) compiled.connectorTerms -
      ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired) grid.shrunk.included current.edges
        current.vertices newSheet (values coefficient))
  have regionBound : Data.Gaussian.Norm.Basic.normSq (geometric - (uncorrected + uncorrected)) < error / 4 :=
    by
    have estimate := OriginalConjugateRegionsComparison.original_conjugate_regions_accurate ordered newSheet
      (OrderedBranchPolygons.branchSheet ordered newSheet)
      excision first second (error / 4) quarterPositive floor stage leftBank rightBank
      leftReadings rightReadings leftSurface rightSurface pair ((Data.Nat.Order.le_max_left _ _).trans later)
    have read : regularSamples.polygons + branchSamples.polygons = uncorrected :=
      ConjugatePeriodArea.original_conjugate_polygons_period_area prepared newSheet excision leftReadings rightReadings
        leftSurface rightSurface pair regularSamples branchSamples
    exact (congrArg (fun polygon => Data.Gaussian.Norm.Basic.normSq (geometric - (polygon + polygon)))
      read.symm).trans_lt estimate
  have correctionBound : Data.Gaussian.Norm.Basic.normSq delta < error / 16 :=
    PolarizedCorrectionRequest.conjugate_accurate corrections reference floor leftReadings rightReadings
      ((Data.Nat.Order.le_max_right _ _).trans later)
  have twice : Data.Gaussian.Norm.Basic.normSq (delta + delta) < 4 * (error / 16) :=
    ((Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
        (Fraction.Order.Arithmetic.add_lt_add_direct correctionBound correctionBound))).trans_eq (by ring1)
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two (geometric - (uncorrected + uncorrected)) (delta +
    delta)).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct regionBound twice))
  have paid : 2 * (error / 4 + 4 * (error / 16)) = error := by
    apply Fraction.Field.mul_right_cancel_of_ne (by decide : (2 : Fraction.Rational) ≠ 0)
    calc
      _ = error / 4 * 4 + error / 16 * 16 := by ring1
      _ = error + error := by rw [Fraction.Field.div_mul_cancel_of_ne _ 4 (by decide),
        Fraction.Field.div_mul_cancel_of_ne _ 16 (by decide)]
      _ = error * 2 := by ring1
  have identity : uncorrected + delta = physical := by
    unfold uncorrected delta physical values BilinearPolarization.extract
    ring1
  have read : geometric - (physical + physical) = (geometric - (uncorrected + uncorrected)) - (delta + delta) := by
    rw [← identity]
    ring1
  exact (congrArg Data.Gaussian.Norm.Basic.normSq read).trans_lt (estimate.trans_eq paid)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalPeriodComparison
