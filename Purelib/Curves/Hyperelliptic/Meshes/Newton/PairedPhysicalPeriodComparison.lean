module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
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
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedPeriodArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Basic
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
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

open Purelib

public section

/-! The paired Newton surface comparison after paying terminal and connector
errors. Its actual physical exterior and sewn cut corrections remain explicit. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedPhysicalPeriodComparison

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} (prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {firstIndex secondIndex : Fin genus}

/-- The shared threshold is above the caller floor. Terminal and connector
errors are paid without assuming any smallness of the physical exterior. -/
theorem paired_physical_period_accurate (newSheet : Fin 2) (excision :
  Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid current)
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential firstIndex))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential secondIndex))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    let reference := fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
      grid.shrunk.included current.edges current.vertices
      reference (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
        ordered.prepared.partition newSheet
    let quarterPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
    let part := Rational.Budget.Aggregate.perTerm (error / 4) 2
    let partPositive := Rational.Budget.Aggregate.perTerm_positive quarterPositive 2
    let regular := Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.build first second
      (Rational.Budget.Aggregate.perTerm part compiled.regulars.length)
      (Rational.Budget.Aggregate.perTerm_positive partPositive _) floor compiled.regulars
    let branch := Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.build bank
      (Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.branchSheet ordered newSheet) first second
      (Rational.Budget.Aggregate.perTerm part excision.entries.length)
      (Rational.Budget.Aggregate.perTerm_positive partPositive _) floor excision.entries
    let corrections :=
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections.PolarizedCorrectionRequest.build (paired :=
      paired) grid.shrunk.included compiled first second
      (error / 16) (Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 16)) floor
    let threshold := max (max regular.index branch.index) (corrections.index floor)
    floor ≤ threshold ∧
    ∀ stage (leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential firstIndex) stage domains)
      (rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
        (Periods.PeriodMatrix.standardDifferential secondIndex) stage domains)
      (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank
        current.mesh) (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
        rightBank current.mesh)
      (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
        leftReadings.values) (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample
        current.cutPolygon.patch rightReadings.values),
      threshold ≤ stage →
      let regularSamples := Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.Samples.build
        leftReadings rightReadings leftSurface rightSurface regular
      let branchSamples := Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.Samples.build
        leftReadings rightReadings leftSurface rightSurface branch
      let physical := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
        coefficient =>
        let value := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values)
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
            coefficient
        current.edges.chainArea current.vertices value (grid.shrunk.included.resplit base.bank.exterior
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet +
          Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges
            current.vertices newSheet value -
          Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection (paired :=
            paired) grid.shrunk.included current.edges current.vertices newSheet value)
      Data.Gaussian.Norm.Basic.normSq (Topology.Polygon.Stokes.edgeListArea
        (Hyperelliptic.Meshes.Newton.Regular.PairedRegion.pairedValues leftSurface rightSurface)
        current.cutPolygon.patch.cut.boundary -
        (regularSamples.corrections + branchSamples.corrections) - (physical + physical)) < error := by
  intro reference compiled quarterPositive part partPositive regular branch corrections threshold
  constructor
  · exact (corrections.minimum_le floor).trans (Data.Nat.Order.le_max_right _ _)
  intro stage leftBank rightBank leftReadings rightReadings leftSurface rightSurface later regularSamples branchSamples
    physical
  let values := fun coefficient => Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values)
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values) coefficient
  let geometric := Topology.Polygon.Stokes.edgeListArea (Hyperelliptic.Meshes.Newton.Regular.PairedRegion.pairedValues
    leftSurface rightSurface) current.cutPolygon.patch.cut.boundary -
    (regularSamples.corrections + branchSamples.corrections)
  let uncorrected := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
    coefficient =>
    current.edges.chainArea current.vertices (values coefficient) (grid.shrunk.included.resplit base.bank.exterior
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet +
      Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges
        current.vertices newSheet (values coefficient) -
      Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitEndCorrection (paired := paired) grid.shrunk.included
        current.edges current.vertices newSheet (values coefficient) -
      Topology.Mesh.RetracingWords.AreaTerm.total (values coefficient) compiled.connectorTerms)
  let delta := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient
    =>
    Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitEndCorrection (paired := paired) grid.shrunk.included
      current.edges current.vertices newSheet (values coefficient) +
      Topology.Mesh.RetracingWords.AreaTerm.total (values coefficient) compiled.connectorTerms -
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
        grid.shrunk.included current.edges current.vertices newSheet (values coefficient))
  have regionBound : Data.Gaussian.Norm.Basic.normSq (geometric - (uncorrected + uncorrected)) < error / 4 :=
    Hyperelliptic.Meshes.Newton.PairedPeriodArea.original_paired_period_area_accurate prepared newSheet excision first
      second (error / 4) quarterPositive floor
      stage leftBank rightBank leftReadings rightReadings leftSurface rightSurface ((Data.Nat.Order.le_max_left _
        _).trans later)
  have correctionBound : Data.Gaussian.Norm.Basic.normSq delta < error / 16 :=
    corrections.accurate reference floor leftReadings rightReadings ((Data.Nat.Order.le_max_right _ _).trans later)
  have twice : Data.Gaussian.Norm.Basic.normSq (delta + delta) < 4 * (error / 16) :=
    ((Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
        (Fraction.Order.Arithmetic.add_lt_add_direct correctionBound correctionBound))).trans_eq (by ring1)
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_two (geometric - (uncorrected + uncorrected)) (delta +
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
    unfold uncorrected delta physical values
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract
    ring1
  have read : geometric - (physical + physical) = (geometric - (uncorrected + uncorrected)) - (delta + delta) := by
    rw [← identity]
    ring1
  exact (congrArg Data.Gaussian.Norm.Basic.normSq read).trans_lt (estimate.trans_eq paid)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedPhysicalPeriodComparison
