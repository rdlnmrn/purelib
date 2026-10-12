module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.PolarizedWordArea
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateExteriorLapRequest
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.ExteriorBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalExteriorProduct
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

public section

/-! Twice the actual conjugate exterior offset is the canonical component
polygon sum minus twice the retained terminal product, up to the lap request.
This fixes the orientation and multiplicity before the cap comparison. -/
section

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateExteriorLapRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Polynomial.Geometry.Grid.Extension
open Purelib.Riemann.Periods
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Boundary.PolarizedWordArea

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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest (ExteriorLapRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation edgeValuation_reverse)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal (resplitExteriorFactor
  resplitPhysicalExteriorCorrection)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (extract mix
  extract_congr mix_reverse)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Basic (conj)
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

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateExteriorLapRequest.ConjugatePhysicalRequest

/-- The exterior residual keeps the physical terminal product. In even degree it must still be estimated; component
closure alone does not remove it. -/
theorem exterior_component_accurate
    {first : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential firstIndex)}
    {second : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential secondIndex)}
    {error : Fraction.Rational} (request : LapRequest.ExteriorLapRequest first second error)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential firstIndex) stage
      domains}
    {rightBank : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential secondIndex) stage domains}
    (left : TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh)
    (later : request.index ≤ stage) (newSheet : Fin 2) :
    let firstValue := fun edge => Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh
      left.values edge)
    let secondValue := CanonicalEdgeValues.edgeValuation current.mesh right.values
    let components := Data.Gaussian.Norm.Sum.Basic.gaussianSum (current.exteriorBoundaries.map (fun word =>
      PairedIncrementArea.area (word.map (fun edge =>
        (⟨firstValue edge, secondValue edge⟩ : Stokes.PrimitivePoint)))))
    let factor := (⟨resplitExteriorFactor (paired := paired) grid.shrunk.included current.edges current.vertices
      newSheet firstValue,
      ExteriorTotal.resplitExteriorFactor (paired := paired) grid.shrunk.included current.edges current.vertices
        newSheet secondValue⟩ :
        Stokes.PrimitivePoint)
    let total := (⟨current.edges.chainValue current.vertices firstValue
        (grid.shrunk.included.resplit base.bank.exterior (FramedBranchCellBank.baseMember base.bank)) newSheet,
      current.edges.chainValue current.vertices secondValue
        (grid.shrunk.included.resplit base.bank.exterior (FramedBranchCellBank.baseMember base.bank)) newSheet⟩ :
          Stokes.PrimitivePoint)
    Data.Gaussian.Norm.Basic.normSq (2 * ConjugatePhysicalRequest.exterior (paired := paired) newSheet
      (CanonicalEdgeValues.edgeValuation current.mesh left.values) secondValue -
        (components - 2 * Stokes.edgeArea factor total)) ≤ error := by
  intro firstValue secondValue components factor total
  let lap := BilinearPolarization.extract fun coefficient => current.edges.chainArea current.vertices
    (BilinearPolarization.mix firstValue secondValue coefficient)
    (grid.shrunk.included.resplit base.bank.exterior (FramedBranchCellBank.baseMember base.bank)) newSheet
  have split : ConjugatePhysicalRequest.exterior (paired := paired) newSheet
      (CanonicalEdgeValues.edgeValuation current.mesh left.values) secondValue =
        lap - Stokes.edgeArea factor total := by
    have linear (area correction : Data.Gaussian.Basic.Canonical → Data.Gaussian.Basic.Canonical) :
        BilinearPolarization.extract (fun coefficient => area coefficient - correction coefficient) =
          BilinearPolarization.extract area - BilinearPolarization.extract correction := by
      unfold BilinearPolarization.extract
      ring1
    unfold ConjugatePhysicalRequest.exterior
    rw [linear]
    exact congrArg (fun correction => lap - correction)
      (PhysicalExteriorProduct.product_readback (paired := paired) (current := current)
        grid.shrunk.included newSheet firstValue secondValue)
  have comparison := CoordinateInclusion.exterior_comparison grid.shrunk.included base.bank.frame
    grid.punctured.bank.frame
    current.edges current.vertices (fun point member => (BranchCellBank.referenceAt grid.punctured.bank.toBranchCellBank
      point member).toLoop)
  have readback : lap = PairedIncrementArea.area
      ((current.edges.indexedEdges current.vertices grid.punctured.bank.exterior newSheet).map
        (fun edge => (⟨firstValue edge, secondValue edge⟩ : Stokes.PrimitivePoint))) := by
    have equal := BilinearPolarization.extract_congr (fun coefficient => comparison.areas (BilinearPolarization.mix
      firstValue secondValue coefficient)
      (BilinearPolarization.mix_reverse _ _ (fun edge => by
        dsimp only [firstValue]
        rw [CanonicalEdgeValues.edgeValuation_reverse]
        rfl) (CanonicalEdgeValues.edgeValuation_reverse current.mesh right.values) coefficient) newSheet)
    exact equal.trans (BilinearPolarization.extract_wordArea_mix _ _ _)
  have bounded := ExteriorLapRequest.conjugate_accurate request left right later newSheet
  change Data.Gaussian.Norm.Basic.normSq (_ + _ - components) ≤ error at bounded
  have rearrange : 2 * ConjugatePhysicalRequest.exterior (paired := paired) newSheet
      (CanonicalEdgeValues.edgeValuation current.mesh left.values) secondValue -
        (components - 2 * Stokes.edgeArea factor total) = lap + lap - components :=
    (congrArg (fun value => 2 * value - (components - 2 * Stokes.edgeArea factor total)) split).trans
      (by ring1)
  exact (congrArg Data.Gaussian.Norm.Basic.normSq rearrange).trans_le
    ((congrArg (fun area => Data.Gaussian.Norm.Basic.normSq (area + area - components)) readback).trans_le
      bounded)

/-- Pay the retained terminal product before comparing canonical polygons with cap polygons. Both error bounds concern
the same numerical readings. -/
theorem exterior_component_bound
    {first : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential firstIndex)}
    {second : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential secondIndex)}
    {error : Fraction.Rational} (request : LapRequest.ExteriorLapRequest first second error)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential firstIndex) stage
      domains}
    {rightBank : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential secondIndex) stage domains}
    (left : TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh)
    (later : request.index ≤ stage) (newSheet : Fin 2) {terminalError : Fraction.Rational}
    (terminal : Data.Gaussian.Norm.Basic.normSq (BilinearPolarization.extract (fun coefficient =>
      ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
      grid.shrunk.included current.edges current.vertices newSheet
      (BilinearPolarization.mix (fun edge => Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation
        current.mesh left.values edge))
        (CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient))) ≤ terminalError) :
    Data.Gaussian.Norm.Basic.normSq (2 * ConjugatePhysicalRequest.exterior (paired := paired) newSheet
      (CanonicalEdgeValues.edgeValuation current.mesh left.values)
      (CanonicalEdgeValues.edgeValuation current.mesh right.values) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (current.exteriorBoundaries.map (fun word =>
          PairedIncrementArea.area (word.map (fun edge =>
            (⟨conj (CanonicalEdgeValues.edgeValuation current.mesh left.values edge),
              CanonicalEdgeValues.edgeValuation current.mesh right.values edge⟩ : Stokes.PrimitivePoint)))))) ≤
      2 * (error + 4 * terminalError) := by
  let correction := BilinearPolarization.extract (fun coefficient => ExteriorTotal.resplitPhysicalExteriorCorrection
    (paired := paired)
    grid.shrunk.included current.edges current.vertices newSheet
    (BilinearPolarization.mix (fun edge => Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation
      current.mesh left.values edge))
      (CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient))
  let offset := 2 * ConjugatePhysicalRequest.exterior (paired := paired) newSheet
    (CanonicalEdgeValues.edgeValuation current.mesh left.values)
    (CanonicalEdgeValues.edgeValuation current.mesh right.values)
  let components := Data.Gaussian.Norm.Sum.Basic.gaussianSum (current.exteriorBoundaries.map (fun word =>
    PairedIncrementArea.area (word.map (fun edge =>
      (⟨conj (CanonicalEdgeValues.edgeValuation current.mesh left.values edge),
        CanonicalEdgeValues.edgeValuation current.mesh right.values edge⟩ : Stokes.PrimitivePoint)))))
  have lap :=
    exterior_component_accurate
    (paired := paired) request left right later newSheet
  have product := PhysicalExteriorProduct.product_readback (paired := paired) (current := current)
    grid.shrunk.included newSheet (fun edge => Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation
      current.mesh left.values edge))
    (CanonicalEdgeValues.edgeValuation current.mesh right.values)
  have first : Data.Gaussian.Norm.Basic.normSq (offset - (components - 2 * correction)) ≤ error :=
    (congrArg (fun value => Data.Gaussian.Norm.Basic.normSq (offset - (components - 2 * value)))
      product).trans_le lap
  have twice : Data.Gaussian.Norm.Basic.normSq (correction + correction) ≤ 4 * terminalError :=
    ((Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct terminal
        terminal) (by decide))).trans_eq (by ring1)
  have bounded := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two
    (offset - (components - 2 * correction)) (correction + correction)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct first
        twice) (by decide))
  exact (congrArg Data.Gaussian.Norm.Basic.normSq (show offset - components =
    (offset - (components - 2 * correction)) - (correction + correction) by ring1)).trans_le bounded

end Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateExteriorLapRequest.ConjugatePhysicalRequest

end
