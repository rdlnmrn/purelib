module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalExteriorProduct
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateExteriorLapRequest
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
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateExteriorLapRequest

open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

@[expose] public section

/-! The actual odd ordered ending has zero terminal product; only the lap error remains. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorBound

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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal (resplitPhysicalExteriorCorrection)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (extract mix
  extract_congr mix_reverse)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateExteriorLapRequest.ConjugatePhysicalRequest
  (exterior_component_bound)
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
    {prepared : Prepared paired}
  {preparation : NewtonPreparation
    base.bank.toBranchCellBank} {target radius : Rational}
  {grid : NewtonGrid preparation target radius}
    {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {firstIndex secondIndex : Fin genus}

namespace ConjugatePhysicalRequest

/-- The odd terminal factor vanishes on these canonical readings. -/
theorem odd_exterior_component_bound
    {first : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential firstIndex)}
    {second : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential secondIndex)}
    {error : Fraction.Rational} (request : LapRequest.ExteriorLapRequest first second error)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential firstIndex) stage
      domains}
    {rightBank : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential secondIndex) stage domains}
    (left : TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh)
    (later : request.index ≤ stage) (newSheet : Fin 2)
    (degree : curve.polynomial.natDegree = 2 * genus + 1) :
    Data.Gaussian.Norm.Basic.normSq (2 * ConjugatePhysicalRequest.exterior (paired := paired) newSheet
      (CanonicalEdgeValues.edgeValuation current.mesh left.values)
      (CanonicalEdgeValues.edgeValuation current.mesh right.values) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (current.exteriorBoundaries.map (fun word =>
          PairedIncrementArea.area (word.map (fun edge =>
            (⟨conj (CanonicalEdgeValues.edgeValuation current.mesh left.values edge),
              CanonicalEdgeValues.edgeValuation current.mesh right.values edge⟩ : Stokes.PrimitivePoint)))))) ≤
      2 * error := by
  have terminal := PhysicalExteriorProduct.product_zero_of_odd (paired := paired) grid.shrunk.included degree newSheet
    (fun edge => Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh left.values edge))
    (CanonicalEdgeValues.edgeValuation current.mesh right.values)
  have zero : Data.Gaussian.Norm.Basic.normSq (BilinearPolarization.extract (fun coefficient =>
    ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
      grid.shrunk.included current.edges current.vertices newSheet
      (BilinearPolarization.mix (fun edge => Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation
        current.mesh left.values edge))
        (CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient))) ≤ 0 := by
    exact (congrArg Data.Gaussian.Norm.Basic.normSq terminal).le
  exact (ConjugatePhysicalRequest.exterior_component_bound (paired := paired) request left right later newSheet
    zero).trans_eq (by ring1)

end ConjugatePhysicalRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorBound
