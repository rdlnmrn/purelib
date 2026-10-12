module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorBound
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
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
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest

open Purelib.Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorBound

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Integration.Path

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

public section

/-! Acquire all odd canonical exterior lap comparisons at one coefficient-independent stage. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Data

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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (extract mix
  extract_congr mix_reverse)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorBound.ConjugatePhysicalRequest
  (odd_exterior_component_bound)
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

section ConjugatePhysicalRequest

namespace OddCanonicalExteriorRequest.ConjugatePhysicalRequest

/-- The complete original basis-pair lap requests with half the supplied pair budget. -/
@[expose] def CanonicalLapEntries
    (magnitudes : Data.Vector.DependentVector (fun row : Fin genus => MagnitudeBank.FaceMagnitudeBank domains
      (PeriodMatrix.standardDifferential row)))
    (pairTarget : Fraction.Rational) :=
  Data.Vector.DependentVector fun first : Fin genus => Data.Vector.DependentVector fun second : Fin genus =>
    LapRequest.ExteriorLapRequest (magnitudes.get first) (magnitudes.get second) (pairTarget / 2)

end OddCanonicalExteriorRequest.ConjugatePhysicalRequest

set_option genInjectivity false in
/-- Store the shared pair budget and all lap requests before reading any coefficient vector. -/
structure OddCanonicalExteriorRequest
    (magnitudes : Data.Vector.DependentVector (fun row : Fin genus => MagnitudeBank.FaceMagnitudeBank domains
      (PeriodMatrix.standardDifferential row)))
    (allowance : Fraction.Rational) (floor : Nat) where
  /-- The retained homogeneous energy allowance is strictly positive. -/ positive : 0 < allowance
  /-- The shared scalar error budget for each original basis pair. -/ pairTarget : Fraction.Rational
  /-- The pair budget is exactly the retained energy-allocation target. -/ pairTarget_eq : pairTarget =
    ConjugateRequest.energyAllowanceTarget genus allowance
  /-- The retained pair budget is strictly positive. -/ pair_positive : 0 < pairTarget
  /-- The original genus-squared contraction is paid by the squared energy allowance. -/ paid : (genus :
    Fraction.Rational)^2 * pairTarget ≤ 16 * allowance^2
  /-- The complete retained matrix of original lap requests. -/ laps :
    Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorRequest.ConjugatePhysicalRequest.CanonicalLapEntries
    magnitudes pairTarget
  /-- The cached common stage paying the requested floor and all actual lap requests. -/ index : Nat
  /-- The cached stage equals the maximum of the original floor and retained lap thresholds. -/ index_eq : index = max
    floor (laps.maximum fun _ row => row.maximum fun _ request => request.index)

constructive_injectivity OddCanonicalExteriorRequest

namespace OddCanonicalExteriorRequest
variable {magnitudes : Purelib.Data.Vector.DependentVector (fun row : Fin genus =>
  FaceMagnitudeBank domains
  (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential row))}
  {allowance : Rational} {floor : Nat}

/-- The finite family is computed once, including the caller's numerical floor. -/
@[expose] def build (magnitudes : Data.Vector.DependentVector (fun row : Fin genus => MagnitudeBank.FaceMagnitudeBank
  domains (PeriodMatrix.standardDifferential row)))
    (allowance : Fraction.Rational) (positive : 0 < allowance) (floor : Nat) :
    OddCanonicalExteriorRequest
      magnitudes allowance floor := by
  let pairTarget := ConjugateRequest.energyAllowanceTarget genus allowance
  have pairPositive : 0 < pairTarget := ConjugateRequest.energyAllowanceTarget_positive positive
  have lapPositive : 0 < pairTarget / 2 := Fraction.Order.Field.div_pos_direct pairPositive (by decide)
  let laps : Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorRequest.ConjugatePhysicalRequest.CanonicalLapEntries
    magnitudes pairTarget := DependentVector.ofFn fun first =>
    DependentVector.ofFn fun second => ExteriorLapRequest.build (magnitudes.get first) (magnitudes.get second)
      (pairTarget / 2) lapPositive
  exact ⟨positive, pairTarget, rfl, pairPositive,
    (ConjugateRequest.energyAllowanceTarget_paid positive).trans_eq (by ring1), laps,
    max floor (laps.maximum fun _ row => row.maximum fun _ request => request.index), rfl⟩

variable (request :
  OddCanonicalExteriorRequest
  magnitudes allowance floor)

/-- The original numerical floor is paid by the retained common stage. -/
theorem floor_le : floor ≤ request.index := by
  rw [request.index_eq]
  exact Nat.Order.le_max_left _ _

/-- Every basis pair uses the common retained threshold. -/
theorem pair_le (first second : Fin genus) : ((request.laps.get first).get second).index ≤ request.index := by
  rw [request.index_eq]
  exact (((request.laps.get first).get_le_maximum (fun _ request => request.index) second).trans
    (request.laps.get_le_maximum (fun _ row => row.maximum fun _ request => request.index) first)).trans
      (Nat.Order.le_max_right _ _)

/-- All later triangle readings satisfy the paid pair bound in odd degree. -/
theorem accurate (first second : Fin genus) {stage : Nat}
    {leftBank : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential first) stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential second) stage domains}
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
      request.pairTarget := by
  have bounded := ConjugatePhysicalRequest.odd_exterior_component_bound (paired := paired) ((request.laps.get first).get
    second)
    left right ((request.pair_le first second).trans later) newSheet degree
  exact bounded.trans_eq ((show 2 * (request.pairTarget / 2) = request.pairTarget / 2 * 2 by ring1).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

end OddCanonicalExteriorRequest
end ConjugatePhysicalRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton
