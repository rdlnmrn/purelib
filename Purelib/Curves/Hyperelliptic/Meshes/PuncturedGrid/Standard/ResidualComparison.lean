module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
public import Purelib.Curves.Hyperelliptic.Periods.Pairing
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaAccuracy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.HandleAreaBudgets
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.NamedArea
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Budget.SynchronizedSamples
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.FamilyReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.WeightedPair
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Algebra

open Purelib.Approximation.Rational.Budget

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.NamedArea

open Purelib.Curves.Hyperelliptic.Periods

open Purelib.Data.Gaussian.Norm.Sum

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary

@[expose] public section

/-! All standard cycles contribute to the actual named first-bilinear
residual. The finite cycle count and every sampler floor are paid together. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.ResidualComparison

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Surface.Boundary.HandleAreaBudgets (HandleAreaBudget)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaAccuracy (standardPairMagnitude
  standardPairBudget standardPairRow)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.NamedArea (StandardNamedAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutChordPrograms)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods (ComponentSamples)
open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods (chordPeriods)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Riemann.Periods.PeriodMatrix (sampledMatrix)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Riemann.Integration.PreparedRefinementPrograms (rawPeriodDataOfData)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : FramedPuncturedGrid curve
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher}
  {lifted : LiftedPuncturedGrid base} {first second : Fin genus}
  {roots : Purelib.Riemann.Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank curve}
  {canonical : ∀ cycle, roots.rows cycle =
    (Purelib.Riemann.Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData curve
    branches).rows cycle}
  {source : Differential genus} {programs :
    CutChordPrograms lifted source}
  {firstComponents : ComponentSamples
    programs.programs first}
  {secondComponents : ComponentSamples
    programs.programs second}
  {segments : Purelib.Data.Vector.DependentVector (fun entry =>
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (programs.programs.programs
    entry).period)}
  {domains : FaceDomainBank lifted.frames
    base.faces.regulars}
  {minimum numericalFloor : Nat} {extraPoints : List Canonical}
  {cutTarget target : Rational} {cutFloor : Nat}
  {cut : CutPairingRequest lifted domains first
    second cutTarget cutFloor}
  {stage : Nat} {cache : Numerics
    domains stage}

/-- The retained handle-area budget for one standard cycle with its allocated share of the complete residual target. -/
def CycleBudget (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve)
    (first second cycle : Fin genus) (target : Fraction.Rational) :=
  HandleAreaBudgets.HandleAreaBudget (PairedAreaAccuracy.standardPairMagnitude
    (PreparedRefinementPrograms.rawPeriodDataOfData curve branches) first second cycle) 1
    (Aggregate.perTerm target genus)

/-- Allocate the original cycle budgets using the actual standard-pair period magnitude bounds. -/
def budgets (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve)
    (first second : Fin genus) (target : Fraction.Rational) (positive : 0 < target) :
    Data.Vector.DependentVector (fun cycle =>
      CycleBudget curve branches first second
      cycle target) :=
  DependentVector.ofFn fun cycle => PairedAreaAccuracy.standardPairBudget
    (PreparedRefinementPrograms.rawPeriodDataOfData curve branches) first second cycle
    (Aggregate.perTerm target genus) (Aggregate.perTerm_positive positive genus)

variable {allocation : Purelib.Data.Vector.DependentVector (fun cycle =>
  CycleBudget curve branches first second
  cycle target)}

/-- The actual paired standard-cycle readbacks on the shared cut-area triangle bank and retained row budgets. -/
def CycleReadings (cycle : Fin genus) :=
  PairedAreaReadings
    (TourChordPeriods.chordPeriods (PairedAreaAccuracy.standardPairRow lifted cycle (roots.rows cycle) (canonical
      cycle)).span programs firstComponents)
    (TourChordPeriods.chordPeriods (PairedAreaAccuracy.standardPairRow lifted cycle (roots.rows cycle) (canonical
      cycle)).span programs secondComponents)
    segments domains minimum numericalFloor (allocation.get cycle).rowTarget (allocation.get cycle).rowTarget
      extraPoints cut cache

/-- Two retained triangle readers on the same original numerical bank have identical actual values. -/
private theorem shared_triangle_values {differential : Fin genus}
    (left right : TrianglePrimitiveReadings.TriangleReadings (cache.get differential) lifted.mesh) : left.values =
      right.values := by
  apply Data.Vector.Basic.vector_ext
  intro triangle
  let face : Fin base.faces.regulars.length := ⟨triangle.val / 4, by
    have bound := triangle.isLt.trans_eq lifted.mesh.faceCount
    omega⟩
  let sheet : Fin 2 := ⟨(triangle.val % 4) / 2, by omega⟩
  let upper : Bool := decide (triangle.val % 2 = 1)
  have decomposition : lifted.mesh.triangleIndex face sheet upper = triangle := by
    apply Fin.ext
    change 4 * (triangle.val / 4) + 2 * ((triangle.val % 4) / 2) +
      (if decide (triangle.val % 2 = 1) then 1 else 0) = triangle.val
    by_cases odd : triangle.val % 2 = 1
    · rewrite [decide_eq_true odd]
      change 4 * (triangle.val / 4) + 2 * ((triangle.val % 4) / 2) + 1 = triangle.val
      omega
    · rewrite [decide_eq_false odd]
      change 4 * (triangle.val / 4) + 2 * ((triangle.val % 4) / 2) + 0 = triangle.val
      omega
  rw [← decomposition, left.values_eq, right.values_eq]

open Purelib.Topology.Surface.Sewing.SewingRetraction in
/-- The actual standard A/B determinant read from the supplied cut-surface object. -/
def cycleArea (area : CutPairingRequest.Readings cut cache) (cycle : Fin genus) : Gaussian :=
  let row := PairedAreaAccuracy.standardPairRow lifted cycle (roots.rows cycle) (canonical cycle)
  let left := CanonicalEdgeValues.edgeValuation lifted.mesh area.left.values
  let right := CanonicalEdgeValues.edgeValuation lifted.mesh area.right.values
  Stokes.edgeArea (⟨wordValue left row.pair.aFaces.geometry.indexed, wordValue right row.pair.aFaces.geometry.indexed⟩ :
    PrimitivePoint)
    (⟨wordValue left row.pair.bFaces.geometry.indexed, wordValue right row.pair.bFaces.geometry.indexed⟩ :
      PrimitivePoint)

/-- The standard cycle area is identical for two cut readings on the same original numerical bank. -/
private theorem cycleArea_eq (left right : CutPairingRequest.Readings cut cache) (cycle : Fin genus) :
    cycleArea (roots := roots) (canonical
      := canonical) left cycle = cycleArea
      (roots := roots) (canonical := canonical) right cycle := by
  have leftEq := shared_triangle_values left.left
    right.left
  have rightEq := shared_triangle_values
    left.right right.right
  unfold cycleArea
  rw [leftEq, rightEq]

/-- The complete named/model comparison requests on the actual retained standard-cycle readings. -/
def Requests (readings : Data.Vector.DependentVector (fun cycle =>
  CycleReadings (roots := roots) (canonical :=
  canonical)
    (firstComponents := firstComponents) (secondComponents := secondComponents) (segments := segments)
    (minimum := minimum) (numericalFloor := numericalFloor) (extraPoints := extraPoints) (cut := cut) (cache := cache)
    (allocation := allocation) cycle)) (namedFloor : Nat) :=
  Data.Vector.DependentVector fun cycle => NamedArea.StandardNamedAreaRequest
    (PreparedRefinementPrograms.rawPeriodDataOfData curve branches) first second cycle
    (allocation.get cycle) namedFloor
    (max (readings.get cycle).left.readings.standard.original.comparison.stage
      (readings.get cycle).right.readings.standard.original.comparison.stage)

/-- Build every original standard-cycle comparison with the supplied named floor and its actual model threshold. -/
def requests (readings : Data.Vector.DependentVector (fun cycle =>
  CycleReadings (roots := roots) (canonical :=
  canonical)
    (firstComponents := firstComponents) (secondComponents := secondComponents) (segments := segments)
    (minimum := minimum) (numericalFloor := numericalFloor) (extraPoints := extraPoints) (cut := cut) (cache := cache)
    (allocation := allocation) cycle)) (namedFloor : Nat) :
      Requests readings namedFloor :=
  DependentVector.ofFn fun cycle => StandardNamedAreaRequest.build (PreparedRefinementPrograms.rawPeriodDataOfData curve
    branches)
    first second cycle (allocation.get cycle) namedFloor
    (max (readings.get cycle).left.readings.standard.original.comparison.stage
      (readings.get cycle).right.readings.standard.original.comparison.stage)

/-- A quarter of a positive rational is at most the original value. -/
private theorem quarter_le {value : Fraction.Rational} (positive : 0 < value) : value / 4 ≤ value := by
  apply (Fraction.Order.Field.div_le_iff_pos (by decide)).mpr
  exact (show value = value * 1 by ring1).le.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide : (1 : Fraction.Rational) ≤ 4) positive.le)

/-- The sum of actual standard-cycle surface areas approximates the synchronized public named period-pairing residual.
-/
def Accurate (area : CutPairingRequest.Readings cut cache) (namedStage : Nat) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin
    (cycleArea (roots := roots) (canonical :=
    canonical) area) -
    (Pairing.synchronizedPeriodPairingResidual (PreparedRefinementPrograms.rawPeriodDataOfData curve branches) first
      second).sample namedStage) < target

/-- All standard rows are evaluated on the supplied cut-surface object. Their exact cached readbacks, not equality of
stage numbers, identify the triangle values. No per-cycle accuracy hypothesis is supplied. -/
theorem accurate (readings : Data.Vector.DependentVector (fun cycle =>
  CycleReadings (roots := roots) (canonical :=
  canonical)
    (firstComponents := firstComponents) (secondComponents := secondComponents) (segments := segments)
    (minimum := minimum) (numericalFloor := numericalFloor) (extraPoints := extraPoints) (cut := cut) (cache := cache)
    (allocation := allocation) cycle)) (area : CutPairingRequest.Readings cut cache) (positive : 0 < target) (namedFloor
      : Nat) :
    let requested := requests readings namedFloor
    ∀ namedStage, requested.maximum (fun _ request => request.namedIndex) ≤ namedStage →
      Accurate (roots := roots) (canonical :=
        canonical) (target := target) area namedStage := by
  intro requested namedStage later
  let data := PreparedRefinementPrograms.rawPeriodDataOfData curve branches
  let a := PeriodMatrix.sampledMatrix data.aMatrix namedStage
  let b := PeriodMatrix.sampledMatrix data.bMatrix namedStage
  let error := fun cycle => cycleArea (roots :=
    roots) (canonical := canonical) area cycle -
    (a first cycle * b second cycle - b first cycle * a second cycle)
  have each (cycle : Fin genus) : Data.Gaussian.Norm.Basic.normSq (error cycle) ≤ Aggregate.perTerm target
    genus := by
    have cycleLater := (requested.get_le_maximum (fun _ request => request.namedIndex) cycle).trans later
    dsimp only [requested, requests] at cycleLater
    rw [DependentVector.ofFn_get] at cycleLater
    have bound := PairedAreaReadings.named_standard_area_accurate (roots.rows cycle) (canonical cycle)
      (allocation.get cycle) (readings.get cycle) namedFloor namedStage cycleLater
    have same := cycleArea_eq (roots := roots)
      (canonical := canonical) area (readings.get cycle).area cycle
    have transported := (congrArg (fun value => Data.Gaussian.Norm.Basic.normSq (value -
      (a first cycle * b second cycle - b first cycle * a second cycle))) same).trans_lt bound
    exact transported.le.trans (quarter_le
      (Aggregate.perTerm_positive positive genus))
  have estimate := Indexed.normSq_sumFin_le error _ each
  have paid := Aggregate.count_mul_perTerm_lt positive genus
  have strict : Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin error) < target := estimate.trans_lt
    ((show (genus : Fraction.Rational) ^ 2 * Aggregate.perTerm target genus =
      (genus : Fraction.Rational) * ((genus : Fraction.Rational) * Aggregate.perTerm target genus) by ring1).trans_lt
        paid)
  dsimp only [Accurate]
  rw [Pairing.synchronizedPeriodPairingResidual_sample]
  exact (congrArg Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin_sub _ _)).symm.trans_lt strict

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.ResidualComparison
