module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Program.Gaussian.Basic

import Purelib.CCL.Calculus.WeightedAggregateBudget
import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Purelib.Topology.Surface.Boundary.HandleAreaBudgets
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaAccuracy
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Budget.SynchronizedSamples
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.WeightedPair
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Program.Gaussian.Name
import Purelib.LinearAlgebra.Matrix.Basic
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
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Rational.Budget

open Purelib.CCL.Calculus

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaAccuracy

open Purelib.Data.Rat

open Purelib.Integration

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.PeriodMatrix

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Boundary.HandleAreaBounds

open Purelib.Topology.Surface.Sewing

@[expose] public section

/-! The standard area comparison reaches the public named-matrix sampler,
whose selected model indices need not equal the surface comparison index. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.NamedArea
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Surface.Boundary.HandleAreaBudgets (HandleAreaBudget)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Periods.PeriodMatrix (PeriodData sampledMatrix sampledMatrix_apply)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaAccuracy (standardPairMagnitude
  StandardAreaAccurate)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaAccuracy (standardPairRow)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutChordPrograms)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods (ComponentSamples)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods (ChordPeriods)
open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Riemann.Integration.PreparedRefinementPrograms (rawPeriodDataOfData)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

/-- An operational comparison between a retained program's public named samples and its actual model samples. -/
def PeriodSampleComparison (program : Program.Gaussian.Basic.RefinementProgram)
    (namedFloor modelFloor : Nat) (error : Fraction.Rational) :=
  Gaussian.Equivalence.Comparison
    (Sampling.approximation program.output.name) program.approximation namedFloor modelFloor error

set_option genInjectivity false in
/-- The four actual named/model comparisons for a standard A/B determinant.

Both differential rows share the retained handle-area budget while preserving separate named and model floors. -/
structure StandardNamedAreaRequest {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve) (first second cycle : Fin genus)
    {target : Fraction.Rational} (budget : HandleAreaBudgets.HandleAreaBudget (PairedAreaAccuracy.standardPairMagnitude
      data first second cycle) 1 target)
    (namedFloor modelFloor : Nat) where
  /-- The actual named/model comparison for the first differential's A period. -/ aLeft :
    PeriodSampleComparison (data.aProgram first
    cycle).integral namedFloor modelFloor budget.rowTarget
  /-- The actual named/model comparison for the second differential's A period. -/ aRight :
    PeriodSampleComparison (data.aProgram second
    cycle).integral namedFloor modelFloor budget.rowTarget
  /-- The actual named/model comparison for the first differential's B period. -/ bLeft :
    PeriodSampleComparison (data.bProgram first
    cycle).integral namedFloor modelFloor budget.rowTarget
  /-- The actual named/model comparison for the second differential's B period. -/ bRight :
    PeriodSampleComparison (data.bProgram second
    cycle).integral namedFloor modelFloor budget.rowTarget

constructive_injectivity StandardNamedAreaRequest

namespace StandardNamedAreaRequest
variable {genus : Nat} {curve : HyperellipticCurve genus} {data :
  PeriodData curve}
  {first second cycle : Fin genus} {target : Rational}
  {budget : HandleAreaBudget
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaAccuracy.standardPairMagnitude data first
    second cycle) 1 target}
  {namedFloor modelFloor : Nat}

/-- Prepare all four original named/model comparisons using the retained row budget and separate stage floors. -/
def build (data : PeriodMatrix.PeriodData curve) (first second cycle : Fin genus)
    (budget : HandleAreaBudgets.HandleAreaBudget (PairedAreaAccuracy.standardPairMagnitude data first second cycle) 1
      target)
    (namedFloor modelFloor : Nat) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.NamedArea.StandardNamedAreaRequest data first second cycle
      budget namedFloor modelFloor :=
  ⟨(Equivalent.toNamed_sampling (data.aProgram first cycle).integral.approximation).compare
      namedFloor modelFloor budget.rowTarget budget.row_positive,
   (Equivalent.toNamed_sampling (data.aProgram second cycle).integral.approximation).compare
      namedFloor modelFloor budget.rowTarget budget.row_positive,
   (Equivalent.toNamed_sampling (data.bProgram first cycle).integral.approximation).compare
      namedFloor modelFloor budget.rowTarget budget.row_positive,
   (Equivalent.toNamed_sampling (data.bProgram second cycle).integral.approximation).compare
      namedFloor modelFloor budget.rowTarget budget.row_positive⟩

/-- The maximum named-sample stage requested by the four retained comparisons. -/
def namedIndex (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.NamedArea.StandardNamedAreaRequest data
  first second cycle budget namedFloor modelFloor) : Nat :=
  max (max request.aLeft.leftIndex request.aRight.leftIndex) (max request.bLeft.leftIndex request.bRight.leftIndex)

/-- The maximum model-sample stage requested by the four retained comparisons. -/
def modelIndex (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.NamedArea.StandardNamedAreaRequest data
  first second cycle budget namedFloor modelFloor) : Nat :=
  max (max request.aLeft.rightIndex request.aRight.rightIndex) (max request.bLeft.rightIndex request.bRight.rightIndex)

/-- The original model floor is paid by the retained common model index. -/
theorem modelFloor_le (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.NamedArea.StandardNamedAreaRequest
  data first second cycle budget namedFloor modelFloor) :
    modelFloor ≤ request.modelIndex :=
  request.aLeft.right_ge.trans ((Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _))

/-- The original named floor is paid by the retained common named index. -/
theorem namedFloor_le (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.NamedArea.StandardNamedAreaRequest
  data first second cycle budget namedFloor modelFloor) :
    namedFloor ≤ request.namedIndex :=
  request.aLeft.left_ge.trans ((Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _))

/-- The public named A/B determinant approximates the original model determinant at independently supplied stages. -/
def AreaAccurate (budget : HandleAreaBudgets.HandleAreaBudget (PairedAreaAccuracy.standardPairMagnitude data first
  second cycle) 1 target)
    (namedStage modelStage : Nat) : Prop :=
  let a := PeriodMatrix.sampledMatrix data.aMatrix namedStage
  let b := PeriodMatrix.sampledMatrix data.bMatrix namedStage
  Data.Gaussian.Norm.Basic.normSq ((a first cycle * b second cycle - b first cycle * a second cycle) -
    (((data.aProgram first cycle).integral.model modelStage).integralSample *
      ((data.bProgram second cycle).integral.model modelStage).integralSample -
     ((data.bProgram first cycle).integral.model modelStage).integralSample *
      ((data.aProgram second cycle).integral.model modelStage).integralSample)) < budget.handleTarget

/-- Each public sample is compared to a common later raw model through the retained operational comparison, not by
identifying their indices. -/
theorem area_accurate (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.NamedArea.StandardNamedAreaRequest
  data first second cycle budget namedFloor modelFloor)
    {namedStage modelStage : Nat} (namedLater : request.namedIndex ≤ namedStage) (modelLater : request.modelIndex ≤
      modelStage) :
    AreaAccurate budget namedStage
      modelStage := by
  let a : PrimitivePoint := ⟨((data.aProgram first cycle).integral.model modelStage).integralSample,
    ((data.aProgram second cycle).integral.model modelStage).integralSample⟩
  let b : PrimitivePoint := ⟨((data.bProgram first cycle).integral.model modelStage).integralSample,
    ((data.bProgram second cycle).integral.model modelStage).integralSample⟩
  let namedA : PrimitivePoint := ⟨sampledMatrix data.aMatrix namedStage first cycle,
    PeriodMatrix.sampledMatrix data.aMatrix namedStage second cycle⟩
  let namedB : PrimitivePoint := ⟨sampledMatrix data.bMatrix namedStage first cycle,
    PeriodMatrix.sampledMatrix data.bMatrix namedStage second cycle⟩
  have aBound : PrimitivePoint.Bounded a (PairedAreaAccuracy.standardPairMagnitude data first second cycle) :=
    ⟨((data.aProgram first cycle).integral.sample_bounded modelStage).trans ((Fraction.Order.Basic.le_max_left _
      _).trans (Fraction.Order.Basic.le_max_left _ _)),
     ((data.aProgram second cycle).integral.sample_bounded modelStage).trans ((Fraction.Order.Basic.le_max_right _
       _).trans (Fraction.Order.Basic.le_max_left _ _))⟩
  have bBound : PrimitivePoint.Bounded b (PairedAreaAccuracy.standardPairMagnitude data first second cycle) :=
    ⟨((data.bProgram first cycle).integral.sample_bounded modelStage).trans ((Fraction.Order.Basic.le_max_left _
      _).trans (Fraction.Order.Basic.le_max_right _ _)),
     ((data.bProgram second cycle).integral.sample_bounded modelStage).trans ((Fraction.Order.Basic.le_max_right _
       _).trans (Fraction.Order.Basic.le_max_right _ _))⟩
  have aError : PrimitivePoint.Bounded (namedA.sub a) budget.rowTarget := by
    dsimp only [namedA, a, PrimitivePoint.sub, PrimitivePoint.Bounded]
    simp only [PeriodMatrix.sampledMatrix_apply, PeriodData.aMatrix_apply]
    constructor
    · have h := (request.aLeft.close (((Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _)).trans
        namedLater)
          (((Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _)).trans modelLater)).le
      change Fraction.Order.Basic.LessEqual _ _ at h
      change Fraction.Order.Basic.LessEqual _ _
      simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at h
      convert h using 1; rfl
    · have h := (request.aRight.close (((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_left _ _)).trans
        namedLater)
          (((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_left _ _)).trans modelLater)).le
      change Fraction.Order.Basic.LessEqual _ _ at h
      change Fraction.Order.Basic.LessEqual _ _
      simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at h
      convert h using 1; rfl
  have bError : PrimitivePoint.Bounded (namedB.sub b) budget.rowTarget := by
    dsimp only [namedB, b, PrimitivePoint.sub, PrimitivePoint.Bounded]
    simp only [PeriodMatrix.sampledMatrix_apply, PeriodData.bMatrix_apply]
    constructor
    · have h := (request.bLeft.close (((Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)).trans
        namedLater)
          (((Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)).trans modelLater)).le
      change Fraction.Order.Basic.LessEqual _ _ at h
      change Fraction.Order.Basic.LessEqual _ _
      simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at h
      convert h using 1; rfl
    · have h := (request.bRight.close (((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)).trans
        namedLater)
          (((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)).trans modelLater)).le
      change Fraction.Order.Basic.LessEqual _ _ at h
      change Fraction.Order.Basic.LessEqual _ _
      simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at h
      convert h using 1; rfl
  have estimate := PrimitivePoint.area_difference_bound budget.magnitude_nonnegative budget.row_positive.le
    budget.row_le_one aBound bBound aError bError
  have weightNonnegative : 0 ≤ 32 * (PairedAreaAccuracy.standardPairMagnitude data first second cycle + 1) := by
    rw [← budget.weight_eq]
    exact budget.weight_nonnegative
  have paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct budget.row_paid weightNonnegative).trans
    (WeightedAggregateBudget.weighted_perTerm_le budget.handle_positive weightNonnegative 1)
  have strict : Aggregate.perTerm budget.handleTarget 1 < budget.handleTarget := by
    simpa only [Nat.cast_one, Fraction.Field.one_mul] using
      Aggregate.count_mul_perTerm_lt budget.handle_positive 1
  exact estimate.trans_lt (paid.trans_lt strict)

end StandardNamedAreaRequest

/-- Two comparisons with the same actual model give the allocated surface-to-named area bound. -/
private theorem combine_area {surface model named : Data.Gaussian.Basic.Canonical} {target : Fraction.Rational}
    (surfaceError : Data.Gaussian.Norm.Basic.normSq (surface - model) < target / 16)
    (namedError : Data.Gaussian.Norm.Basic.normSq (named - model) < target / 16) :
      Data.Gaussian.Norm.Basic.normSq (surface - named) < target / 4 := by
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two (surface - model) (named - model)).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct surfaceError namedError))
  have paid : 2 * (target / 16 + target / 16) = target / 4 := by
    apply Fraction.Field.mul_right_cancel_of_ne (by decide : (4 : Fraction.Rational) ≠ 0)
    calc
      _ = (target / 16) * 16 := by ring1
      _ = target := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
      _ = (target / 4) * 4 := (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)).symm
  exact (congrArg Data.Gaussian.Norm.Basic.normSq (by
      ring1 : surface - named = (surface - model) - (named - model))).trans_lt
    (estimate.trans_eq paid)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : FramedPuncturedGrid curve
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher}
  {lifted : LiftedPuncturedGrid base} {cycle first second : Fin genus}
  (period : Purelib.Riemann.Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodRow curve)
  (periodEq : period =
    (Purelib.Riemann.Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData curve
    branches).rows cycle)
  {source : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {programs :
    CutChordPrograms lifted source}
  {firstComponents : ComponentSamples
    programs.programs first}
  {secondComponents : ComponentSamples
    programs.programs second}
  {firstPeriods : ChordPeriods
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaAccuracy.standardPairRow lifted cycle period
    periodEq).span programs firstComponents}
  {secondPeriods : ChordPeriods
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaAccuracy.standardPairRow lifted cycle period
    periodEq).span programs secondComponents}
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

/-- The retained surface determinant approximates the public named standard-matrix determinant.

Both surface readings use the actual cut-area triangle bank, and the named entries keep their independently selected
sample stage. -/
def NamedStandardAreaAccurate
    (budget : HandleAreaBudgets.HandleAreaBudget (PairedAreaAccuracy.standardPairMagnitude
      (PreparedRefinementPrograms.rawPeriodDataOfData curve branches) first second cycle) 1 target)
    (readings : PairedAreaReadings firstPeriods secondPeriods segments domains minimum numericalFloor
      budget.rowTarget budget.rowTarget extraPoints cut cache)
    (namedStage : Nat) : Prop :=
  let data := PreparedRefinementPrograms.rawPeriodDataOfData curve branches
  let row := PairedAreaAccuracy.standardPairRow lifted cycle period periodEq
  let left := CanonicalEdgeValues.edgeValuation lifted.mesh readings.area.left.values
  let right := CanonicalEdgeValues.edgeValuation lifted.mesh readings.area.right.values
  let a : PrimitivePoint := ⟨SewingRetraction.wordValue left row.pair.aFaces.geometry.indexed,
    SewingRetraction.wordValue right row.pair.aFaces.geometry.indexed⟩
  let b : PrimitivePoint := ⟨SewingRetraction.wordValue left row.pair.bFaces.geometry.indexed,
    SewingRetraction.wordValue right row.pair.bFaces.geometry.indexed⟩
  let namedA := PeriodMatrix.sampledMatrix data.aMatrix namedStage
  let namedB := PeriodMatrix.sampledMatrix data.bMatrix namedStage
  Data.Gaussian.Norm.Basic.normSq (Stokes.edgeArea a b - (namedA first cycle * namedB second cycle - namedB
    first cycle * namedA second cycle)) < target / 4

/-- The actual named standard-matrix entries are controlled by the same cut-area triangle caches. Both sampling
thresholds are constructed internally. -/
theorem PairedAreaReadings.named_standard_area_accurate
    (budget : HandleAreaBudgets.HandleAreaBudget (PairedAreaAccuracy.standardPairMagnitude
      (PreparedRefinementPrograms.rawPeriodDataOfData curve branches) first second cycle) 1 target)
    (readings : PairedAreaReadings firstPeriods secondPeriods segments domains minimum numericalFloor
      budget.rowTarget budget.rowTarget extraPoints cut cache) (namedFloor : Nat) :
    let request := Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.NamedArea.StandardNamedAreaRequest.build
      (PreparedRefinementPrograms.rawPeriodDataOfData curve branches)
      first second cycle budget namedFloor
      (max readings.left.readings.standard.original.comparison.stage
        readings.right.readings.standard.original.comparison.stage)
    ∀ namedStage, request.namedIndex ≤ namedStage →
      NamedStandardAreaAccurate period periodEq budget
      readings namedStage := by
  intro request namedStage namedLater
  have model := PairedAreaReadings.standard_area_accurate period periodEq budget readings request.modelIndex
    request.modelFloor_le
  have named := request.area_accurate namedLater (le_refl request.modelIndex)
  dsimp only [PairedAreaAccuracy.StandardAreaAccurate] at model
  dsimp only [StandardNamedAreaRequest.AreaAccurate] at named
  exact combine_area (model.trans_eq
    budget.handleTarget_eq) (named.trans_eq budget.handleTarget_eq)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.NamedArea
