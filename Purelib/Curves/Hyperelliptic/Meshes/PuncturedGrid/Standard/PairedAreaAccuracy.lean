module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic

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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.CanonicalCut
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
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
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Word.PairedWord
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaReadings
public import Purelib.Topology.Surface.Boundary.HandleAreaBudgets
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Budget.SynchronizedSamples
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.FamilyReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.WeightedPair
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
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
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.CCL.Calculus

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection

open Purelib.Data.Rat

open Purelib.Riemann

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank.PreparedCycleModels

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Boundary.HandleAreaBounds

open Purelib.Topology.Surface.Boundary.HandleAreaBudgets

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Word.PairedWord.CutBoundaryWord

@[expose] public section

/-! Compare one actual standard A/B area with its two-differential surface
valuation at a common period stage. Magnitudes are fixed before requesting
the surface readings; no physical or signed-face term is discarded. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaAccuracy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Surface.Boundary.HandleAreaBudgets (HandleAreaBudget)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaReadings (CanonicalIntersectionRow)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection (IntersectionRow)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings (StandardBoundaryReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutChordPrograms)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods (ComponentSamples)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods (ChordPeriods)
open Purelib.Riemann.Periods.PeriodMatrix (PeriodData)
open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Riemann.Integration.PreparedRefinementPrograms (rawPeriodDataOfData)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

/-- A common nonnegative bound for both differentials' actual A/B period samples on one standard cycle. -/
def standardPairMagnitude {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve) (first second cycle : Fin genus) : Fraction.Rational :=
  max (max (data.aProgram first cycle).integral.centerBound (data.aProgram second cycle).integral.centerBound)
    (max (data.bProgram first cycle).integral.centerBound (data.bProgram second cycle).integral.centerBound)

/-- Allocate the standard handle-area comparison budget using its actual four period magnitude bounds. -/
def standardPairBudget {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve) (first second cycle : Fin genus)
    (target : Fraction.Rational) (positive : 0 < target) :
    HandleAreaBudgets.HandleAreaBudget
      (standardPairMagnitude data first second
      cycle) 1 target :=
  HandleAreaBudget.build
    (@max Fraction.Rational (@LinearOrder.toMax Fraction.Rational Fraction.Order.Basic.instLinearOrder)
      (@max Fraction.Rational (@LinearOrder.toMax Fraction.Rational Fraction.Order.Basic.instLinearOrder) (data.aProgram
        first cycle).integral.centerBound (data.aProgram second cycle).integral.centerBound)
      (max (data.bProgram first cycle).integral.centerBound (data.bProgram second cycle).integral.centerBound) :
        Fraction.Rational)
    ((data.aProgram first cycle).integral.centerBound_nonneg.trans
    ((Fraction.Order.Basic.le_max_left _ _).trans (Fraction.Order.Basic.le_max_left _ _))) 1 target positive

/-- A quarter of a positive rational is at most the original value. -/
private theorem quarter_le {value : Fraction.Rational} (positive : 0 < value) : value / 4 ≤ value := by
  apply (Fraction.Order.Field.div_le_iff_pos (by decide)).mpr
  exact (show value = value * 1 by ring1).le.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide : (1 : Fraction.Rational) ≤ 4) positive.le)

/-- Transport a scalar approximation along an equality of its retained input owners. -/
private theorem transfer_value {α : Sort _} (value : α → Data.Gaussian.Basic.Canonical) {before after : α}
    (same : before = after) {sample : Data.Gaussian.Basic.Canonical} {error : Fraction.Rational}
    (accurate : Data.Gaussian.Norm.Basic.normSq (value after - sample) < error) :
      Data.Gaussian.Norm.Basic.normSq (value before - sample) < error :=
  (congrArg (fun input => Data.Gaussian.Norm.Basic.normSq (value input - sample)) same).trans_lt accurate

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

/-- The actual standard cycle's intersection row in the lifted grid's canonical integral pairing. -/
def standardPairRow (lifted : Meshes.LiftedPuncturedGrid base) (cycle : Fin genus)
    (period : PreparedCycleModels.RootClosedPeriodRow curve)
    (periodEq : period = (RootClosedPeriodBank.ofData curve branches).rows cycle) :
    PairedAreaReadings.CanonicalIntersectionRow lifted cycle :=
  IntersectionRow.ofPeriod lifted lifted.cutIntegralPairing (IntegralPairing.wordNormalForm
    lifted.cutIntegralPairing).normal cycle period periodEq

variable {source : Differential genus} {programs :
  CutChordPrograms lifted source}
  {firstComponents : ComponentSamples
    programs.programs first}
  {secondComponents : ComponentSamples
    programs.programs second}
  {firstPeriods : ChordPeriods
    (standardPairRow lifted cycle period
    periodEq).span programs firstComponents}
  {secondPeriods : ChordPeriods
    (standardPairRow lifted cycle period
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

/-- The shared cut-area determinant approximates the original A/B period determinant at the supplied period stage.

Both differentials retain their actual triangle bank and the original standard cycle's intersection row. -/
def StandardAreaAccurate
    (budget : HandleAreaBudgets.HandleAreaBudget
      (standardPairMagnitude
      (PreparedRefinementPrograms.rawPeriodDataOfData curve branches) first second cycle) 1 target)
    (readings : PairedAreaReadings firstPeriods secondPeriods segments domains minimum numericalFloor
      budget.rowTarget budget.rowTarget extraPoints cut cache)
    (periodStage : Nat) : Prop :=
    let data := PreparedRefinementPrograms.rawPeriodDataOfData curve branches
    let left := CanonicalEdgeValues.edgeValuation lifted.mesh readings.area.left.values
    let right := CanonicalEdgeValues.edgeValuation lifted.mesh readings.area.right.values
    let row := standardPairRow lifted cycle period
      periodEq
    let a : PrimitivePoint := ⟨wordValue left row.pair.aFaces.geometry.indexed,
      SewingRetraction.wordValue right row.pair.aFaces.geometry.indexed⟩
    let b : PrimitivePoint := ⟨wordValue left row.pair.bFaces.geometry.indexed,
      SewingRetraction.wordValue right row.pair.bFaces.geometry.indexed⟩
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeArea a b -
      (((data.aProgram first cycle).integral.model periodStage).integralSample *
        ((data.bProgram second cycle).integral.model periodStage).integralSample -
       ((data.bProgram first cycle).integral.model periodStage).integralSample *
        ((data.aProgram second cycle).integral.model periodStage).integralSample)) < budget.handleTarget

/-- The original A-period approximation holds on triangle values equal to the retained standard reader. -/
private theorem shared_a_error {differential : Fin genus} {error : Fraction.Rational}
    (standard : BoundaryReadings.StandardBoundaryReadings
      (standardPairRow lifted cycle period
      periodEq) differential minimum error domains extraPoints)
    (values : Data.Vector (PrimitiveSewing.PrimitiveValues 3) lifted.mesh.triangles.length)
    (same : values = standard.triangles.values) (periodStage : Nat) (later : standard.original.comparison.stage ≤
      periodStage) :
    Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh
      values) (standardPairRow lifted cycle period
      periodEq).pair.aFaces.geometry.indexed -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).aProgram differential cycle).integral.model
        periodStage).integralSample) < error := by
  have bound := CanonicalCut.a_valuation_accurate (IntegralPairing.wordNormalForm lifted.cutIntegralPairing).normal
    period periodEq standard periodStage later
  exact transfer_value
    (fun readings : Data.Vector (PrimitiveSewing.PrimitiveValues 3) lifted.mesh.triangles.length =>
      SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings)
        (standardPairRow lifted cycle period
        periodEq).pair.aFaces.geometry.indexed)
    same bound

/-- The original B-period approximation holds on triangle values equal to the retained standard reader. -/
private theorem shared_b_error {differential : Fin genus} {error : Fraction.Rational}
    (standard : BoundaryReadings.StandardBoundaryReadings
      (standardPairRow lifted cycle period
      periodEq) differential minimum error domains extraPoints)
    (values : Data.Vector (PrimitiveSewing.PrimitiveValues 3) lifted.mesh.triangles.length)
    (same : values = standard.triangles.values) (periodStage : Nat) (later : standard.original.comparison.stage ≤
      periodStage) :
    Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh
      values) (standardPairRow lifted cycle period
      periodEq).pair.bFaces.geometry.indexed -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).bProgram differential cycle).integral.model
        periodStage).integralSample) < error := by
  have bound := CanonicalCut.b_valuation_accurate (IntegralPairing.wordNormalForm lifted.cutIntegralPairing).normal
    period periodEq standard periodStage later
  exact transfer_value
    (fun readings : Data.Vector (PrimitiveSewing.PrimitiveValues 3) lifted.mesh.triangles.length =>
      SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings)
        (standardPairRow lifted cycle period
        periodEq).pair.bFaces.geometry.indexed)
    same bound

/-- The original A/B determinant is approximated on the exact cut-area triangle bank. Both differentials use the same
later period index. -/
theorem PairedAreaReadings.standard_area_accurate
    (budget : HandleAreaBudgets.HandleAreaBudget
      (standardPairMagnitude
      (PreparedRefinementPrograms.rawPeriodDataOfData curve branches) first second cycle) 1 target)
    (readings : PairedAreaReadings firstPeriods secondPeriods segments domains minimum numericalFloor
      budget.rowTarget budget.rowTarget extraPoints cut cache)
    (periodStage : Nat)
    (later : max readings.left.readings.standard.original.comparison.stage
      readings.right.readings.standard.original.comparison.stage ≤ periodStage) :
    StandardAreaAccurate period periodEq budget
      readings periodStage := by
  let data := PreparedRefinementPrograms.rawPeriodDataOfData curve branches
  let a : PrimitivePoint := ⟨((data.aProgram first cycle).integral.model periodStage).integralSample,
    ((data.aProgram second cycle).integral.model periodStage).integralSample⟩
  let b : PrimitivePoint := ⟨((data.bProgram first cycle).integral.model periodStage).integralSample,
    ((data.bProgram second cycle).integral.model periodStage).integralSample⟩
  have aBound : PrimitivePoint.Bounded a
    (standardPairMagnitude data first second
    cycle) :=
    ⟨((data.aProgram first cycle).integral.sample_bounded periodStage).trans
      ((Fraction.Order.Basic.le_max_left _ _).trans (Fraction.Order.Basic.le_max_left _ _)),
     ((data.aProgram second cycle).integral.sample_bounded periodStage).trans
      ((Fraction.Order.Basic.le_max_right _ _).trans (Fraction.Order.Basic.le_max_left _ _))⟩
  have bBound : PrimitivePoint.Bounded b
    (standardPairMagnitude data first second
    cycle) :=
    ⟨((data.bProgram first cycle).integral.sample_bounded periodStage).trans
      ((Fraction.Order.Basic.le_max_left _ _).trans (Fraction.Order.Basic.le_max_right _ _)),
     ((data.bProgram second cycle).integral.sample_bounded periodStage).trans
      ((Fraction.Order.Basic.le_max_right _ _).trans (Fraction.Order.Basic.le_max_right _ _))⟩
  have leftLater := (Data.Nat.Order.le_max_left _ _).trans later
  have rightLater := (Data.Nat.Order.le_max_right _ _).trans later
  have aLeft := shared_a_error period periodEq
    readings.left.readings.standard readings.area.left.values
    readings.ownership.2.2.1 periodStage leftLater
  have aRight := shared_a_error period periodEq
    readings.right.readings.standard readings.area.right.values
    readings.ownership.2.2.2 periodStage rightLater
  have bLeft := shared_b_error period periodEq
    readings.left.readings.standard readings.area.left.values
    readings.ownership.2.2.1 periodStage leftLater
  have bRight := shared_b_error period periodEq
    readings.right.readings.standard readings.area.right.values
    readings.ownership.2.2.2 periodStage rightLater
  have errorPaid : (budget.rowTarget / 4) / 4 ≤ budget.rowTarget :=
    (quarter_le
      (Fraction.Order.Field.div_pos_direct budget.row_positive (by decide))).trans
      (quarter_le budget.row_positive)
  let row := standardPairRow lifted cycle period
    periodEq
  have aError : PrimitivePoint.Bounded ((⟨wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh
    readings.area.left.values) row.pair.aFaces.geometry.indexed,
      SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.area.right.values)
        row.pair.aFaces.geometry.indexed⟩ : Stokes.PrimitivePoint).sub a) budget.rowTarget := by
    exact ⟨by simpa only [PrimitivePoint.sub,
        Data.Gaussian.Norm.Basic.normSq_eq_canonical] using aLeft.le.trans errorPaid,
      by simpa only [PrimitivePoint.sub,
        Data.Gaussian.Norm.Basic.normSq_eq_canonical] using aRight.le.trans errorPaid⟩
  have bError : PrimitivePoint.Bounded ((⟨wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh
    readings.area.left.values) row.pair.bFaces.geometry.indexed,
      SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.area.right.values)
        row.pair.bFaces.geometry.indexed⟩ : Stokes.PrimitivePoint).sub b) budget.rowTarget := by
    exact ⟨by simpa only [PrimitivePoint.sub,
        Data.Gaussian.Norm.Basic.normSq_eq_canonical] using bLeft.le.trans errorPaid,
      by simpa only [PrimitivePoint.sub,
        Data.Gaussian.Norm.Basic.normSq_eq_canonical] using bRight.le.trans errorPaid⟩
  have estimate := PrimitivePoint.area_difference_bound budget.magnitude_nonnegative budget.row_positive.le
    budget.row_le_one aBound bBound aError bError
  have weightNonnegative : 0 ≤ 32 *
    (standardPairMagnitude data first second cycle
    + 1) := by
    rw [← budget.weight_eq]
    exact budget.weight_nonnegative
  have paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct budget.row_paid weightNonnegative).trans
    (WeightedAggregateBudget.weighted_perTerm_le budget.handle_positive weightNonnegative 1)
  have strict : Aggregate.perTerm budget.handleTarget 1 < budget.handleTarget := by
    simpa only [Nat.cast_one, Fraction.Field.one_mul] using Aggregate.count_mul_perTerm_lt budget.handle_positive 1
  exact estimate.trans_lt (paid.trans_lt strict)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaAccuracy
