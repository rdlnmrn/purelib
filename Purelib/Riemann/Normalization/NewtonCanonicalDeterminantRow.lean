module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Calculus.WeightedAggregateBudget
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Purelib.Topology.Surface.Boundary.HandleAreaBudgets
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Riemann.Periods.NewtonCanonicalPeriodReadback
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests
import Purelib.Riemann.Branches.NewtonRequestedCutBudget
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Riemann.Periods.NewtonPairedPeriodFragments
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.Periods.NewtonRequestedPairedPeriods
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Periods.NewtonPeriodGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Periods.NewtonCanonicalPeriodData
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

public section

open Purelib.Data

/-! Four retained original-period comparisons pay one corrected determinant
row on the actual Newton mesh, with the same incoming sheet in every word. -/
namespace Purelib.Riemann.Normalization.NewtonCanonicalDeterminantRow

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered
  anchor)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces (MeshWordReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Riemann.Periods.NewtonPeriodGeometry (PeriodGeometry)
open Purelib.Riemann.Periods.NewtonCanonicalPeriodData (ACanonicalPreparation BCanonicalPreparation aCanonicalAssigned
  bCanonicalAssigned aCanonicalFaces bCanonicalFaces)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Topology.Surface.Boundary.HandleAreaBudgets (HandleAreaBudget)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests (rowMagnitude)
open Purelib.Riemann.Periods.NewtonCanonicalPeriodReadback (canonicalPeriodSheet)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
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
  {preparation : NewtonPreparation base.bank.toBranchCellBank}
  {boundaryTarget radius : Rational} {floor : Nat}
  {first second differential cycle : Fin genus}
  {target : Rational} {minimum : Nat}

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Data.Rat.Fraction.Compatibility

section
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Rat
/-- The exact original four-period row magnitude identity. -/
@[expose] def CanonicalRowMagnitudeEq (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (first
  second cycle : Fin genus) (magnitude : Fraction.Rational) : Prop :=
  magnitude = Meshes.PuncturedGrid.Paired.BilinearRequests.rowMagnitude prepared first second cycle

/-- The retained first-differential canonical A preparation for this original boundary and cycle. -/
@[expose] def CanonicalRowFirstA (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (boundary : BoundaryPreparation preparation first second boundaryTarget radius floor)
    (cycle : Fin genus) (minimum : Nat) (allowance : Fraction.Rational) :=
  ACanonicalPreparation prepared boundary.periodGeometry first cycle allowance minimum

/-- The retained second-differential canonical A preparation for this original boundary and cycle. -/
@[expose] def CanonicalRowSecondA (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (boundary : BoundaryPreparation preparation first second boundaryTarget radius floor)
    (cycle : Fin genus) (minimum : Nat) (allowance : Fraction.Rational) :=
  ACanonicalPreparation prepared boundary.periodGeometry second cycle allowance minimum

/-- The retained first-differential canonical B preparation for this original boundary and cycle. -/
@[expose] def CanonicalRowFirstB (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (boundary : BoundaryPreparation preparation first second boundaryTarget radius floor)
    (cycle : Fin genus) (minimum : Nat) (allowance : Fraction.Rational) :=
  BCanonicalPreparation prepared boundary.periodGeometry first cycle allowance minimum

/-- The retained second-differential canonical B preparation for this original boundary and cycle. -/
@[expose] def CanonicalRowSecondB (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (boundary : BoundaryPreparation preparation first second boundaryTarget radius floor)
    (cycle : Fin genus) (minimum : Nat) (allowance : Fraction.Rational) :=
  BCanonicalPreparation prepared boundary.periodGeometry second cycle allowance minimum

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Topology.Surface in
set_option genInjectivity false in
/-- Four original canonical period preparations sharing a paid determinant-row budget.

The retained magnitude, original boundary and cycle index distinct first/second A/B requests with the same target and
minimum stage. -/
structure CanonicalDeterminantRow (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (boundary : BoundaryPreparation preparation first second boundaryTarget radius floor)
    (cycle : Fin genus) (target : Fraction.Rational) (minimum : Nat) : Type 2 where
  /-- The retained magnitude bound for the original four period samples. -/ magnitude : Fraction.Rational
  /-- The magnitude is exactly the original row magnitude. -/ magnitude_eq : CanonicalRowMagnitudeEq prepared first
    second cycle magnitude
  /-- The paid handle-area budget for this original determinant row. -/ budget :
    Boundary.HandleAreaBudgets.HandleAreaBudget magnitude 1 target
  /-- The retained first-differential A preparation. -/ firstA : CanonicalRowFirstA prepared boundary cycle minimum
    budget.rowTarget
  /-- The retained second-differential A preparation. -/ secondA : CanonicalRowSecondA prepared boundary cycle minimum
    budget.rowTarget
  /-- The retained first-differential B preparation. -/ firstB : CanonicalRowFirstB prepared boundary cycle minimum
    budget.rowTarget
  /-- The retained second-differential B preparation. -/ secondB : CanonicalRowSecondB prepared boundary cycle minimum
    budget.rowTarget

constructive_injectivity CanonicalDeterminantRow

namespace CanonicalDeterminantRow

variable {prepared : Prepared paired}
  {boundary : BoundaryPreparation preparation first second boundaryTarget radius floor}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Topology.Surface in
/-- Prepare the four original canonical period entries under one retained row budget.

The actual row magnitude and positive target determine the handle allowance; all four requests retain the original
boundary and cycle. -/
@[expose] def build (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (boundary : BoundaryPreparation preparation first second boundaryTarget radius floor)
    (cycle : Fin genus) (target : Fraction.Rational) (positive : 0 < target) (minimum : Nat) :
    CanonicalDeterminantRow prepared boundary cycle target minimum :=
  let nonnegative : 0 ≤ Meshes.PuncturedGrid.Paired.BilinearRequests.rowMagnitude prepared first second cycle :=
    (prepared.periodData.aProgram first cycle).integral.centerBound_nonneg.trans
      ((Fraction.Order.Basic.le_max_left _ _).trans (Fraction.Order.Basic.le_max_left _ _))
  let budget := Boundary.HandleAreaBudgets.HandleAreaBudget.build
    (Meshes.PuncturedGrid.Paired.BilinearRequests.rowMagnitude prepared first second cycle) nonnegative 1 target
    positive
  ⟨rowMagnitude prepared first second cycle, rfl, budget, ACanonicalPreparation.build prepared boundary.periodGeometry
    first cycle budget.rowTarget budget.row_positive minimum,
    ACanonicalPreparation.build prepared boundary.periodGeometry second cycle budget.rowTarget budget.row_positive
      minimum,
    BCanonicalPreparation.build prepared boundary.periodGeometry first cycle budget.rowTarget budget.row_positive
      minimum,
    BCanonicalPreparation.build prepared boundary.periodGeometry second cycle budget.rowTarget budget.row_positive
      minimum⟩

/-- The maximum of the four retained original numerical floors. -/
@[expose] def numericalIndex (data : CanonicalDeterminantRow prepared boundary cycle target minimum) : Nat :=
  max (max data.firstA.numericalIndex data.secondA.numericalIndex)
    (max data.firstB.numericalIndex data.secondB.numericalIndex)

/-- The maximum of the four original fragment-stage floors. -/
@[expose] def periodStage (data : CanonicalDeterminantRow prepared boundary cycle target minimum) : Nat :=
  max (max data.firstA.request.fragments.stage data.secondA.request.fragments.stage)
    (max data.firstB.request.fragments.stage data.secondB.request.fragments.stage)

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- The retained determinant-row allowance pays its original magnitude-weighted target. -/
private theorem paid (data : CanonicalDeterminantRow prepared boundary cycle target minimum) :
    32 * (data.magnitude + 1) * data.budget.rowTarget ≤ target := by
  have nonnegative : 0 ≤ 32 * (data.magnitude + 1) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_pos_direct (n := 32) (by decide)).le
      (add_nonneg data.budget.magnitude_nonnegative (by decide))
  have bound := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct data.budget.row_paid nonnegative).trans
    (CCL.Calculus.WeightedAggregateBudget.weighted_perTerm_le data.budget.handle_positive nonnegative 1)
  have targetLe : data.budget.handleTarget ≤ target := by
    rw [data.budget.handleTarget_eq]
    exact Fraction.Order.Field.divide_le_self data.budget.positive.le (by decide +kernel)
  exact bound.trans ((Budget.Aggregate.perTerm_le data.budget.handle_positive.le 1).trans targetLe)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Periods in
open Purelib.Riemann.RootContinuation in
open Purelib.Topology.Polygon in
open Purelib.Topology.Surface in
/-- Bound the original canonical-word determinant against the four retained period samples.

Both numerical and period stages must meet their separate maximum floors; the exact A/B order and common row budget
preserve the original determinant sign. -/
theorem accurate (data : CanonicalDeterminantRow prepared boundary cycle target minimum)
    (numericalIndex : Nat) (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics boundary.domains
      numericalIndex)
    (left : Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get first) boundary.lifted.mesh)
    (right : Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get second) boundary.lifted.mesh)
    (later : data.numericalIndex ≤ numericalIndex) (stage : Nat) (after : data.periodStage ≤ stage) :
    let incoming := canonicalPeriodSheet (lifted := lifted) (sheet := sheet) boundary.periodGeometry
    let aWord := boundary.lifted.edges.indexedEdges boundary.lifted.vertices
      (boundary.fine.family.single.grid.shrunk.included.resplit (prepared.aWalk cycle).closed.walk
        (lifted.vertices.coordinate_onGrid
          (Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet))) incoming
    let bWord := boundary.lifted.edges.indexedEdges boundary.lifted.vertices
      (boundary.fine.family.single.grid.shrunk.included.resplit (prepared.bWalk cycle).closed.walk
        (lifted.vertices.coordinate_onGrid
          (Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet))) incoming
    let leftValue := Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation boundary.lifted.mesh left.values
    let rightValue := Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation boundary.lifted.mesh right.values
    Data.Gaussian.Norm.Basic.normSq ((Sewing.SewingRetraction.wordValue leftValue aWord *
      Sewing.SewingRetraction.wordValue
      rightValue bWord -
      Sewing.SewingRetraction.wordValue leftValue bWord * Sewing.SewingRetraction.wordValue rightValue aWord) -
      (((prepared.periodData.aProgram first cycle).integral.model stage).integralSample *
        ((prepared.periodData.bProgram second cycle).integral.model stage).integralSample -
       ((prepared.periodData.bProgram first cycle).integral.model stage).integralSample *
        ((prepared.periodData.aProgram second cycle).integral.model stage).integralSample)) ≤ target := by
  intro incoming aWord bWord leftValue rightValue
  have aLater := (Nat.Order.le_max_left _ _).trans later
  have bLater := (Nat.Order.le_max_right _ _).trans later
  have aAfter := (Nat.Order.le_max_left _ _).trans after
  have bAfter := (Nat.Order.le_max_right _ _).trans after
  have firstA := NewtonCanonicalPeriodReadback.ACanonicalPreparation.word_accurate data.firstA data.budget.row_positive
    numericalIndex cache left
    ((Nat.Order.le_max_left _ _).trans aLater) stage ((Nat.Order.le_max_left _ _).trans aAfter)
  have secondA := NewtonCanonicalPeriodReadback.ACanonicalPreparation.word_accurate data.secondA
    data.budget.row_positive numericalIndex cache right
    ((Nat.Order.le_max_right _ _).trans aLater) stage ((Nat.Order.le_max_right _ _).trans aAfter)
  have firstB := NewtonCanonicalPeriodReadback.BCanonicalPreparation.word_accurate data.firstB data.budget.row_positive
    numericalIndex cache left
    ((Nat.Order.le_max_left _ _).trans bLater) stage ((Nat.Order.le_max_left _ _).trans bAfter)
  have secondB := NewtonCanonicalPeriodReadback.BCanonicalPreparation.word_accurate data.secondB
    data.budget.row_positive numericalIndex cache right
    ((Nat.Order.le_max_right _ _).trans bLater) stage ((Nat.Order.le_max_right _ _).trans bAfter)
  have boundA1 : Basic.Canonical.normSq (((prepared.periodData.aProgram first cycle).integral.model
    stage).integralSample) ≤ data.magnitude :=
    ((prepared.periodData.aProgram first cycle).integral.sample_bounded stage).trans
      (((Fraction.Order.Basic.le_max_left _ _).trans (Fraction.Order.Basic.le_max_left _ _)).trans_eq
        data.magnitude_eq.symm)
  have boundA2 : Basic.Canonical.normSq (((prepared.periodData.aProgram second cycle).integral.model
    stage).integralSample) ≤ data.magnitude :=
    ((prepared.periodData.aProgram second cycle).integral.sample_bounded stage).trans
      (((Fraction.Order.Basic.le_max_right _ _).trans (Fraction.Order.Basic.le_max_left _ _)).trans_eq
        data.magnitude_eq.symm)
  have boundB1 : Basic.Canonical.normSq (((prepared.periodData.bProgram first cycle).integral.model
    stage).integralSample) ≤ data.magnitude :=
    ((prepared.periodData.bProgram first cycle).integral.sample_bounded stage).trans
      (((Fraction.Order.Basic.le_max_left _ _).trans (Fraction.Order.Basic.le_max_right _ _)).trans_eq
        data.magnitude_eq.symm)
  have boundB2 : Basic.Canonical.normSq (((prepared.periodData.bProgram second cycle).integral.model
    stage).integralSample) ≤ data.magnitude :=
    ((prepared.periodData.bProgram second cycle).integral.sample_bounded stage).trans
      (((Fraction.Order.Basic.le_max_right _ _).trans (Fraction.Order.Basic.le_max_right _ _)).trans_eq
        data.magnitude_eq.symm)
  exact (Boundary.HandleAreaBounds.PrimitivePoint.area_difference_bound
    (first := ⟨((prepared.periodData.aProgram first cycle).integral.model stage).integralSample,
      ((prepared.periodData.aProgram second cycle).integral.model stage).integralSample⟩)
    (last := ⟨((prepared.periodData.bProgram first cycle).integral.model stage).integralSample,
      ((prepared.periodData.bProgram second cycle).integral.model stage).integralSample⟩)
    (changedFirst := ⟨wordValue leftValue aWord, Sewing.SewingRetraction.wordValue rightValue aWord⟩)
    (changedLast := ⟨wordValue leftValue bWord, Sewing.SewingRetraction.wordValue rightValue bWord⟩)
    data.budget.magnitude_nonnegative
    data.budget.row_positive.le data.budget.row_le_one
    ⟨boundA1, boundA2⟩ ⟨boundB1, boundB2⟩
    ⟨by
        change Fraction.Order.Basic.LessEqual _ _
        have h := firstA.le
        change Fraction.Order.Basic.LessEqual _ _ at h
        simpa only [aWord, leftValue, incoming,
          NewtonRequestedBoundary.BoundaryPreparation.periodGeometry,
          Stokes.PrimitivePoint.sub,
          Norm.Basic.normSq_eq_canonical] using h,
      by
        change Fraction.Order.Basic.LessEqual _ _
        have h := secondA.le
        change Fraction.Order.Basic.LessEqual _ _ at h
        simpa only [aWord, rightValue, incoming,
          NewtonRequestedBoundary.BoundaryPreparation.periodGeometry,
          Stokes.PrimitivePoint.sub,
          Norm.Basic.normSq_eq_canonical] using h⟩
    ⟨by
        change Fraction.Order.Basic.LessEqual _ _
        have h := firstB.le
        change Fraction.Order.Basic.LessEqual _ _ at h
        simpa only [bWord, leftValue, incoming,
          NewtonRequestedBoundary.BoundaryPreparation.periodGeometry,
          Stokes.PrimitivePoint.sub,
          Norm.Basic.normSq_eq_canonical] using h,
      by
        change Fraction.Order.Basic.LessEqual _ _
        have h := secondB.le
        change Fraction.Order.Basic.LessEqual _ _ at h
        simpa only [bWord, rightValue, incoming,
          NewtonRequestedBoundary.BoundaryPreparation.periodGeometry,
          Stokes.PrimitivePoint.sub,
          Norm.Basic.normSq_eq_canonical] using h⟩).trans data.paid

end CanonicalDeterminantRow
end Purelib.Riemann.Normalization.NewtonCanonicalDeterminantRow
