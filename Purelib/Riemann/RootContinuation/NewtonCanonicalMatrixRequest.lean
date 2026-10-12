module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.LinearAlgebra.Matrix.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Riemann.RootContinuation.NewtonCanonicalSampleComparison
public import Purelib.Riemann.Periods.NewtonCombinedPeriodArea
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.Periods.NewtonCanonicalPeriodData
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Periods.NewtonPairedPeriodFragments
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Riemann.Periods.NewtonCanonicalPeriodReadback
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.NewtonPeriodGeometry
import Purelib.Riemann.Periods.NewtonRequestedPairedPeriods
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

/-! One coefficient-independent comparison schedule for every A/B entry,
on the supplied retained geometry and the original corrected period owner. -/
namespace Purelib.Riemann.RootContinuation.NewtonCanonicalMatrixRequest

open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.Periods.NewtonPeriodGeometry (PeriodGeometry)
open Purelib.Riemann.Periods.NewtonCanonicalPeriodData (ACanonicalPreparation BCanonicalPreparation)
open Purelib.Riemann.Periods.NewtonCanonicalPeriodReadback (canonicalPeriodSheet)
open Purelib.Riemann.Periods.NewtonCombinedPeriodArea (resplitPeriodMatrix)
open Purelib.Riemann.Periods.PeriodMatrix (sampledMatrix)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_antitone)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow firstQuarterBelow_accurate)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Retained A/B period preparations for one matrix position.

Keeps separate quarter-target preparations, numerical and fragment thresholds, and geometric sample-error witnesses at a
common index. -/
structure CanonicalMatrixEntry (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (geometry : PeriodGeometry base.bank.toBranchCellBank)
    (differential cycle : Fin genus) (target : Fraction.Rational) (minimum : Nat) where
  /-- Original A-cycle preparation at one quarter of the target. -/ a : ACanonicalPreparation prepared geometry
    differential cycle (target / 4) minimum
  /-- Original B-cycle preparation at one quarter of the target. -/ b : BCanonicalPreparation prepared geometry
    differential cycle (target / 4) minimum
  /-- Common numerical index retained by the entry or request. -/ index : Nat
  /-- The common entry index follows the A numerical threshold. -/ a_numerical : a.numericalIndex ≤ index
  /-- The common entry index follows the B numerical threshold. -/ b_numerical : b.numericalIndex ≤ index
  /-- The common entry index follows the A fragment threshold. -/ a_period : a.request.fragments.stage ≤ index
  /-- The common entry index follows the B fragment threshold. -/ b_period : b.request.fragments.stage ≤ index
  /-- The original A-program geometric error is at most one quarter of the target. -/ a_witness :
    Geometric.Basic.quarterRadius (max (prepared.periodData.aProgram differential cycle).integral.errorScale 1) index ≤
    target / 4
  /-- The original B-program geometric error is at most one quarter of the target. -/ b_witness :
    Geometric.Basic.quarterRadius (max (prepared.periodData.bProgram differential cycle).integral.errorScale 1) index ≤
    target / 4

constructive_injectivity CanonicalMatrixEntry

namespace CanonicalMatrixEntry

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Construct one canonical matrix entry with retained quarter-budget witnesses.

Builds A and B preparations, searches their original geometric error scales, and takes the maximum of numerical,
fragment and witness thresholds. -/
@[expose] def build (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (geometry : PeriodGeometry base.bank.toBranchCellBank)
    (differential cycle : Fin genus) (target : Fraction.Rational) (positive : 0 < target) (minimum : Nat) :
    CanonicalMatrixEntry prepared geometry differential cycle target minimum := by
  let partPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  let a := ACanonicalPreparation.build prepared geometry differential cycle (target / 4) partPositive minimum
  let b := BCanonicalPreparation.build prepared geometry differential cycle (target / 4) partPositive minimum
  let aScale := max (prepared.periodData.aProgram differential cycle).integral.errorScale 1
  let bScale := max (prepared.periodData.bProgram differential cycle).integral.errorScale 1
  have aNonnegative : 0 ≤ aScale := (by decide : (0 : Fraction.Rational) ≤ 1).trans (Fraction.Order.Basic.le_max_right _
    _)
  have bNonnegative : 0 ≤ bScale := (by decide : (0 : Fraction.Rational) ≤ 1).trans (Fraction.Order.Basic.le_max_right _
    _)
  let aWitness := Geometric.Search.firstQuarterBelow aScale minimum (target / 4)
  let bWitness := Geometric.Search.firstQuarterBelow bScale minimum (target / 4)
  let index := max (max a.numericalIndex b.numericalIndex)
    (max (max a.request.fragments.stage b.request.fragments.stage) (max aWitness bWitness))
  have numerics : max a.numericalIndex b.numericalIndex ≤ index := Data.Nat.Order.le_max_left _ _
  have periods : max a.request.fragments.stage b.request.fragments.stage ≤ index :=
    (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)
  have witnesses : max aWitness bWitness ≤ index :=
    (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)
  refine ⟨a, b, index, (Data.Nat.Order.le_max_left _ _).trans numerics, (Data.Nat.Order.le_max_right _ _).trans
    numerics,
    (Data.Nat.Order.le_max_left _ _).trans periods, (Data.Nat.Order.le_max_right _ _).trans periods, ?_, ?_⟩
  · exact (quarterRadius_antitone aNonnegative ((Data.Nat.Order.le_max_left _ _).trans
      witnesses)).trans
      (Geometric.Search.firstQuarterBelow_accurate aScale aNonnegative minimum (target / 4) partPositive).le
  · exact (quarterRadius_antitone bNonnegative ((Data.Nat.Order.le_max_right _ _).trans
      witnesses)).trans
      (Geometric.Search.firstQuarterBelow_accurate bScale bNonnegative minimum (target / 4) partPositive).le

end CanonicalMatrixEntry

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
/-- Dependent bank of canonical matrix entries by differential and cycle.

Every entry retains the same original period geometry, positive target and requested stage floor. -/
@[expose] def CanonicalMatrixEntries (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (geometry : PeriodGeometry base.bank.toBranchCellBank) (target : Fraction.Rational) (minimum : Nat) :=
  Vector.DependentVector (fun differential : Fin genus => Vector.DependentVector (fun cycle : Fin genus =>
    CanonicalMatrixEntry prepared geometry differential cycle target minimum))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Every retained matrix-entry index lies below the supplied index. -/
@[expose] def CanonicalMatrixEntries.IndexBound {prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}
    {geometry : PeriodGeometry base.bank.toBranchCellBank} {target : Fraction.Rational} {minimum : Nat}
    (entries : CanonicalMatrixEntries prepared geometry target minimum) (index : Nat) : Prop :=
  ∀ differential cycle, ((entries.get differential).get cycle).index ≤ index

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Canonical matrix comparison request with cached entries and a common index.

Retains target positivity and all differential/cycle entries, with a common stage after their thresholds and the
requested floor. -/
structure CanonicalMatrixRequest (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (geometry : PeriodGeometry base.bank.toBranchCellBank) (target : Fraction.Rational) (minimum : Nat) where
  /-- Strict positivity of the requested matrix target. -/ positive : 0 < target
  /-- Actual dependent bank of differential/cycle preparations. -/ entries : CanonicalMatrixEntries prepared geometry
    target minimum
  /-- Common numerical index retained by the entry or request. -/ index : Nat
  /-- The common request index respects the requested floor. -/ minimum_le : minimum ≤ index
  /-- Every retained matrix-entry index lies below the request index. -/ index_ge : entries.IndexBound index

constructive_injectivity CanonicalMatrixRequest

namespace CanonicalMatrixRequest

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
/-- Build all canonical matrix entries and their common stage.

Constructs the differential/cycle bank once and takes the maximum of the requested floor and all retained entry indices.
-/
@[expose] def build (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (geometry : PeriodGeometry base.bank.toBranchCellBank)
    (target : Fraction.Rational) (positive : 0 < target) (minimum : Nat) :
    CanonicalMatrixRequest prepared geometry target minimum := by
  let entries : CanonicalMatrixEntries prepared geometry target minimum := Vector.DependentVector.ofFn fun differential
    =>
    Vector.DependentVector.ofFn fun cycle => CanonicalMatrixEntry.build prepared geometry differential cycle target
      positive minimum
  let maximum := entries.maximum fun _ row => row.maximum fun _ entry => entry.index
  refine ⟨positive, entries, max minimum maximum, Data.Nat.Order.le_max_left _ _, ?_⟩
  intro differential cycle
  exact ((entries.get differential).get_le_maximum (fun _ entry => entry.index) cycle).trans
    ((entries.get_le_maximum (fun _ row => row.maximum fun _ entry => entry.index) differential).trans
      (Data.Nat.Order.le_max_right _ _))

variable {prepared : Prepared paired}
  {geometry : PeriodGeometry base.bank.toBranchCellBank} {target : Rational} {minimum : Nat}

open Purelib
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Riemann.RootContinuation
/-- Bound each canonical A-period matrix entry by the requested target.

At a stage after the retained common index, combines the actual canonical preparation and geometric sample-error
witness, keeping the original refined sheet and triangle cache. -/
theorem a_accurate (request : CanonicalMatrixRequest prepared geometry target minimum)
    (stage : Nat) (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics geometry.domains stage)
    (triangles : Vector.DependentVector (fun basis : Fin genus =>
      Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get basis) geometry.lifted.mesh))
    (later : request.index ≤ stage) (differential cycle : Fin genus) :
    let values := fun basis => Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation geometry.lifted.mesh
      (triangles.get basis).values
    let matrix := resplitPeriodMatrix prepared geometry.grid.shrunk.included geometry.lifted.edges
      geometry.lifted.vertices
      (canonicalPeriodSheet (lifted := lifted) (sheet := sheet) geometry) values false
    Data.Gaussian.Norm.Basic.normSq (matrix differential cycle - sampledMatrix prepared.periodData.aMatrix stage
      differential
      cycle) ≤ target := by
  intro values matrix
  let entry := (request.entries.get differential).get cycle
  have entryLater : entry.index ≤ stage := (request.index_ge differential cycle).trans later
  have positive := Fraction.Order.Field.div_pos_direct request.positive (by decide : (0 : Fraction.Rational) < 4)
  have close := NewtonCanonicalSampleComparison.ACanonicalPreparation.sample_accurate
    entry.a positive stage cache (triangles.get differential)
    (entry.a_numerical.trans entryLater) stage (entry.a_period.trans entryLater)
  have nonnegative : 0 ≤ max (prepared.periodData.aProgram differential cycle).integral.errorScale 1 :=
    (by decide : (0 : Fraction.Rational) ≤ 1).trans (Fraction.Order.Basic.le_max_right _ _)
  have witness := (quarterRadius_antitone nonnegative entryLater).trans entry.a_witness
  have paid : 2 * (target / 4 + Geometric.Basic.quarterRadius
      (max (prepared.periodData.aProgram differential cycle).integral.errorScale 1) stage) ≤ target := by
    calc
      _ ≤ 2 * (target / 4 + target / 4) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct (le_refl _) witness) (by decide)
      _ = target := (by ring1 : 2 * (target / 4 + target / 4) = target / 4 * 4).trans
        (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  change Data.Gaussian.Norm.Basic.normSq (resplitPeriodMatrix prepared geometry.grid.shrunk.included
    geometry.lifted.edges
    geometry.lifted.vertices
    (canonicalPeriodSheet (lifted := lifted) (sheet := sheet) geometry) values false differential cycle - _) ≤ target
  rw [resplitPeriodMatrix, LinearAlgebra.Matrix.matrixOfFn_apply]
  exact close.trans paid

/-- Bound each canonical B-period matrix entry by the requested target.

At a stage after the retained common index, combines the actual B preparation and geometric sample-error witness,
preserving the B-cycle selection and original cache. -/
theorem b_accurate (request : CanonicalMatrixRequest prepared geometry target minimum)
    (stage : Nat) (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics geometry.domains stage)
    (triangles : Vector.DependentVector (fun basis : Fin genus =>
      Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get basis) geometry.lifted.mesh))
    (later : request.index ≤ stage) (differential cycle : Fin genus) :
    let values := fun basis => Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation geometry.lifted.mesh
      (triangles.get basis).values
    let matrix := resplitPeriodMatrix prepared geometry.grid.shrunk.included geometry.lifted.edges
      geometry.lifted.vertices
      (canonicalPeriodSheet (lifted := lifted) (sheet := sheet) geometry) values true
    Data.Gaussian.Norm.Basic.normSq (matrix differential cycle - sampledMatrix prepared.periodData.bMatrix stage
      differential
      cycle) ≤ target := by
  intro values matrix
  let entry := (request.entries.get differential).get cycle
  have entryLater : entry.index ≤ stage := (request.index_ge differential cycle).trans later
  have positive := Fraction.Order.Field.div_pos_direct request.positive (by decide : (0 : Fraction.Rational) < 4)
  have close := NewtonCanonicalSampleComparison.BCanonicalPreparation.sample_accurate
    entry.b positive stage cache (triangles.get differential)
    (entry.b_numerical.trans entryLater) stage (entry.b_period.trans entryLater)
  have nonnegative : 0 ≤ max (prepared.periodData.bProgram differential cycle).integral.errorScale 1 :=
    (by decide : (0 : Fraction.Rational) ≤ 1).trans (Fraction.Order.Basic.le_max_right _ _)
  have witness := (quarterRadius_antitone nonnegative entryLater).trans entry.b_witness
  have paid : 2 * (target / 4 + Geometric.Basic.quarterRadius
      (max (prepared.periodData.bProgram differential cycle).integral.errorScale 1) stage) ≤ target := by
    calc
      _ ≤ 2 * (target / 4 + target / 4) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct (le_refl _) witness) (by decide)
      _ = target := (by ring1 : 2 * (target / 4 + target / 4) = target / 4 * 4).trans
        (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  change Data.Gaussian.Norm.Basic.normSq (resplitPeriodMatrix prepared geometry.grid.shrunk.included
    geometry.lifted.edges
    geometry.lifted.vertices
    (canonicalPeriodSheet (lifted := lifted) (sheet := sheet) geometry) values true differential cycle - _) ≤ target
  rw [resplitPeriodMatrix, LinearAlgebra.Matrix.matrixOfFn_apply]
  exact close.trans paid

end CanonicalMatrixRequest
end Purelib.Riemann.RootContinuation.NewtonCanonicalMatrixRequest
