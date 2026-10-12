module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.LinearAlgebra.Matrix.Basic

public import Purelib.Approximation.Budget.WeightedRowBudgets
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodSamples
import Purelib.Topology.Surface.Boundary.NormalFormErrorBounds
import Init.Data.Int.Basic
import Init.Prelude
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.LinearAlgebra.Alternating.Reduction.CycleRows
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree

open Purelib

open Purelib.Algebra

open Purelib.Approximation.Budget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods

open Purelib.Data.Vector

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

@[expose] public section

/-!
# Cached normal-form coefficient profiles and common-stage row samples

The profile reuses the actual period coefficients. Sampling the rows takes
an already materialized component vector and never evaluates a component
stream again. The retained values are exactly the original period samples.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Topology.Surface.Sewing.CutCycleChains (ClosedCutCycle)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutCycleProgramBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods (ComponentSamples)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (NormalFormPeriods)
open Purelib.Riemann.Periods.WeightedPeriods (Coefficients Coordinate)
open Purelib.Approximation.Budget.WeightedRowBudgets (CoefficientRows)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.LinearAlgebra.Matrix (IntegralMatrix)
open Purelib.LinearAlgebra.Alternating.Handle.Basic (PivotIndices)
open _root_.Purelib.LinearAlgebra.Alternating (NormalForm)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin_congr)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

/-- The finite vector representation retained by the original normal-form period bank. -/
abbrev Vector := Data.Vector

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {source :
    Differential genus} {count : Nat}
  {cycles : Vector
    (ClosedCutCycle lifted.cutPolygon.patch.cut.vertexLabels
    (lifted.cutPolygon.patch.cut.boundary.map (Purelib.Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
      lifted.cutPolygon.patch.cut.vertexLabels))) count}
  {bank : CutCycleProgramBank lifted source cycles}
    {differential : Fin genus}
  {components : ComponentSamples bank differential}
    {matrix : IntegralMatrix count}
  {raw : List (PivotIndices count)} {normal :
    LinearAlgebra.Alternating.NormalForm matrix raw}

/-- Transport the original coefficient certificate across equality of its exact integer weight vectors. -/
public def coefficientsAt {count : Nat} {first last :
  Vector Int count} (equal : first = last)
    (coefficients : WeightedPeriods.Coefficients first) : WeightedPeriods.Coefficients last := by
  cases equal
  exact coefficients

/-- Transporting the original coefficient certificate preserves its cached mass. -/
private theorem coefficientsAt_mass {count : Nat} {first last :
  Vector Int count} (equal : first = last)
    (coefficients : WeightedPeriods.Coefficients first) :
      (coefficientsAt equal coefficients).mass =
      coefficients.mass := by
  cases equal
  rfl

set_option genInjectivity false in
/-- The original normal-form period coefficients collected into a shared row budget profile.

Every row keeps the mass of its actual retained period coefficients after exact weight-vector transport. -/
structure Profile (periods : NormalFormPeriods components normal) where
  /-- The shared coefficient row cache for the original normal-form reduction matrix. -/ rows :
    WeightedRowBudgets.CoefficientRows normal.reduction.cycleRows
  /-- Each profile row has exactly the mass of the original period's retained coefficient certificate. -/ masses_eq : ∀
    row, (rows.coefficients.get row).mass = (periods.rows row).period.coefficients.mass

constructive_injectivity Profile

namespace Profile

variable {periods :
  NormalFormPeriods components
  normal}

/-- Collect the original retained period coefficients after exact weight transport, preserving all row masses. -/
def build (periods : NormalFormPeriods components normal) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples.Profile periods :=
  let coefficients := DependentVector.ofFn fun row =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples.coefficientsAt (periods.weights_eq row)
    (periods.rows row).period.coefficients
  ⟨CoefficientRows.ofCoefficients coefficients, fun row => by
    change (coefficients.get row).mass = _
    rw [DependentVector.ofFn_get]
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples.coefficientsAt_mass _ _⟩

/-- Every original period coefficient mass is bounded by the common cached row-profile total. -/
theorem mass_le_total (profile : Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples.Profile periods) (row : Fin
  count) : (periods.rows row).period.coefficients.mass ≤ profile.rows.total := by
  rw [← profile.masses_eq]
  exact profile.rows.mass_le_total row

end Profile

set_option genInjectivity false in
/-- The common-stage normal-form rows evaluated from one retained component vector.

Exact component and weighted-row readbacks preserve the original streams without evaluating them again. -/
structure Sample (periods : NormalFormPeriods components normal) (stage : Nat) where
  /-- The already materialized original component values at the retained common stage. -/ componentValues :
    Vector Data.Gaussian.Basic.Canonical count
  /-- Each retained component equals the original stream sample at that exact stage. -/ components_eq : ∀ index,
    componentValues index = (components.streams index).sample stage
  /-- The cached original weighted row values at the common component stage. -/ rows :
    Vector Data.Gaussian.Basic.Canonical count
  /-- Each row is the original retained coefficient combination of the cached component vector. -/ rows_eq : ∀ row, rows
    row = (periods.rows row).period.coefficients.combine componentValues

constructive_injectivity Sample

namespace Sample

variable {periods :
  NormalFormPeriods components
  normal} {stage : Nat}

/-- Evaluate all original weighted period rows from the supplied already materialized component vector. -/
def ofComponents (periods : NormalFormPeriods components normal) (stage : Nat)
    (values : Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples.Vector Data.Gaussian.Basic.Canonical count)
      (equal : ∀ index, values index = (components.streams index).sample stage) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples.Sample periods stage :=
  ⟨values, equal, Data.Vector.Basic.vectorOfFn fun row => (periods.rows row).period.coefficients.combine values,
    Data.Vector.Basic.vectorOfFn_apply _⟩

/-- Each cached normal-form row is exactly its original weighted period sample at the common stage. -/
theorem row_eq_period (sample : Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples.Sample periods stage) (row :
  Fin count) :
    sample.rows row = (periods.rows row).period.approximation.sample stage := by
  rw [sample.rows_eq, (periods.rows row).period.sample_eq]
  unfold WeightedPeriods.Coefficients.combine
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [sample.components_eq]

/-- The original row coefficient mass bounds the weighted primitive discrepancy from the retained componentwise bound.
-/
theorem row_comparison (sample : Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples.Sample periods stage)
    (primitive : Fin lifted.cutPolygon.patch.cut.count → Stokes.PrimitivePoint) {bound : WeightedPeriods.Coordinate}
    (bounded : ∀ index, Data.Gaussian.Norm.Basic.normSq (((cycles index).increment primitive).right -
      sample.componentValues index) ≤ bound) (row : Fin count) :
    Data.Gaussian.Norm.Basic.normSq (((periods.rows row).period.chain.increment primitive).right - sample.rows
      row) ≤
      (periods.rows row).period.coefficients.mass * bound := by
  rw [sample.rows_eq]
  have equal : ((periods.rows row).period.chain.increment primitive).right =
      (periods.rows row).period.coefficients.combine (fun index => ((cycles index).increment primitive).right) := by
    rw [(periods.rows row).period.coefficients.combine_eq]
    rfl
  rw [equal]
  have estimate := (periods.rows row).period.coefficients.normSq_difference_le
    (fun index => ((cycles index).increment primitive).right) sample.componentValues (fun _ => bound)
    (fun index => by
      have scalar := bounded index
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar)
  rw [(periods.rows row).period.coefficients.charge_constant] at estimate
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  exact estimate

end Sample
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples
