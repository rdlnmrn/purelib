module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
public import Purelib.Riemann.Periods.WeightedPeriodNames
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Path.Lifted.Program
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree

open Purelib

open Purelib.Algebra

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Geometric

open Purelib.Approximation.Gaussian.Sequence

open Purelib.Approximation.Gaussian.Sequence.Name

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.WeightedPeriodNames

open Purelib.Riemann.Periods.WeightedPeriods

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.VertexSewing

public section

/-!
# Weighted periods of actual cut-mesh chains

All integer rows reuse one bank of root-safe component preparations. Each
differential has cached synchronized component streams. A chain period
retains its exact integer weights and is operationally the corresponding
finite combination of the certified component period names.
No connection between distinct component basepoints is invented.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Topology.Surface.Sewing.CutCycleChains (ClosedCutCycle CutCycleChain)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutCycleProgramBank)
open Purelib.Riemann.Periods.PeriodMatrix (geometricNamed)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Periods.WeightedPeriods (Coordinate GeometricApproximation Coefficients)
open Purelib.Riemann.Periods.WeightedPeriodNames (programApproximation)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

/-- A finite vector retaining its original entry count. -/
abbrev Vector := Data.Vector

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {source :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {count : Nat}
  {cycles : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.Vector
    (Purelib.Topology.Surface.Sewing.CutCycleChains.ClosedCutCycle lifted.cutPolygon.patch.cut.vertexLabels
    (lifted.cutPolygon.patch.cut.boundary.map (Purelib.Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
      lifted.cutPolygon.patch.cut.vertexLabels))) count}

set_option genInjectivity false in
/-- Cached geometric streams for the original component period programs.

Every stream sample is tied to the actual integral sample of its retained component model at the same stage. -/
structure ComponentSamples (bank : CyclePrograms.CutCycleProgramBank lifted source cycles) (differential : Fin genus)
  where
  /-- The cached geometric approximation for each original component program. -/ streams :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.Vector WeightedPeriods.GeometricApproximation count
  /-- Every cached stream stage equals its original component program integral sample. -/ samples_eq : ∀ index stage,
    (streams index).sample stage =
    (((bank.programs index).program differential).integral.model stage).integralSample

constructive_injectivity ComponentSamples

namespace ComponentSamples

variable {bank : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgramBank lifted source
  cycles} {differential : Fin genus}

/-- Cache the original component streams or their exact coefficient-weighted period without replacing the retained
program bank. -/
@[expose] def build (bank : CyclePrograms.CutCycleProgramBank lifted source cycles) (differential : Fin genus) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ComponentSamples bank differential :=
  ⟨vectorOfFn fun index => WeightedPeriodNames.programApproximation ((bank.programs index).program
    differential).integral,
    fun index stage => by rw [Data.Vector.Basic.vectorOfFn_apply]; rfl⟩

/-- The cached geometric output agrees operationally with the original retained named period programs. -/
@[expose] def output_equivalent (components :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ComponentSamples bank differential) (index : Fin count) :
    Gaussian.Equivalence.NamedEquivalent ((bank.programs index).program differential).output.name
      (PeriodMatrix.geometricNamed (components.streams index)).name :=
  Equivalence.approximationEquivalent_toNamed
    (Equivalence.approximationEquivalentOfSamplesEq
      ((bank.programs index).program differential).integral.approximation
      (components.streams index).toApproximation (fun stage => (components.samples_eq index stage).symm))

end ComponentSamples

set_option genInjectivity false in
/-- A weighted stream whose samples remain tied to the original certified component models. Alternative checked scales
and cached streams are allowed. -/
structure ChainPeriod {bank : CyclePrograms.CutCycleProgramBank lifted source cycles} {differential : Fin genus}
    (components : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ComponentSamples bank differential)
      (weights : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.Vector Int count) where
  /-- The retained integer weights indexed by the original component bank. -/ coefficients :
    WeightedPeriods.Coefficients weights
  /-- The cached geometric approximation of the original weighted chain period. -/ approximation :
    WeightedPeriods.GeometricApproximation
  /-- The cached sample is exactly the retained coefficient combination of the original component streams. -/ sample_eq
    : ∀ stage, approximation.sample stage =
    coefficients.combine (fun index => (components.streams index).sample stage)

constructive_injectivity ChainPeriod

namespace ChainPeriod

variable {bank : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgramBank lifted source
  cycles} {differential : Fin genus}
  {components : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ComponentSamples bank differential}
    {weights : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.Vector Int count}

/-- Cache the original component streams or their exact coefficient-weighted period without replacing the retained
program bank. -/
@[expose] def build (components : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ComponentSamples bank
  differential) (weights : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.Vector Int count) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ChainPeriod components weights :=
  let coefficients := Coefficients.build weights
  ⟨coefficients, coefficients.approximation components.streams, fun _ => rfl⟩

/-- Read the original integer-weighted component cycle chain from the retained program bank. -/
@[expose] def chain (_period : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ChainPeriod components
  weights) :
    CutCycleChains.CutCycleChain lifted.cutPolygon.patch.cut.vertexLabels
      (lifted.cutPolygon.patch.cut.boundary.map (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels)) :=
  ⟨count, cycles, weights⟩

/-- The retained integer-weighted component chain has zero boundary. -/
theorem chain_closed (period : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ChainPeriod components
  weights) (vertex : Fin lifted.vertices.count) :
    period.chain.boundary vertex = 0 := period.chain.boundary_zero vertex

/-- The geometric named output of the cached original chain-period approximation. -/
@[expose] def output (period : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ChainPeriod components
  weights) : CoherentNamed := PeriodMatrix.geometricNamed period.approximation

/-- Negate the original coefficient vector and cached stream, retaining the same component program bank. -/
@[expose] def negate (period : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ChainPeriod components
  weights) : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ChainPeriod components
  (Data.Vector.Basic.vectorOfFn fun index => -weights index) :=
  ⟨period.coefficients.negate, period.approximation.neg,
    fun stage => by rw [GeometricApproximation.neg_sample, period.sample_eq,
      period.coefficients.negate_combine]⟩

/-- Negating the retained period gives exactly the negation of its original component chain. -/
theorem negate_chain (period : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ChainPeriod components
  weights) : period.negate.chain = period.chain.negate := rfl

/-- Each cached chain sample is the exact integer-weighted sum of the original component model samples. -/
theorem sample_eq_programs (period : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ChainPeriod components
  weights) (stage : Nat) :
    period.approximation.sample stage = FiniteSum.Fin.sumFin (fun index => (weights index :
      Data.Gaussian.Basic.Canonical) *
      (((bank.programs index).program differential).integral.model stage).integralSample) := by
  rw [period.sample_eq, period.coefficients.combine_eq]
  exact FiniteSum.Fin.sumFin_congr fun index => congrArg (fun value => (weights index : Data.Gaussian.Basic.Canonical) *
    value) (components.samples_eq index stage)

/-- The cached geometric output agrees operationally with the original retained named period programs. -/
@[expose] def output_equivalent (period : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ChainPeriod
  components weights) :
    Gaussian.Equivalence.NamedEquivalent (Coefficients.named period.coefficients
      (fun index => ((bank.programs index).program differential).output)).name
      period.output.name :=
  (Coefficients.named_equivalent
    period.coefficients _ components.streams components.output_equivalent).trans
    (Equivalence.approximationEquivalent_toNamed
      (Equivalence.approximationEquivalentOfSamplesEq
        (period.coefficients.approximation components.streams).toApproximation period.approximation.toApproximation
        (fun stage => (period.sample_eq stage).symm)))

/-- Any component comparison is charged with the actual integer row. There is no assumption that the coefficient
amplification is at most one. -/
theorem comparison_bound (period : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ChainPeriod components
  weights) (values : Fin count → Data.Gaussian.Basic.Canonical) (stage : Nat)
    (bounds : Fin count → WeightedPeriods.Coordinate)
    (bounded : ∀ index, Data.Gaussian.Norm.Basic.normSq
      (values index - (((bank.programs index).program differential).integral.model stage).integralSample) ≤ bounds
        index) :
    Data.Gaussian.Norm.Basic.normSq
      (period.coefficients.combine values - period.approximation.sample stage) ≤ period.coefficients.charge bounds := by
  rw [period.sample_eq]
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  apply period.coefficients.normSq_difference_le
  intro index
  rw [components.samples_eq]
  have scalar := bounded index
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
  exact scalar

end ChainPeriod
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
