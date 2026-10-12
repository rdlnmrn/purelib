module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.LinearAlgebra.Matrix.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.NormalFormArea
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.CutCycleChains
public import Purelib.Topology.Surface.Sewing.NormalFormCycles
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Init.Data.Int.Basic
import Init.Prelude
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.LinearAlgebra.Alternating.Reduction.CycleRows
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
meta import Mathlib.Tactic.Linter.Lint
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods

open Purelib.LinearAlgebra.Alternating

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.CutCycleChains

open Purelib.Topology.Surface.Sewing.NormalFormCycles
open _root_.Purelib.Topology.Surface.Sewing renaming NormalFormCycles -> NormalFormCycles

@[expose] public section

/-!
# Period rows for the actual integral normal form

The integer row matrix is computed once. Every row shares the cached
component streams, and each handle uses minus row q followed by row p.
The resulting periods retain the very closed chains given by those weights.
This does not yet assert that the handle count equals the curve genus or
identify the weighted integrals with the cut-primitive coordinates.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Topology.Surface.Sewing.CutCycleChains (ClosedCutCycle CutCycleChain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
    (CutCycleProgramBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods (ComponentSamples ChainPeriod)
open Purelib.LinearAlgebra.Matrix (IntegralMatrix)
open Purelib.LinearAlgebra.Alternating.Handle.Basic (PivotIndices)
open _root_.Purelib.LinearAlgebra.Alternating (NormalForm)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

namespace NormalFormPeriods.CutCycleProgramBank

/-- A finite vector retaining its original entry count. -/
abbrev Vector := Data.Vector

end NormalFormPeriods.CutCycleProgramBank

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {source :
    Differential genus} {count : Nat}
  {cycles : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods.CutCycleProgramBank.Vector
    (ClosedCutCycle lifted.cutPolygon.patch.cut.vertexLabels
    (lifted.cutPolygon.patch.cut.boundary.map (Purelib.Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
      lifted.cutPolygon.patch.cut.vertexLabels))) count}
  {bank : CutCycleProgramBank lifted source cycles}
    {differential : Fin genus}

namespace NormalFormPeriods.CutCycleProgramBank

set_option genInjectivity false in
/-- A homogeneous cache entry packages its integer row with the period whose type records those exact weights. -/
structure WeightedRow (components : ChainPeriods.ComponentSamples bank differential) where
  /-- The retained original integer coefficient vector for this cached period. -/ weights :
    Vector Int count
  /-- The cached chain period indexed by these exact original integer weights. -/ period : ChainPeriods.ChainPeriod
    components weights

constructive_injectivity WeightedRow

end NormalFormPeriods.CutCycleProgramBank

namespace NormalFormPeriods.CutCycleProgramBank.WeightedRow

variable {components : ComponentSamples bank
  differential}

/-- Cache the original integer-weighted period rows over the retained component streams. -/
def build (components : ChainPeriods.ComponentSamples bank differential) (weights :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods.CutCycleProgramBank.Vector Int count) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods.CutCycleProgramBank.WeightedRow components :=
  ⟨weights, ChainPeriod.build components weights⟩

/-- Negate the original integer row and its cached period while retaining the component bank. -/
def negate (row : Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods.CutCycleProgramBank.WeightedRow
  components) : Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods.CutCycleProgramBank.WeightedRow components
  :=
  ⟨vectorOfFn fun index => -row.weights index, row.period.negate⟩

end NormalFormPeriods.CutCycleProgramBank.WeightedRow

set_option genInjectivity false in
/-- Cached periods for the exact integer rows of an original alternating normal form.

Every retained row keeps its actual coefficient vector and shares the original component streams; the certificate ties
each vector to the computed reduction. -/
structure NormalFormPeriods (components : ChainPeriods.ComponentSamples bank differential)
    {matrix : LinearAlgebra.Matrix.IntegralMatrix count} {raw : List
      (Handle.Basic.PivotIndices count)} (normal : LinearAlgebra.Alternating.NormalForm matrix raw) where
  /-- The cached period entries for every original normal-form row. -/ rows :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods.CutCycleProgramBank.Vector
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods.CutCycleProgramBank.WeightedRow components) count
  /-- Each cached row uses exactly the original reduction's integer cycle weights. -/ weights_eq : ∀ row, (rows
    row).weights = normal.reduction.cycleRows row

constructive_injectivity NormalFormPeriods

namespace NormalFormPeriods

variable {components : ComponentSamples bank
  differential} {matrix : IntegralMatrix count}
  {raw : List (PivotIndices count)} {normal :
    LinearAlgebra.Alternating.NormalForm matrix raw}

/-- Cache the original integer-weighted period rows over the retained component streams. -/
def build (components : ChainPeriods.ComponentSamples bank differential) (normal : LinearAlgebra.Alternating.NormalForm
  matrix
  raw) : NormalFormPeriods components
  normal :=
  let weights := normal.reduction.cycleRows
  ⟨vectorOfFn fun row =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods.CutCycleProgramBank.WeightedRow.build components
    (weights row), fun row => by rw [Data.Vector.Basic.vectorOfFn_apply]; rfl⟩

/-- Read the original handle's negative second row with its cached period. -/
def first (periods : NormalFormPeriods
  components normal) (pair : Handle.Basic.PivotIndices count) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods.CutCycleProgramBank.WeightedRow components :=
  (periods.rows pair.2).negate

/-- Read the original handle's first row with its cached period. -/
def last (periods : NormalFormPeriods
  components normal) (pair : Handle.Basic.PivotIndices count) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods.CutCycleProgramBank.WeightedRow components :=
  periods.rows pair.1

/-- Each cached row period retains exactly the original component chain with its computed normal-form weights. -/
theorem row_chain (periods :
  NormalFormPeriods components normal)
  (row : Fin count) :
    (periods.rows row).period.chain = ⟨count, cycles, normal.reduction.cycleRows row⟩ := by
  change CutCycleChain.mk count cycles (periods.rows row).weights = _
  rw [periods.weights_eq]

/-- The original first handle period retains the negation of the actual second-row component chain. -/
theorem first_chain (periods :
  NormalFormPeriods components normal)
  (pair : Handle.Basic.PivotIndices count) :
    (periods.first pair).period.chain =
      (CutCycleChain.mk count cycles (normal.reduction.cycleRows pair.2)).negate := by
  change (periods.rows pair.2).period.negate.chain = _
  rw [ChainPeriod.negate_chain, periods.row_chain]

/-- The original last handle period retains exactly the actual first-row component chain. -/
theorem last_chain (periods :
  NormalFormPeriods components normal)
  (pair : Handle.Basic.PivotIndices count) :
    (periods.last pair).period.chain = CutCycleChain.mk count cycles (normal.reduction.cycleRows pair.1) :=
      periods.row_chain _

/-- The original first handle sample is the negative cached second-row sample at the same stage. -/
theorem first_sample (periods :
  NormalFormPeriods components normal)
  (pair : Handle.Basic.PivotIndices count) (stage : Nat) :
    (periods.first pair).period.approximation.sample stage =
      -(periods.rows pair.2).period.approximation.sample stage := rfl

/-- The original last handle sample is exactly the cached first-row sample at the same stage. -/
theorem last_sample (periods :
  NormalFormPeriods components normal)
  (pair : Handle.Basic.PivotIndices count) (stage : Nat) :
    (periods.last pair).period.approximation.sample stage = (periods.rows pair.1).period.approximation.sample stage :=
      rfl

/-- Only actual retained pivots index this bank. Its length is the computed handle count; identifying that count with
genus remains a separate theorem. -/
def handles (periods : NormalFormPeriods
  components normal) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods.CutCycleProgramBank.Vector
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods.CutCycleProgramBank.WeightedRow components ×
      Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods.CutCycleProgramBank.WeightedRow components) raw.length
      :=
  Data.Vector.Basic.vectorOfFn fun index => (periods.first raw[index.val], periods.last raw[index.val])

end NormalFormPeriods
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods.CutChordPrograms

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutChordPrograms)
open _root_.Purelib.Topology.Surface.Sewing (NormalFormCycles)
open _root_.Purelib.Topology.Surface.Boundary (NormalFormArea)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open Purelib.Topology.Surface.Cut.BoundaryWord.ProjectedEdgePairing (boundaryWord)
open Purelib.LinearAlgebra.Alternating.Handle.Basic (PivotIndices)
open _root_.Purelib.LinearAlgebra.Alternating (NormalForm)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods (ComponentSamples)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (NormalFormPeriods)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {source :
    Differential genus}
  {prepared : CutChordPrograms lifted source}
  {pairing : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {primitive : Fin lifted.cutPolygon.patch.cut.count → Purelib.Topology.Polygon.Stokes.PrimitivePoint}
  {values : Data.Vector Purelib.Topology.Polygon.Stokes.PrimitivePoint
    lifted.cutBoundaryWord.alphabet.count}
  {samples : prepared.routes.Sample pairing primitive values}
  {differential : Fin genus} {components :
    ComponentSamples prepared.programs differential}
  {raw : List (PivotIndices lifted.cutBoundaryWord.alphabet.count)}
    {normal : LinearAlgebra.Alternating.NormalForm pairing.paired raw}

/-- The analytic row and every refined cut-primitive sample refer to the same actual chain, not merely to
equal-dimensional coordinate vectors. -/
theorem row_chain_eq (periods :
  NormalFormPeriods components normal)
    (sample : Topology.Surface.Sewing.NormalFormCycles normal samples) (row : Fin
      lifted.cutBoundaryWord.alphabet.count) :
    (periods.rows row).period.chain = sample.chains row := by
  rw [periods.row_chain, sample.chains_eq, sample.weights_eq]

/-- The first analytic handle's retained cut increment has the exact dual coordinate and both corrections. This is chain
provenance, not an assertion that the analytic period already equals an arbitrary primitive reading. -/
theorem first_increment (periods :
  NormalFormPeriods components normal)
    (sample : Topology.Surface.Sewing.NormalFormCycles normal samples) (evaluated :
      Topology.Surface.Boundary.NormalFormArea normal
      values)
    (pair : Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count) (member : pair ∈ raw) :
    (periods.first pair).period.chain.increment primitive =
      (evaluated.points pair.1).sub ((sample.physical pair.2).add (sample.errors pair.2)) := by
  have same : (periods.first pair).period.chain = sample.handleFirst pair := by
    rw [periods.first_chain, NormalFormCycles.handleFirst, sample.chains_eq, sample.weights_eq]
  rw [same]
  exact sample.handleFirst_increment evaluated pair member

/-- The original last handle chain increment retains the exact dual coordinate and both physical and error corrections.
-/
theorem last_increment (periods :
  NormalFormPeriods components normal)
    (sample : Topology.Surface.Sewing.NormalFormCycles normal samples) (evaluated :
      Topology.Surface.Boundary.NormalFormArea normal
      values)
    (pair : Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count) (member : pair ∈ raw) :
    (periods.last pair).period.chain.increment primitive =
      ((evaluated.points pair.2).add (sample.physical pair.1)).add (sample.errors pair.1) := by
  have same : (periods.last pair).period.chain = sample.handleLast pair := by
    rw [periods.last_chain, NormalFormCycles.handleLast, sample.chains_eq, sample.weights_eq]
  rw [same]
  exact sample.handleLast_increment evaluated pair member

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods.CutChordPrograms
