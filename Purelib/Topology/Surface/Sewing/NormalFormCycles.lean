module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Pairing
import Purelib.LinearAlgebra.Alternating.Handle.UnitPairing
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.LinearAlgebra.Bilinear.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Vector.IntCast
import Purelib.LinearAlgebra.Vector.Unit

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.Pairing
public import Purelib.Topology.Surface.Sewing.ChordCycleBank
public import Purelib.Topology.Surface.Boundary.NormalFormArea
import Purelib.Data.Gaussian.Basic
public import Purelib.LinearAlgebra.Alternating.Reduction.CycleRows
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint
import Purelib.LinearAlgebra.Alternating.NormalForm.Evaluation

open Purelib.LinearAlgebra.Alternating (NormalForm)

open Purelib

open Purelib.Algebra

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Alternating.Handle

open Purelib.LinearAlgebra.Bilinear

open Purelib.LinearAlgebra.Vector

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.IntegralPairing

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.CutCycleChains

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Surface.Word

/-!
# Actual closed chains for the dual handle coordinates

The computed integer cycle rows act on a cached bank of actual chord paths.
The resulting chains remain closed on the surface, while their cut-primitive
increments equal the dual handle values with the separately transported
physical-boundary and local-error corrections. Analytic period identification
is not assumed by this finite identity.
-/

public section

namespace Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open Purelib.Topology.Surface.Sewing.CutCycleChains (CutCycleChain)

open Purelib.Topology.Surface.Sewing.ChordCycleBank
open _root_.Purelib.Topology.Surface.Sewing renaming ChordCycleBank -> ChordCycleBank
open Purelib.Topology.Surface.Boundary.NormalFormArea
open _root_.Purelib.Topology.Surface.Boundary renaming NormalFormArea -> NormalFormArea

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint)

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin_congr sumFin_add sumFin_mul_left)
open Purelib.LinearAlgebra.Alternating

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}
  {word : BoundaryWord.CutBoundaryWord labels edges} {pairing : Cut.IntegralPairing.CutBoundaryWord word}
  {primitive : Fin source → Stokes.PrimitivePoint}
  {values : Data.Vector Stokes.PrimitivePoint word.alphabet.count}
  {routes : ChordCycleBank word}
  {raw : List (Handle.Basic.PivotIndices word.alphabet.count)}

set_option genInjectivity false in
/-- Actual closed cut-cycle chains for the original computed normal-form rows.

The retained integer weights act on one fixed chord bank; separate jump, physical and local-error caches preserve the
complete primitive readback. -/
structure NormalFormCycles (normal : NormalForm pairing.paired raw) (bank :
  ChordCycleBank.Sample
  routes pairing primitive values) where
  /-- Cached integer rows computed by the original retained normal-form reduction. -/ weights :
    LinearAlgebra.Matrix.IntegralMatrix word.alphabet.count
  /-- The weights are exactly the original reduction's cycle rows. -/ weights_eq : weights = normal.reduction.cycleRows
  /-- Cached actual integer combinations of the original chord cycles. -/ chains : Data.Vector
    (CutCycleChains.CutCycleChain labels (edges.map (OrientedEdge.map labels))) word.alphabet.count
  /-- Each chain reuses the original chord-cycle bank with its retained row weights. -/ chains_eq : ∀ row, chains row =
    ⟨word.alphabet.count, routes.cycles, weights row⟩
  /-- Cached integer-weighted original chord jumps. -/ jumps : Data.Vector Stokes.PrimitivePoint
    word.alphabet.count
  /-- Each jump is the weighted reading of the original sample jump vector. -/ jumps_eq : ∀ row, jumps row =
    Pairing.linear (weights row) bank.jumps
  /-- Cached integer-weighted physical contributions. -/ physical : Data.Vector Stokes.PrimitivePoint
    word.alphabet.count
  /-- Each physical contribution uses the same original row weights and sample bank. -/ physical_eq : ∀ row, physical
    row = Pairing.linear (weights row) bank.physical
  /-- Cached integer-weighted local increment errors. -/ errors : Data.Vector Stokes.PrimitivePoint
    word.alphabet.count
  /-- Each transported error uses the same original row weights and sample bank. -/ errors_eq : ∀ row, errors row =
    Pairing.linear (weights row) bank.errors

constructive_injectivity NormalFormCycles

namespace NormalFormCycles

variable {normal : NormalForm pairing.paired raw} {bank : ChordCycleBank.Sample routes pairing
  primitive values}

/-- Cache original normal-form cycle weights, actual chains and all three transported sample readings. -/
@[expose] def build (normal : NormalForm pairing.paired raw) (bank : ChordCycleBank.Sample
  routes
  pairing primitive values) :
    NormalFormCycles normal bank :=
  let weights := normal.reduction.cycleRows
  { weights := weights, weights_eq := rfl
    chains := Data.Vector.Basic.vectorOfFn fun row => ⟨word.alphabet.count, routes.cycles, weights row⟩
    chains_eq := Data.Vector.Basic.vectorOfFn_apply _
    jumps := Data.Vector.Basic.vectorOfFn fun row => Pairing.linear (weights row) bank.jumps
    jumps_eq := Data.Vector.Basic.vectorOfFn_apply _
    physical := Data.Vector.Basic.vectorOfFn fun row => Pairing.linear (weights row) bank.physical
    physical_eq := Data.Vector.Basic.vectorOfFn_apply _
    errors := Data.Vector.Basic.vectorOfFn fun row => Pairing.linear (weights row) bank.errors
    errors_eq := Data.Vector.Basic.vectorOfFn_apply _ }

/-- Evaluating an original retained normal-form chain gives its cached primitive jump. -/
theorem increment_eq (sample : NormalFormCycles normal bank) (row : Fin word.alphabet.count) :
    (sample.chains row).increment primitive = sample.jumps row := by
  rw [sample.chains_eq, sample.jumps_eq]
  change Pairing.linear (sample.weights row) (fun index => (routes.cycles index).increment primitive) = _
  exact Pairing.linear_values_congr (sample.weights row) bank.cycle_jump

/-- Refining either primitive changes the readings, not the underlying normal-form chains. This applies to alternative
checked sample caches too. -/
theorem chains_independent (sample : NormalFormCycles normal bank)
    {otherPrimitive : Fin source → Stokes.PrimitivePoint}
    {otherValues : Data.Vector Stokes.PrimitivePoint word.alphabet.count}
    {otherBank : ChordCycleBank.Sample routes pairing otherPrimitive otherValues}
    (other : NormalFormCycles normal otherBank) : sample.chains = other.chains := by
  apply Data.Vector.Basic.vector_ext
  intro row
  rw [sample.chains_eq, other.chains_eq, sample.weights_eq, other.weights_eq]

/-- Each cached normal-form jump is its dual handle reading plus transported physical and error terms. -/
theorem row_decomposition (sample : NormalFormCycles normal bank) (evaluated :
  Boundary.NormalFormArea normal values)
    (row : Fin word.alphabet.count) :
    sample.jumps row = ((⟨Pairing.handlePairing raw (Unit.unitVector row) evaluated.left,
      Pairing.handlePairing raw (Unit.unitVector row) evaluated.right⟩ : Stokes.PrimitivePoint).add (sample.physical
        row)).add (sample.errors row) := by
  have source := Pairing.linear_values_congr (fun index => sample.weights row index) (bank.row_eq)
  rw [Pairing.linear_values_add, Pairing.linear_values_add, Pairing.linear_rows] at source
  rw [sample.jumps_eq, sample.physical_eq, sample.errors_eq, source, sample.weights_eq,
    normal.cycleRow_pairing, normal.cycleRow_pairing, ← evaluated.left_eq, ← evaluated.right_eq]

/-- The oriented handle is minus the second cycle row, followed by the first cycle row. This is forced by the positive
unit-pivot convention. -/
@[expose] def handleFirst (sample : NormalFormCycles normal bank) (pair : Handle.Basic.PivotIndices
  word.alphabet.count) :
    CutCycleChains.CutCycleChain labels (edges.map (OrientedEdge.map labels)) := (sample.chains pair.2).negate

/-- Select the original first pivot cycle row as the second oriented handle chain. -/
@[expose] def handleLast (sample : NormalFormCycles normal bank) (pair : Handle.Basic.PivotIndices
  word.alphabet.count) :
    CutCycleChains.CutCycleChain labels (edges.map (OrientedEdge.map labels)) := sample.chains pair.1

/-- The first oriented handle increment is the original first handle point minus its full physical and error correction.
-/
theorem handleFirst_increment (sample : NormalFormCycles normal bank) (evaluated :
  Boundary.NormalFormArea normal values)
    (pair : Handle.Basic.PivotIndices word.alphabet.count) (member : pair ∈ raw) :
    (sample.handleFirst pair).increment primitive =
      (PrimitivePoint.sub (evaluated.points pair.1)) ((sample.physical pair.2).add (sample.errors pair.2)) := by
  have left := (UnitPairing.handlePairing_unit_handle raw normal.disjoint pair member evaluated.left).2
  have right := (UnitPairing.handlePairing_unit_handle raw normal.disjoint pair member evaluated.right).2
  rw [handleFirst, CutCycleChain.increment_negate, sample.increment_eq, sample.row_decomposition
    evaluated,
    left, right, evaluated.points_eq, Data.Vector.Basic.vectorOfFn_apply]
  simp only [PrimitivePoint.zero, PrimitivePoint.sub, PrimitivePoint.add]
  congr 1 <;> ring1

/-- The second oriented handle increment is the original second handle point plus its full physical and error
correction. -/
theorem handleLast_increment (sample : NormalFormCycles normal bank) (evaluated :
  Boundary.NormalFormArea normal values)
    (pair : Handle.Basic.PivotIndices word.alphabet.count) (member : pair ∈ raw) :
    (sample.handleLast pair).increment primitive =
      ((evaluated.points pair.2).add (sample.physical pair.1)).add (sample.errors pair.1) := by
  have left := (UnitPairing.handlePairing_unit_handle raw normal.disjoint pair member evaluated.left).1
  have right := (UnitPairing.handlePairing_unit_handle raw normal.disjoint pair member evaluated.right).1
  rw [handleLast, sample.increment_eq, sample.row_decomposition evaluated, left, right,
    evaluated.points_eq, Data.Vector.Basic.vectorOfFn_apply]

end NormalFormCycles
end Purelib.Topology.Surface.Sewing
