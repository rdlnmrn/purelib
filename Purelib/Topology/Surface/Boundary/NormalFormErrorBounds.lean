module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.NormalFormArea
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.CutCycleChains
public import Purelib.Topology.Surface.Sewing.NormalFormCycles
public import Purelib.Approximation.Budget.WeightedRowBudgets
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Vector.Dependent
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Init
import Purelib.Riemann.Periods.WeightedPeriods
import Mathlib.Data.Int.Cast.Defs
import Purelib.LinearAlgebra.Alternating.Reduction.CycleRows
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Budget

open Purelib.Approximation.Budget.WeightedRowBudgets

open Purelib.Data

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.IntegralPairing

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.ChordCycleBank
open _root_.Purelib.Topology.Surface.Sewing renaming ChordCycleBank -> ChordCycleBank

open Purelib.Topology.Surface.Sewing.CutCycleChains

open Purelib.Topology.Surface.Sewing.NormalFormCycles
open _root_.Purelib.Topology.Surface.Sewing renaming NormalFormCycles -> NormalFormCycles

public section

/-!
# Chord errors after the actual integral change of basis

Cached coefficient masses pay every transformed row and both orientations
of each retained handle. Physical-boundary coordinates remain separate.
-/

namespace Purelib.Topology.Surface.Boundary.NormalFormErrorBounds

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint)

open Purelib.Approximation.Budget.WeightedRowBudgets (CoefficientRows)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open _root_.Purelib.Topology.Surface.Sewing (ChordCycleBank)
open _root_.Purelib.Topology.Surface.Boundary (NormalFormArea)
open _root_.Purelib.Topology.Surface.Sewing (NormalFormCycles)
open Purelib.Riemann.Readings.PrimitiveAreaBounds (AreaCoordinate)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.LinearAlgebra.Alternating.Handle.Basic (PivotIndices)
open _root_.Purelib.LinearAlgebra.Alternating (NormalForm)

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}
  {word : BoundaryWord.CutBoundaryWord labels edges} {pairing : Cut.IntegralPairing.CutBoundaryWord word}
  {primitive : Fin source → Stokes.PrimitivePoint}
  {values : Data.Vector Stokes.PrimitivePoint word.alphabet.count}
  {routes : Sewing.ChordCycleBank word} {raw : List (Handle.Basic.PivotIndices word.alphabet.count)}
  {normal : LinearAlgebra.Alternating.NormalForm pairing.paired raw} {bank : ChordCycleBank.Sample routes pairing
    primitive
    values}

/-- A retained row coefficient mass bounds both components of its transformed chord error. -/
theorem errors_bounded (sample : Sewing.NormalFormCycles normal bank) (profile :
  WeightedRowBudgets.CoefficientRows normal.reduction.cycleRows)
    {bound : PrimitiveAreaBounds.AreaCoordinate} (bounded : ∀ index, (PrimitivePoint.Bounded (bank.errors index)) bound)
      (row : Fin word.alphabet.count) :
    (PrimitivePoint.Bounded (sample.errors row)) ((profile.coefficients.get row).mass * bound) := by
  rw [sample.errors_eq, sample.weights_eq]
  exact Coefficients.point_bounded (profile.coefficients.get row) bank.errors bounded

/-- Paid component accuracy gives strict bounds on both components of each transformed error row. -/
theorem errors_accurate (sample : Sewing.NormalFormCycles normal bank) (profile :
  WeightedRowBudgets.CoefficientRows normal.reduction.cycleRows)
    {target : PrimitiveAreaBounds.AreaCoordinate} (positive : 0 < target)
    (bounded : ∀ index, (PrimitivePoint.Bounded (bank.errors index)) (profile.perComponent target)) (row : Fin
      word.alphabet.count) :
    Data.Gaussian.Norm.Basic.normSq (sample.errors row).left < target ∧ Data.Gaussian.Norm.Basic.normSq (sample.errors
      row).right < target := by
  rw [sample.errors_eq, sample.weights_eq]
  exact CoefficientRows.point_accurate profile bank.errors positive bounded row

section
open Purelib.Topology.Surface.Boundary
/-- The first handle increment approximates its transformed coordinate with the physical correction retained. -/
theorem first_accurate (sample : Sewing.NormalFormCycles normal bank) (evaluated :
  NormalFormArea normal values)
    (profile : WeightedRowBudgets.CoefficientRows normal.reduction.cycleRows) {target :
      PrimitiveAreaBounds.AreaCoordinate} (positive : 0 < target)
    (bounded : ∀ index, (PrimitivePoint.Bounded (bank.errors index)) (profile.perComponent target))
    (pair : Handle.Basic.PivotIndices word.alphabet.count) (member : pair ∈ raw) :
    let difference := (PrimitivePoint.sub ((sample.handleFirst pair).increment primitive))
      ((PrimitivePoint.sub (evaluated.points pair.1)) (sample.physical pair.2))
    Data.Gaussian.Norm.Basic.normSq difference.left < target ∧ Data.Gaussian.Norm.Basic.normSq difference.right <
      target := by
  have equal : (PrimitivePoint.sub ((sample.handleFirst pair).increment primitive))
      ((PrimitivePoint.sub (evaluated.points pair.1)) (sample.physical pair.2)) = (PrimitivePoint.sub
        PrimitivePoint.zero) (sample.errors pair.2) := by
    rw [sample.handleFirst_increment evaluated pair member]
    simp only [PrimitivePoint.sub, PrimitivePoint.add, PrimitivePoint.zero]
    congr 1 <;> ring1
  dsimp only
  rw [equal]
  simpa only [PrimitivePoint.sub, PrimitivePoint.zero, zero_sub, Gaussian.Norm.Basic.normSq_neg]
    using errors_accurate sample profile positive bounded pair.2

/-- The last handle increment approximates its transformed coordinate with the physical correction retained. -/
theorem last_accurate (sample : Sewing.NormalFormCycles normal bank) (evaluated :
  NormalFormArea normal values)
    (profile : WeightedRowBudgets.CoefficientRows normal.reduction.cycleRows) {target :
      PrimitiveAreaBounds.AreaCoordinate} (positive : 0 < target)
    (bounded : ∀ index, (PrimitivePoint.Bounded (bank.errors index)) (profile.perComponent target))
    (pair : Handle.Basic.PivotIndices word.alphabet.count) (member : pair ∈ raw) :
    let difference := (PrimitivePoint.sub ((sample.handleLast pair).increment primitive))
      ((evaluated.points pair.2).add (sample.physical pair.1))
    Data.Gaussian.Norm.Basic.normSq difference.left < target ∧ Data.Gaussian.Norm.Basic.normSq difference.right <
      target := by
  have equal : (PrimitivePoint.sub ((sample.handleLast pair).increment primitive))
      ((evaluated.points pair.2).add (sample.physical pair.1)) = sample.errors pair.1 := by
    rw [sample.handleLast_increment evaluated pair member]
    simp only [PrimitivePoint.sub, PrimitivePoint.add]
    congr 1 <;> ring1
  dsimp only
  rw [equal]
  exact errors_accurate sample profile positive bounded pair.1

end

/-- Transfer a sampled second row, with its forced negative orientation, to the first handle coordinate.
Physical-boundary terms are not discarded. -/
theorem first_sample_bounded (sample : Sewing.NormalFormCycles normal bank) (evaluated :
  NormalFormArea normal values)
    (rows : Fin word.alphabet.count → Gaussian.Basic.Canonical)
    {jumpBound errorBound : Fin word.alphabet.count → PrimitiveAreaBounds.AreaCoordinate}
    (jumps : ∀ row, Data.Gaussian.Norm.Basic.normSq ((sample.jumps row).right - rows row) ≤ jumpBound row)
    (errors : ∀ row, Data.Gaussian.Norm.Basic.normSq (sample.errors row).right ≤ errorBound row)
    (pair : Handle.Basic.PivotIndices word.alphabet.count) (member : pair ∈ raw) :
    Data.Gaussian.Norm.Basic.normSq (-rows pair.2 - ((evaluated.points pair.1).right - (sample.physical pair.2).right))
      ≤
      2 * (jumpBound pair.2 + errorBound pair.2) := by
  have model : (PrimitivePoint.sub (evaluated.points pair.1)) (sample.physical pair.2) =
      ((sample.handleFirst pair).increment primitive).add (sample.errors pair.2) := by
    rw [sample.handleFirst_increment evaluated pair member]
    simp only [PrimitivePoint.sub, PrimitivePoint.add]
    congr 1 <;> ring1
  have scalar := congrArg PrimitivePoint.right model
  rw [NormalFormCycles.handleFirst, CutCycleChain.increment_negate, sample.increment_eq] at scalar
  simp only [PrimitivePoint.sub, PrimitivePoint.add, PrimitivePoint.zero, zero_sub] at scalar
  rw [scalar]
  have equal : -rows pair.2 - (-(sample.jumps pair.2).right + (sample.errors pair.2).right) =
      ((sample.jumps pair.2).right - rows pair.2) - (sample.errors pair.2).right := by ring1
  rw [equal]
  exact (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (jumps pair.2) (errors pair.2)) (by decide))

/-- The first row has positive orientation in the last handle coordinate. -/
theorem last_sample_bounded (sample : Sewing.NormalFormCycles normal bank) (evaluated :
  NormalFormArea normal values)
    (rows : Fin word.alphabet.count → Gaussian.Basic.Canonical)
    {jumpBound errorBound : Fin word.alphabet.count → PrimitiveAreaBounds.AreaCoordinate}
    (jumps : ∀ row, Data.Gaussian.Norm.Basic.normSq ((sample.jumps row).right - rows row) ≤ jumpBound row)
    (errors : ∀ row, Data.Gaussian.Norm.Basic.normSq (sample.errors row).right ≤ errorBound row)
    (pair : Handle.Basic.PivotIndices word.alphabet.count) (member : pair ∈ raw) :
    Data.Gaussian.Norm.Basic.normSq (rows pair.1 - ((evaluated.points pair.2).right + (sample.physical pair.1).right)) ≤
      2 * (jumpBound pair.1 + errorBound pair.1) := by
  have model : (evaluated.points pair.2).add (sample.physical pair.1) =
      (PrimitivePoint.sub ((sample.handleLast pair).increment primitive)) (sample.errors pair.1) := by
    rw [sample.handleLast_increment evaluated pair member]
    simp only [PrimitivePoint.sub, PrimitivePoint.add]
    congr 1 <;> ring1
  have scalar := congrArg PrimitivePoint.right model
  rw [NormalFormCycles.handleLast, sample.increment_eq] at scalar
  simp only [PrimitivePoint.sub, PrimitivePoint.add] at scalar
  rw [scalar]
  have equal : rows pair.1 - ((sample.jumps pair.1).right - (sample.errors pair.1).right) =
      (sample.errors pair.1).right - ((sample.jumps pair.1).right - rows pair.1) := by ring1
  rw [equal]
  exact (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (by simpa only [add_comm] using add_le_add (errors pair.1) (jumps pair.1)) (by decide))

end Purelib.Topology.Surface.Boundary.NormalFormErrorBounds
