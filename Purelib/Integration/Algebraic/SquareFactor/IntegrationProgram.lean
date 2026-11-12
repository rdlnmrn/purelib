module
import Purelib.Data.Gaussian.Basic
public import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Program.Gaussian.Basic
public import Purelib.Integration.Program.Gaussian.Sequential

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Algebraic.SquareFactor.PathInput
public import Purelib.Integration.Algebraic.SquareFactor.IntegrationLayers
import Purelib.CCL.Progressive.IntegrationPrograms
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Tactic.Ring

public section

/-!
# Generated coherent integration of square-factor differentials

The finite layer recursion derives an ordinary Gaussian refinement program
on its actual integration cells.  Coherence, model allowances and the sample
bound are conclusions of the construction, not caller-supplied fields.
Only the initial root sheet is selected independently.  Every later cell
inherits a parent's point-query occurrence on the same retained segment.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.IntegrationProgram

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput
open Purelib.Integration.Algebraic.SquareFactor.IntegrationLayers
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Rat in
/-- The rational carrier for retained integration-program requests. -/
abbrev Coordinate := Fraction.Rational

variable {polynomial : GaussianPolynomial} {request :
  Request}
  {prepared : Prepared polynomial request} {segment :
    Segment}
  {data : Data prepared segment}

section
open Purelib.Integration.Algebraic.SquareFactor
/-- Iterate exact retained layer refinements from the supplied original initial layer. -/
@[expose] def layerFrom {safe : data.Safe} (start : Layer safe 0) : (index : Nat) →
  Layer safe index
  | 0 => start
  | index + 1 => (Next.make (IntegrationProgram.layerFrom
    start index)).layer

/-- Read the retained refinement layer starting from the original safe path and selected sheet. -/
@[expose] def layerAt (safe : data.Safe) (sheet : Fin 2) : (index : Nat) → Layer safe index :=
  layerFrom (IntegrationLayers.initial safe sheet)

end

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian in
/-- Construct the consecutive certified refinement program from one retained initial layer.

The original segment direction sets the comparison scale, and each stage uses the exact successor refinement of its
retained layer. -/
@[expose] def sequentialFrom {safe : data.Safe} (start : Layer safe 0) :
    Sequential.SequentialCompatibleConstantRefinementProgram :=
  { model index := (layerFrom start index).model
    steps index := (Next.make (layerFrom start index)).refinement
    stepScale := 4 * Norm.Basic.normSq segment.direction
    stepScale_nonneg := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Norm.Basic.normSq_nonneg
      segment.direction)
    initialAllowance_le := by
      have bound := start.modelAllowance_le
      have scaled : Norm.Basic.normSq segment.direction ≤ 16 * Norm.Basic.normSq
        segment.direction :=
        by
        have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (show (1 : Coordinate) ≤ 16 by decide) (Norm.Basic.normSq_nonneg segment.direction)
        simpa only [Fraction.Field.one_mul] using scaled
      calc
        _ ≤ Norm.Basic.normSq segment.direction := by
          simpa only [layerFrom, Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
            Fraction.Field.mul_one_direct] using bound
        _ ≤ 16 * Norm.Basic.normSq segment.direction := scaled
        _ = 4 * (4 * Norm.Basic.normSq segment.direction) := by ring1
    comparisonAllowance_le index := (Next.make (layerFrom start
      index)).comparisonAllowance_le_quarter }

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian in
/-- Construct the original consecutive refinement program, retaining the selected sheet's initial layer once. -/
@[expose] def sequential (safe : data.Safe) (sheet : Fin 2) :
    Sequential.SequentialCompatibleConstantRefinementProgram :=
  sequentialFrom (IntegrationLayers.initial safe sheet)

open Purelib.Integration.Algebraic.SquareFactor in
/-- A retained original initial layer identifies the complete original consecutive refinement program. -/
theorem sequentialFrom_eq_sequential (safe : data.Safe) (sheet : Fin 2) (start : Layer safe 0)
    (same : start = IntegrationLayers.initial safe sheet) : sequentialFrom start = sequential safe sheet := by
  cases same
  rfl

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian in
/-- Read the certified geometric refinement program from the supplied retained initial layer and its original data. -/
@[expose] def programFrom {safe : data.Safe} (start : Layer safe 0) : Basic.RefinementProgram :=
  (sequentialFrom start).toRefinementProgram

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian in
/-- Read the certified geometric refinement program for the original safe path and selected sheet. -/
@[expose] def program (safe : data.Safe) (sheet : Fin 2) : Basic.RefinementProgram :=
  (sequential safe sheet).toRefinementProgram

open Purelib.Integration.Algebraic.SquareFactor in
/-- The same retained original initial layer preserves the complete original geometric refinement program. -/
theorem programFrom_eq_program (safe : data.Safe) (sheet : Fin 2) (start : Layer safe 0)
    (same : start = IntegrationLayers.initial safe sheet) : programFrom start = program safe sheet := by
  cases same
  rfl

open Purelib.Integration.Algebraic.SquareFactor in
/-- The program's exact stage model equals the retained layer model at the same index. -/
theorem model_eq (safe : data.Safe) (sheet : Fin 2) (index : Nat) :
    (program safe sheet).model index = (layerAt safe sheet index).model := rfl

open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The original program error scale is sixteen times the segment direction's squared norm. -/
theorem errorScale_eq (safe : data.Safe) (sheet : Fin 2) :
    (program safe sheet).errorScale = 16 * Norm.Basic.normSq segment.direction := by
  change 4 * (4 * Norm.Basic.normSq segment.direction) = _
  ring1

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Later retained layer samples meet the earlier quarter radius with the exact original direction-based scale. -/
theorem later_close (safe : data.Safe) (sheet : Fin 2) {earlier later : Nat} (order : earlier ≤ later) :
    Norm.Basic.normSq ((layerAt safe sheet later).model.integralSample -
      (layerAt safe sheet earlier).model.integralSample) ≤
      Geometric.Basic.quarterRadius (16 * Norm.Basic.normSq segment.direction) earlier := by
  have bound := (program safe sheet).later_close order
  rw [errorScale_eq, model_eq, model_eq] at bound
  rw [Norm.Basic.normSq_eq_canonical]
  exact bound

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian in
/-- Read the certified cached program for the original safe path and selected sheet. -/
@[expose] def cached (safe : data.Safe) (sheet : Fin 2) : Cached.Basic.CachedProgram :=
  (program safe sheet).certifiedView.program

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian in
/-- Retain the supplied original initial layer when constructing the exact certified cached model source. -/
@[expose] def cachedFrom {safe : data.Safe} (start : Layer safe 0) : Cached.Basic.CachedProgram :=
  (programFrom start).certifiedView.program

open Purelib.Integration.Algebraic.SquareFactor in
/-- The original initial-layer identity preserves the whole original cached source and all retained callbacks. -/
theorem cachedFrom_eq_cached (safe : data.Safe) (sheet : Fin 2) (start : Layer safe 0)
    (same : start = IntegrationLayers.initial safe sheet) : cachedFrom start = cached safe sheet := by
  cases same
  rfl

open Purelib.Integration in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian in
/-- A cached stage retains the same initial layer and computes model readbacks through the original constructor. -/
private theorem cachedFrom_stage_spec {safe : data.Safe} (start : Layer safe 0) (index : Nat) :
    ((cachedFrom start).stage index) = CertifiedProgram.CachedModel.canonical
      (operations := Cached.Basic.modelOperations) (layerFrom start index).model := rfl

open Purelib.Integration in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian in
/-- Every cached stage retains its original layer model and canonical sample/allowance caches from that same layer. -/
theorem cachedFrom_stage {safe : data.Safe} (start : Layer safe 0) (index : Nat) :
    ((cachedFrom start).stage index) = CertifiedProgram.CachedModel.canonical
      (operations := Cached.Basic.modelOperations) (layerFrom start index).model := cachedFrom_stage_spec start index

open Purelib.Integration.Algebraic.SquareFactor
/-- The cached stage model equals the exact retained layer model. -/
theorem cached_model (safe : data.Safe) (sheet : Fin 2) (index : Nat) :
    ((cached safe sheet).stage index).model = (layerAt safe sheet index).model :=
      rfl

/-- The cached stage sample equals the exact retained layer model's integral sample. -/
theorem cached_sample (safe : data.Safe) (sheet : Fin 2) (index : Nat) :
    ((cached safe sheet).stage index).sample = (layerAt safe sheet
      index).model.integralSample := rfl

/-- The cached stage selected for a positive target has allowance strictly below that original target. -/
theorem requested_allowance (safe : data.Safe) (sheet : Fin 2) (current : Nat)
    (target : Coordinate) (positive : 0 < target) :
    ((cached safe sheet).stage
      ((cached safe sheet).approximation.refineIndex current target positive)).allowance < target :=
  (cached safe sheet).requested_allowance current target positive

end Purelib.Integration.Algebraic.SquareFactor.IntegrationProgram
