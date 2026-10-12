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

variable {polynomial : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {request :
  Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Request}
  {prepared : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Prepared polynomial request} {segment :
    Purelib.Integration.Algebraic.SquareFactor.PathInput.Segment}
  {data : Purelib.Integration.Algebraic.SquareFactor.PathInput.Data prepared segment}

section
open Purelib.Integration.Algebraic.SquareFactor
/-- Iterate exact retained layer refinements from the supplied original initial layer. -/
@[expose] def layerFrom {safe : data.Safe} (start : IntegrationLayers.Layer safe 0) : (index : Nat) →
  IntegrationLayers.Layer safe index
  | 0 => start
  | index + 1 => (IntegrationLayers.Next.make (Purelib.Integration.Algebraic.SquareFactor.IntegrationProgram.layerFrom
    start index)).layer

/-- Read the retained refinement layer starting from the original safe path and selected sheet. -/
@[expose] def layerAt (safe : data.Safe) (sheet : Fin 2) : (index : Nat) → IntegrationLayers.Layer safe index :=
  IntegrationProgram.layerFrom (IntegrationLayers.initial safe sheet)

end

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian in
/-- Construct the consecutive certified refinement program from one retained initial layer.

The original segment direction sets the comparison scale, and each stage uses the exact successor refinement of its
retained layer. -/
@[expose] def sequential (safe : data.Safe) (sheet : Fin 2) :
    Sequential.SequentialCompatibleConstantRefinementProgram :=
  let start := IntegrationLayers.initial safe sheet
  { model index := (IntegrationProgram.layerFrom start index).model
    steps index := (IntegrationLayers.Next.make (IntegrationProgram.layerFrom start index)).refinement
    stepScale := 4 * Data.Gaussian.Norm.Basic.normSq segment.direction
    stepScale_nonneg := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Norm.Basic.normSq_nonneg
      segment.direction)
    initialAllowance_le := by
      have bound := start.modelAllowance_le
      have scaled : Data.Gaussian.Norm.Basic.normSq segment.direction ≤ 16 * Data.Gaussian.Norm.Basic.normSq
        segment.direction :=
        by
        have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (show (1 : IntegrationProgram.Coordinate) ≤ 16 by decide) (Norm.Basic.normSq_nonneg segment.direction)
        simpa only [Fraction.Field.one_mul] using scaled
      calc
        _ ≤ Data.Gaussian.Norm.Basic.normSq segment.direction := by
          simpa only [IntegrationProgram.layerFrom, Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
            Fraction.Field.mul_one_direct] using bound
        _ ≤ 16 * Data.Gaussian.Norm.Basic.normSq segment.direction := scaled
        _ = 4 * (4 * Data.Gaussian.Norm.Basic.normSq segment.direction) := by ring1
    comparisonAllowance_le index := (IntegrationLayers.Next.make (IntegrationProgram.layerFrom start
      index)).comparisonAllowance_le_quarter }

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian in
/-- Read the certified geometric refinement program for the original safe path and selected sheet. -/
@[expose] def program (safe : data.Safe) (sheet : Fin 2) : Basic.RefinementProgram :=
  (IntegrationProgram.sequential safe sheet).toRefinementProgram

open Purelib.Integration.Algebraic.SquareFactor in
/-- The program's exact stage model equals the retained layer model at the same index. -/
theorem model_eq (safe : data.Safe) (sheet : Fin 2) (index : Nat) :
    (IntegrationProgram.program safe sheet).model index = (IntegrationProgram.layerAt safe sheet index).model := rfl

open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The original program error scale is sixteen times the segment direction's squared norm. -/
theorem errorScale_eq (safe : data.Safe) (sheet : Fin 2) :
    (IntegrationProgram.program safe sheet).errorScale = 16 * Data.Gaussian.Norm.Basic.normSq segment.direction := by
  change 4 * (4 * Data.Gaussian.Norm.Basic.normSq segment.direction) = _
  ring1

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Later retained layer samples meet the earlier quarter radius with the exact original direction-based scale. -/
theorem later_close (safe : data.Safe) (sheet : Fin 2) {earlier later : Nat} (order : earlier ≤ later) :
    Data.Gaussian.Norm.Basic.normSq ((IntegrationProgram.layerAt safe sheet later).model.integralSample -
      (IntegrationProgram.layerAt safe sheet earlier).model.integralSample) ≤
      Geometric.Basic.quarterRadius (16 * Data.Gaussian.Norm.Basic.normSq segment.direction) earlier := by
  have bound := (IntegrationProgram.program safe sheet).later_close order
  rw [IntegrationProgram.errorScale_eq, IntegrationProgram.model_eq, IntegrationProgram.model_eq] at bound
  rw [Norm.Basic.normSq_eq_canonical]
  exact bound

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian in
/-- Read the certified cached program for the original safe path and selected sheet. -/
@[expose] def cached (safe : data.Safe) (sheet : Fin 2) : Cached.Basic.CachedProgram :=
  (IntegrationProgram.program safe sheet).certifiedView.program

open Purelib.Integration.Algebraic.SquareFactor
/-- The cached stage model equals the exact retained layer model. -/
theorem cached_model (safe : data.Safe) (sheet : Fin 2) (index : Nat) :
    ((IntegrationProgram.cached safe sheet).stage index).model = (IntegrationProgram.layerAt safe sheet index).model :=
      rfl

/-- The cached stage sample equals the exact retained layer model's integral sample. -/
theorem cached_sample (safe : data.Safe) (sheet : Fin 2) (index : Nat) :
    ((IntegrationProgram.cached safe sheet).stage index).sample = (IntegrationProgram.layerAt safe sheet
      index).model.integralSample := rfl

/-- The cached stage selected for a positive target has allowance strictly below that original target. -/
theorem requested_allowance (safe : data.Safe) (sheet : Fin 2) (current : Nat)
    (target : IntegrationProgram.Coordinate) (positive : 0 < target) :
    ((IntegrationProgram.cached safe sheet).stage
      ((IntegrationProgram.cached safe sheet).approximation.refineIndex current target positive)).allowance < target :=
  (IntegrationProgram.cached safe sheet).requested_allowance current target positive

end Purelib.Integration.Algebraic.SquareFactor.IntegrationProgram
