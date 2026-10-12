module
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.LinearAlgebra.Matrix.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Riemann.Integration.ScalarTailLower
import Init.Core
import Init.Data.Nat.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Approximation.Matrix
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Rational

open Purelib.Data.Rat

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods

@[expose] public section

/-! Regression: the canonical scalar may vanish in a discarded prefix of a coherent named matrix.
The executed finite request starts with scalar zero, selects anchor 17, and reads scalar 1/256
with scalar-norm floor 1/65536 and positive clearance 1/262144. -/
namespace Test.LinearAlgebra.Matrix.Approximation.ScalarTailLower

open Purelib.Riemann.Integration.ScalarTailLower
open Purelib.Riemann.Periods.PeriodMatrix
open Purelib.LinearAlgebra.Gaussian.QuadraticForm
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_zero)
open Purelib.LinearAlgebra.Matrix (matrixOfFn matrixOfFn_apply)

/-- The exact nonzero Gaussian scalar one quarter. -/
def value : Gaussian := ⟨1 / 4, 0⟩

/-- A geometrically coherent approximation with an initial zero sample and constant nonzero tail.

The retained initial error allowance pays the jump to one quarter, and all later samples agree exactly. -/
def source : PeriodMatrix.GeometricApproximation where
  sample := fun index => if index = 0 then 0 else value
  errorScale := 1 / 2
  errorScale_nonneg := by decide
  later_close := by
    intro earlier later order
    cases earlier with
    | zero =>
        cases later with
        | zero => decide
        | succ later =>
          change Data.Gaussian.Norm.Basic.normSq (value - 0) ≤ (1 / 2 :
            PeriodMatrix.Coordinate); decide
    | succ earlier =>
        have laterNonzero : later ≠ 0 := Nat.ne_of_gt ((Nat.zero_lt_succ earlier).trans_le order)
        have earlierNonzero : earlier + 1 ≠ 0 := by
          intro impossible
          cases impossible
        rewrite [if_neg earlierNonzero, if_neg laterNonzero,
          Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
        exact Geometric.Basic.quarterRadius_nonneg (by decide) _
  centerBound := 1
  centerBound_nonneg := by decide
  sample_bounded := by
    intro index
    cases index with
    | zero => decide
    | succ index =>
      change Data.Gaussian.Norm.Basic.normSq value ≤ (1 : PeriodMatrix.Coordinate); decide

/-- The one-entry coherent named matrix built from the original delayed nonzero source. -/
def matrix : PeriodMatrix.NamedMatrix 1 := LinearAlgebra.Matrix.matrixOfFn fun _ _ =>
  PeriodMatrix.geometricNamed source

/-- The original source-state index selected by canonical finite refinement at the requested matrix stage. -/
def sourceIndex (stage : Nat) : Nat :=
  Gaussian.Process.Sampling.stateAt ScalarTailLower.source.toApproximation.toProcess (0 : Nat) stage

/-- The initial matrix stage retains original source index zero. -/
theorem sourceIndex_zero : sourceIndex 0 = 0 := by decide

/-- Every positive matrix stage has advanced to a strictly positive original source index. -/
theorem sourceIndex_succ_positive : ∀ stage, 0 < sourceIndex (stage + 1)
  | 0 => by decide
  | stage + 1 =>
      (sourceIndex_succ_positive stage).trans_le
        (ScalarTailLower.source.toApproximation.refineIndex_ge (sourceIndex (stage + 1))
          (Gaussian.Process.Sampling.refinementTarget (stage + 1 + 1))
          (Gaussian.Process.Sampling.refinementTarget_pos (stage + 1 + 1)))

/-- The sampled matrix entry is zero precisely at retained source index zero and otherwise reads the fixed nonzero
value. -/
theorem matrix_sample (stage : Nat) : PeriodMatrix.sampledMatrix matrix stage 0 0 = if
  sourceIndex stage = 0 then 0 else value := by
  rw [PeriodMatrix.sampledMatrix_apply]
  rfl

/-- The initial named-matrix entry is exactly zero. -/
theorem matrix_sample_zero : PeriodMatrix.sampledMatrix matrix 0 0 0 = 0 := by
  rw [matrix_sample, sourceIndex_zero, if_pos rfl]

/-- Every positive-stage named-matrix entry is exactly one quarter. -/
theorem matrix_sample_succ (stage : Nat) : PeriodMatrix.sampledMatrix matrix (stage + 1) 0 0 = value :=
  by
  rw [matrix_sample, if_neg (Nat.ne_of_gt (sourceIndex_succ_positive stage))]

/-- The canonical scaled inverse scalar is zero at the discarded initial stage. -/
theorem scalar_zero : (PeriodMatrix.canonicalScaledInverse matrix).scalar.sample 0 = 0 := by
  apply Data.Gaussian.Norm.Basic.normSq_eq_zero.mp
  rw [PeriodMatrix.normSq_canonicalScaledInverse_one_scalar_sample]
  change Data.Gaussian.Norm.Basic.normSq (PeriodMatrix.sampledMatrix matrix 0 0 0) ^ 4 = 0
  rw [matrix_sample_zero, Data.Gaussian.Norm.Basic.normSq_zero]
  decide

/-- The fixed positive squared-norm floor of the canonical scaled inverse scalar on the retained tail. -/
def scalarFloor : Fraction.Rational := Data.Gaussian.Norm.Basic.normSq value ^ 4

/-- Every positive-stage scaled inverse scalar has exactly the retained squared-norm floor. -/
theorem scalar_norm_succ (stage : Nat) : Data.Gaussian.Norm.Basic.normSq ((PeriodMatrix.canonicalScaledInverse
  matrix).scalar.sample (stage + 1)) = scalarFloor := by
  rw [PeriodMatrix.normSq_canonicalScaledInverse_one_scalar_sample]
  change Data.Gaussian.Norm.Basic.normSq (PeriodMatrix.sampledMatrix matrix (stage + 1) 0 0) ^
    4 = _
  rw [matrix_sample_succ]
  rfl

/-- The scalar lower-bound certificate beginning at stage one with its original positive squared-norm floor. -/
def tailLower : ScalarTailLower.ScalarTailLowerCertificate matrix where
  threshold := 1
  lowerSq := scalarFloor
  positive := Fraction.Order.Arithmetic.pow_pos_direct
    (Data.Gaussian.Norm.Basic.normSq_pos (by decide : value ≠ 0)) 4
  sample_lower := by
    intro stage later
    cases stage with
    | zero => exact (Nat.not_succ_le_zero 0 later).elim
    | succ stage =>
        rewrite [scalar_norm_succ]
        exact Fraction.Order.Basic.le_refl scalarFloor

/-- The tail-separation certificate selected from the original scalar lower bound. -/
def separated : PeriodMatrix.ScalarTailSeparationCertificate matrix :=
  ScalarTailLower.tailLower.toScalarTailSeparationCertificate

/-- The retained tail anchor lies strictly beyond the initial zero scalar sample. -/
theorem discarded_zero_before_anchor : 0 < separated.anchor := by
  have threshold : 1 ≤ tailLower.tailAnchor := ScalarTailLower.tailLower.threshold_le_tailAnchor
  change 1 ≤ ScalarTailLower.separated.anchor
  rw [show ScalarTailLower.separated.anchor = ScalarTailLower.tailLower.tailAnchor from rfl]
  exact threshold

/-- The selected original tail anchor has strictly positive scalar clearance. -/
theorem positive_clearance : 0 < PeriodMatrix.scalarTailClearanceAt matrix separated.anchor :=
  ScalarTailLower.separated.tailPositive

/-- Every scalar sample at or beyond the retained original anchor is nonzero. -/
theorem retained_scalar_nonzero (stage : Nat) (later : ScalarTailLower.separated.anchor ≤ stage) :
    (PeriodMatrix.canonicalScaledInverse matrix).scalar.sample stage ≠ 0 :=
      ScalarTailLower.separated.sample_nonzero_of_anchor_le stage later

end Test.LinearAlgebra.Matrix.Approximation.ScalarTailLower
