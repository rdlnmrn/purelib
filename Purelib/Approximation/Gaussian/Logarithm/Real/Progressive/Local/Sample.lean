module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Logarithm.Rational.Sample
import Purelib.Approximation.Gaussian.Logarithm.Rational.Sensitivity
public import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Sequence
public import Purelib.Approximation.Rat.Logarithm.Horner.Sensitivity
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.Rational

open Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local

open Purelib.Approximation.Rat.Logarithm.Horner

open Purelib.Approximation.Rational

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Local logarithm as a CCL computation

This is the local core of logarithm as a CCL-to-CCL computation.  The input is
an arithmetic CCL name carrying an explicit overlapping chart certificate.
Every candidate is a displayed real Gaussian rational whose coordinate lies
in `[1/2,2]`.  The output synchronizes later finite input witnesses with later
finite Horner depths, packages the result as an accuracy sidechannel, and
starts the unchanged productive CCL controller on it.  It does not assert a
completed positive real input or a completed logarithm.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Sample

/-- Evaluate the real logarithm sample at the retained chart sample and matching finite depth. -/
def sampleFrom (source :
  Sequence.ChartSamples) (index : Nat) : Data.Gaussian.Basic.Canonical :=
  Sample.sample (source.value index) index

/-- Input movement contribution at one fixed finite logarithm depth. -/
theorem sampleFrom_input_effect (source :
  Sequence.ChartSamples)
    {oldIndex newIndex : Nat} (indexOrder : oldIndex ≤ newIndex) :
    Data.Gaussian.Norm.Basic.normSq
        (Sample.sample (source.value newIndex) oldIndex -
          Sample.sample (source.value oldIndex) oldIndex) ≤
      (Sensitivity.sampleInputScale * 4) *
        (1 / 4 : Fraction.Rational) ^ oldIndex := by
  have sensitivity := Sensitivity.sample_input_close
    (source.half newIndex) (source.two newIndex)
    (source.half oldIndex) (source.two oldIndex) oldIndex
  have movement := source.close indexOrder
  calc
    Data.Gaussian.Norm.Basic.normSq
        (Sample.sample (source.value newIndex) oldIndex -
          Sample.sample (source.value oldIndex) oldIndex) ≤
        Sensitivity.sampleInputScale *
          (source.value newIndex - source.value oldIndex) ^ 2 := sensitivity
    _ ≤ Sensitivity.sampleInputScale *
        Geometric.Basic.quarterRadius 4 oldIndex :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct movement
        (by
          rw [Sensitivity.sampleInputScale]
          exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (add_nonneg (by decide) (by decide)))
    _ = (Sensitivity.sampleInputScale * 4) *
        (1 / 4 : Fraction.Rational) ^ oldIndex := by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1

/-- The real-logarithm input sensitivity scale multiplied by the canonical scale-four input movement allowance. -/
def inputEffectScale : Fraction.Rational
  :=
  Sensitivity.sampleInputScale * 4

/-- The combined real-logarithm error scale, twice the sum of unit truncation scale and retained input-effect scale. -/
def errorScale : Fraction.Rational := 2 *
  (1 + inputEffectScale)

/-- The combined real-logarithm error scale is nonnegative. -/
theorem errorScale_nonneg : 0 ≤
  errorScale := by
  rw [errorScale,
    inputEffectScale,
    Sensitivity.sampleInputScale]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (by decide)
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg (by decide) (by decide))) (by decide)))

/-- Combined finite input and truncation movement. -/
theorem sampleFrom_later_close (source :
  Sequence.ChartSamples)
    {oldIndex newIndex : Nat} (indexOrder : oldIndex ≤ newIndex) :
    Data.Gaussian.Norm.Basic.normSq (sampleFrom
      source newIndex - sampleFrom source oldIndex) ≤
      Geometric.Basic.quarterRadius errorScale oldIndex
        := by
  have truncation := Sample.sample_later_close
    (source.half newIndex) (source.two newIndex) indexOrder
  have inputEffect := sampleFrom_input_effect source
    indexOrder
  calc
    Data.Gaussian.Norm.Basic.normSq (sampleFrom
      source newIndex - sampleFrom source oldIndex) ≤
        2 * (Data.Gaussian.Norm.Basic.normSq
          (Sample.sample (source.value newIndex) newIndex -
            Sample.sample (source.value newIndex) oldIndex) +
          Data.Gaussian.Norm.Basic.normSq
          (Sample.sample (source.value newIndex) oldIndex -
            Sample.sample (source.value oldIndex) oldIndex)) :=
      Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
    _ ≤ 2 * (Geometric.Basic.quarterRadius 1 oldIndex +
        inputEffectScale * (1 / 4 : Fraction.Rational) ^
          oldIndex) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add truncation (by
          simpa only [inputEffectScale] using
            inputEffect)) (by decide)
    _ = Geometric.Basic.quarterRadius errorScale oldIndex
      := by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow,
        Geometric.Basic.quarterRadius_eq_mul_pow,
          errorScale]
      ring1
end Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Sample

end
