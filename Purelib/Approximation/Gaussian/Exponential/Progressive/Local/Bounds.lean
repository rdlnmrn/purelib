module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Budget
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Sample
public import Purelib.Approximation.Gaussian.Sequence.UnitDisk
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Gaussian.Exponential.Horner

open Purelib.Approximation.Gaussian.Exponential.Progressive.Local

open Purelib.Approximation.Gaussian.Sequence

open Purelib.Approximation.Rational

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Progressive finite exponential

This is the local core of exponential as a CCL-to-CCL computation.  The input
is an existing arithmetic CCL name together with a finite domain certificate
for its candidates.  At natural index `n`, the output evaluates the depth-`n`
Horner program at the input's depth-`n` displayed rational witness, packages
those samples as a progressive enclosure process, and starts the unchanged
productive raw CCL controller on that process.  Thus neither side names a
completed point, while every requested finite output prefix is genuinely a
CCL prefix for the calculated exponential enclosure.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Bounds

/-- Input movement at one fixed finite Horner depth. -/
theorem sampleFrom_input_effect (source :
  UnitDisk.UnitDiskSamples)
    {oldIndex newIndex : Nat} (indexOrder : oldIndex ≤ newIndex) :
    Data.Gaussian.Norm.Basic.normSq
        (Horner.Sample.sample (source.value newIndex) oldIndex -
          Horner.Sample.sample (source.value oldIndex) oldIndex) ≤
      Budget.inputErrorScale * (1 / 4 : Fraction.Rational) ^ oldIndex := by
  have sensitivity := Horner.Sample.sample_input_close
    (source.value newIndex) (source.value oldIndex)
    (source.unit newIndex) (source.unit oldIndex) oldIndex
  have movement := source.close indexOrder
  calc
    Data.Gaussian.Norm.Basic.normSq
        (Horner.Sample.sample (source.value newIndex) oldIndex -
          Horner.Sample.sample (source.value oldIndex) oldIndex) ≤
        16 * Data.Gaussian.Norm.Basic.normSq (source.value newIndex - source.value oldIndex) := sensitivity
    _ ≤ 16 * Geometric.Basic.quarterRadius 4 oldIndex :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct movement
        (by decide)
    _ = Budget.inputErrorScale * (1 / 4 : Fraction.Rational) ^ oldIndex := by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow,
        Budget.inputErrorScale]
      ring1

/-- Quantitative core for simultaneous input and Horner-depth refinement. -/
theorem sampleFrom_later_close (source :
  UnitDisk.UnitDiskSamples)
    {oldIndex newIndex : Nat} (indexOrder : oldIndex ≤ newIndex) :
    Data.Gaussian.Norm.Basic.normSq (Sample.sampleFrom source.value newIndex -
      Sample.sampleFrom source.value oldIndex) ≤
      Geometric.Basic.quarterRadius Budget.errorScale oldIndex := by
  have truncation := Horner.Sample.sample_later_close
    (source.value newIndex) (source.unit newIndex) indexOrder
  have inputEffect := sampleFrom_input_effect source
    indexOrder
  calc
    Data.Gaussian.Norm.Basic.normSq (Sample.sampleFrom source.value newIndex -
        Sample.sampleFrom source.value oldIndex) ≤
        2 * (Data.Gaussian.Norm.Basic.normSq
          (Horner.Sample.sample (source.value newIndex) newIndex -
            Horner.Sample.sample (source.value newIndex) oldIndex) +
          Data.Gaussian.Norm.Basic.normSq
          (Horner.Sample.sample (source.value newIndex) oldIndex -
            Horner.Sample.sample (source.value oldIndex) oldIndex)) :=
      Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
    _ ≤ 2 * (Geometric.Basic.quarterRadius 10 oldIndex +
        Budget.inputErrorScale * (1 / 4 : Fraction.Rational) ^ oldIndex) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add truncation inputEffect) (by decide)
    _ = Geometric.Basic.quarterRadius Budget.errorScale oldIndex := by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow,
        Geometric.Basic.quarterRadius_eq_mul_pow, Budget.errorScale]
      ring1
end Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Bounds

end
