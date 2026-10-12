module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Sequence
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample
public import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sensitivity
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
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local

open Purelib.Approximation.Gaussian.Logarithm.Local.Horner

open Purelib.Approximation.Rational

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Local complex logarithm as a CCL computation

The input to this module is a progressive name for the reduced argument
`z = (u - 1) / (u + 1)`, together with the finite chart certificate that every
currently possible Gaussian-rational candidate has quadrance at most `1/9`.
Finite input refinement and finite Horner depth advance together.  No
completed complex value, infinite series, or global branch is introduced.
The resulting approximation is used as the accuracy sidechannel of a
productive CCL output name; a separate explicit chart supplies the global
branch correction.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Sample

attribute [local irreducible] Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample.sample

/-- Evaluate the local logarithm Horner program at the retained disk sample and matching finite depth. -/
def sampleFrom (source :
  Sequence.DiskSamples) (index : Nat) : Data.Gaussian.Basic.Canonical :=
  Sample.sample (source.value index) index

/-- The sample input sensitivity scale multiplied by the retained scale-four input movement allowance. -/
def inputEffectScale :
  Fraction.Rational :=
  Sensitivity.sampleInputScale * 4

/-- The input movement contribution to the logarithm error scale is nonnegative. -/
theorem inputEffectScale_nonneg : 0 ≤
  inputEffectScale :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    Sensitivity.sampleInputScale_nonneg (by decide)

/-- Changing to a later input sample at the earlier fixed Horner depth stays within the retained geometric input-effect
allowance. -/
theorem sampleFrom_input_effect (source
  : Sequence.DiskSamples)
    {oldIndex newIndex : Nat} (order : oldIndex ≤ newIndex) :
    Data.Gaussian.Norm.Basic.normSq
        (Sample.sample
            (source.value newIndex) oldIndex -
          Sample.sample
            (source.value oldIndex) oldIndex) ≤
      inputEffectScale * (1 / 4 : Fraction.Rational) ^
        oldIndex := by
  have sensitivity :
      Data.Gaussian.Norm.Basic.normSq
          (Sample.sample
              (source.value newIndex) oldIndex -
            Sample.sample
              (source.value oldIndex) oldIndex) ≤
        Sensitivity.sampleInputScale *
          Data.Gaussian.Norm.Basic.normSq (source.value newIndex - source.value oldIndex) :=
    @Sensitivity.sample_input_close
      (source.value newIndex) (source.value oldIndex)
      (source.bound newIndex) (source.bound oldIndex) oldIndex
  have movement :
      Data.Gaussian.Norm.Basic.normSq (source.value newIndex - source.value oldIndex) ≤
        Geometric.Basic.quarterRadius 4 oldIndex :=
    source.close order
  calc
    Data.Gaussian.Norm.Basic.normSq
        (Sample.sample
            (source.value newIndex) oldIndex -
          Sample.sample
            (source.value oldIndex) oldIndex) ≤
        Sensitivity.sampleInputScale *
          Data.Gaussian.Norm.Basic.normSq (source.value newIndex - source.value oldIndex) := sensitivity
    _ ≤ Sensitivity.sampleInputScale *
        Geometric.Basic.quarterRadius 4 oldIndex :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct movement
        (by rw [Sensitivity.sampleInputScale]; decide)
    _ = inputEffectScale * (1 / 4 : Fraction.Rational)
      ^ oldIndex := by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow,
        inputEffectScale,
          Sensitivity.sampleInputScale]
      ring1

/-- The rational scale-five bound for finite local logarithm truncation differences. -/
def truncationScale : Fraction.Rational
  := 5

/-- The combined logarithm sample movement scale, twice the sum of truncation and input-effect scales. -/
def errorScale : Fraction.Rational := 2
  * (truncationScale +
  inputEffectScale)

/-- The combined logarithm sample movement scale is nonnegative. -/
theorem errorScale_nonneg : 0 ≤
  errorScale := by
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (by rw [truncationScale]; decide)
      inputEffectScale_nonneg)

/-- Advancing both the retained disk sample and Horner depth stays within the earlier index's combined quarter-radius
allowance. -/
theorem sampleFrom_later_close (source
  : Sequence.DiskSamples)
    {oldIndex newIndex : Nat} (order : oldIndex ≤ newIndex) :
    Data.Gaussian.Norm.Basic.normSq
      (sampleFrom source newIndex -
      sampleFrom source oldIndex) ≤
      Geometric.Basic.quarterRadius errorScale
        oldIndex := by
  have truncation :
      Data.Gaussian.Norm.Basic.normSq
          (Sample.sample
              (source.value newIndex) newIndex -
            Sample.sample
              (source.value newIndex) oldIndex) ≤
        5 * (1 / 4 : Fraction.Rational) ^ oldIndex :=
    @Sample.sample_later_close
      (source.value newIndex) (source.bound newIndex) oldIndex newIndex order
  have inputEffect :
      Data.Gaussian.Norm.Basic.normSq
          (Sample.sample
              (source.value newIndex) oldIndex -
            Sample.sample
              (source.value oldIndex) oldIndex) ≤
        inputEffectScale * (1 / 4 : Fraction.Rational)
          ^ oldIndex :=
    @sampleFrom_input_effect source oldIndex newIndex
      order
  calc
    Data.Gaussian.Norm.Basic.normSq
      (sampleFrom source newIndex -
      sampleFrom source oldIndex) ≤
        2 * (Data.Gaussian.Norm.Basic.normSq
          (Sample.sample
              (source.value newIndex) newIndex -
            Sample.sample
              (source.value newIndex) oldIndex) +
          Data.Gaussian.Norm.Basic.normSq
          (Sample.sample
              (source.value newIndex) oldIndex -
            Sample.sample
              (source.value oldIndex) oldIndex)) :=
      Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
    _ ≤ 2 * (truncationScale * (1 / 4 :
      Fraction.Rational) ^ oldIndex +
        inputEffectScale * (1 / 4 : Fraction.Rational)
          ^ oldIndex) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (by
            simpa only [truncationScale]
              using truncation)
          inputEffect) (by decide)
    _ = Geometric.Basic.quarterRadius errorScale
      oldIndex := by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow,
        errorScale,
        truncationScale]
      ring1
end Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Sample

end
