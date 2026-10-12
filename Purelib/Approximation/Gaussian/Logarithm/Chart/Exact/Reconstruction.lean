module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Branch
import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Division
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Projective.Homography.Cayley.Bounds
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Gaussian.Logarithm (Chart)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation.Gaussian.Logarithm

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Sampling

open Purelib.Data.Gaussian

section
@[expose] public section

/-!
# Operational branch certificates for the complex logarithm

The geometric `Chart` data proves that its finite local recurrence is safe
and productive.  It intentionally permits any additive correction name.
This module records the additional semantic obligation needed to call that
correction a logarithm branch: exponentiating it must reproduce the inverse
of the chart's displayed scale, in finite operational equality.

Once the local inverse law and the exponential addition law are established,
this certificate is the missing branch datum in the calculation

`Exp(localLog(factor * input) + correction) = input`.

The exponentiation, equality, and inverse factor below are all CCL programs
or displayed Gaussian rationals.  No completed complex number or global
single-valued logarithm is introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Exact.Reconstruction

/-! ## Finite anchored inverse law for displayed rational inputs -/

/-- The rational reduced coordinate displayed by an exact chart input. -/
def exactReducedValue (input :
  Canonical)
    (chart : Chart (Named.exact input)) :
    Canonical :=
  (chart.factor * input - 1) / (chart.factor * input + 1)

/-- The denominator of an exact chart's reduced coordinate is nonzero by its retained apartness certificate. -/
theorem exactReducedValue_denominator_ne_zero
  (input : Canonical)
    (chart : Chart (Named.exact input)) :
    chart.factor * input + 1 ≠ 0 := by
  let denominator := Reduction.denominator
    (Named.exact input) chart.factor
  let state := denominator.state
  rcases denominator.process.witness state with ⟨value, possible⟩
  rcases Reduction.denominator_possible
      (Named.exact input) chart.factor
      possible with ⟨source, sourcePossible, valueEqual⟩
  change source = input at sourcePossible
  subst source
  rw [valueEqual] at possible
  have lower := chart.denominatorApart.lower state possible
  intro denominatorZero
  rw [denominatorZero, Data.Gaussian.Norm.Basic.normSq_zero] at lower
  exact (not_le_of_gt chart.denominatorApart.positive) lower

/-- Every canonical sample of the exact chart's reduced process equals its displayed rational reduced coordinate. -/
theorem
  reduced_inputSample_eq_exactReducedValue
  (input : Canonical)
    (chart : Chart (Named.exact input))
    (index : Nat) :
    ComplexLog.inputSample
        (Reduction.reduced
          (Named.exact input)
          chart.factor chart.denominatorApart) index =
      exactReducedValue input chart := by
  let reduced := Reduction.reduced
    (Named.exact input)
    chart.factor chart.denominatorApart
  have possible :=
    ComplexLog.inputSample_possible_start
      reduced index
  rcases Reduction.reduced_possible
      (Named.exact input)
      chart.factor chart.denominatorApart possible with
    ⟨numeratorSource, denominatorSource, numeratorPossible,
      denominatorPossible, valueEqual⟩
  change numeratorSource = input at numeratorPossible
  change denominatorSource = input at denominatorPossible
  subst numeratorSource
  subst denominatorSource
  exact valueEqual

/-- The exact reduced coordinate satisfies the chart's one-ninth quadrance bound. -/
theorem exactReducedValue_disk (input :
  Canonical)
    (chart : Chart (Named.exact input)) :
    Data.Gaussian.Norm.Basic.normSq
      (exactReducedValue input chart) ≤ 1 / 9 := by
  let reduced := Reduction.reduced
    (Named.exact input)
    chart.factor chart.denominatorApart
  have possible :=
    ComplexLog.inputSample_possible_start reduced 0
  have bound := chart.reducedDisk.possible_normSq possible
  rwa [reduced_inputSample_eq_exactReducedValue input chart
    0] at bound

/-- Applying the Cayley reconstruction to the exact reduced coordinate recovers the scaled original Gaussian input. -/
theorem exactReducedValue_chart (input :
  Canonical)
    (chart : Chart (Named.exact input)) :
    (1 + exactReducedValue input chart) /
        (1 - exactReducedValue input chart) =
      chart.factor * input := by
  let scaled := chart.factor * input
  let reduced := exactReducedValue input chart
  have denominatorNonzero : scaled + 1 ≠ 0 := by
    exact exactReducedValue_denominator_ne_zero input chart
  have reducedIdentity : reduced * (scaled + 1) = scaled - 1 := by
    exact Division.gaussian_div_mul_cancel
      (scaled - 1) (scaled + 1) denominatorNonzero
  have reducedBound : Data.Gaussian.Norm.Basic.normSq reduced ≤ 1 / 9 :=
    exactReducedValue_disk input chart
  have oneSubNonzero : 1 - reduced ≠ 0 :=
    Geometry.Projective.Homography.Cayley.Bounds.one_sub_ne_zero reducedBound
  have reducedCancellation :
      (1 - reduced) * (scaled + 1) = 1 + 1 := by
    calc
      (1 - reduced) * (scaled + 1) =
          (scaled + 1) - reduced * (scaled + 1) := by
        apply Data.Gaussian.Basic.ext <;>
          simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im,
            Basic.one_re, Basic.one_im] <;> ring1
      _ = (scaled + 1) - (scaled - 1) := by rw [reducedIdentity]
      _ = 1 + 1 := by
        apply Data.Gaussian.Basic.ext <;>
          simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Basic.one_re, Basic.one_im] <;> ring1
  apply Data.Gaussian.Field.mul_right_cancel_of_ne
    oneSubNonzero
  rw [Division.gaussian_div_mul_cancel
    (1 + reduced) (1 - reduced) oneSubNonzero]
  apply Data.Gaussian.Field.mul_right_cancel_of_ne
    denominatorNonzero
  calc
    (1 + reduced) * (scaled + 1) =
        (scaled + 1) + reduced * (scaled + 1) := by ring1
    _ = (scaled + 1) + (scaled - 1) := by rw [reducedIdentity]
    _ = scaled * (1 - reduced) * (scaled + 1) := by
      rw [Data.Gaussian.Basic.mul_assoc, reducedCancellation]
      apply Data.Gaussian.Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im,
          Basic.one_re, Basic.one_im] <;> ring1

/-- The reconstructed exact chart value multiplied by the reciprocal chart factor equals the original input.

The retained branch certificate supplies the nonzero scaling factor. -/
theorem exactReducedValue_chart_times_inverse
  (input : Canonical)
    (chart : Chart (Named.exact input))
    (certificate : Branch.BranchCertificate
      (Named.exact input) chart) :
    ((1 + exactReducedValue input chart) /
        (1 - exactReducedValue input chart)) * (1 /
          chart.factor) = input := by
  rw [exactReducedValue_chart input chart,
    Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    chart.factor * input * (1 * chart.factor⁻¹) =
        input * (chart.factor * chart.factor⁻¹) := by
      rw [Data.Gaussian.Basic.one_mul,
        Data.Gaussian.Basic.mul_comm chart.factor input,
        Data.Gaussian.Basic.mul_assoc]
    _ = input * 1 := by
      rw [show chart.factor * chart.factor⁻¹ = 1 by
        simpa only [Data.Gaussian.Field.inv_eq] using
          Data.Gaussian.Field.mul_inv chart.factor
            certificate.factor_ne_zero]
    _ = input := Data.Gaussian.Basic.mul_one input
end Purelib.Approximation.Gaussian.Logarithm.Chart.Exact.Reconstruction

end
