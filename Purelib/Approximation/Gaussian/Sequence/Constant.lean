module
public import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Sequence

section
@[expose] public section

/-!
# Finite operational laws for transcendental CCL programs

This module begins the analytic identification layer without adjoining a
completed non-rational value.  Laws compare finite approximation programs:
from any current indices and any positive displayed rational tolerance they
compute synchronized later indices whose entire displayed tails agree to that
tolerance.

The exponential addition law will be proved here by a finite polynomial
Cauchy-product identity followed by explicit rational remainder bounds.  The
normalization law `exp(0) = 1` is already exact at every finite Horner depth.
-/

namespace Purelib.Approximation.Gaussian.Sequence.Constant

/-- The exact constant approximation. It answers every refinement request without changing its displayed rational
sample. -/
def constantApproximation (value :
  Data.Gaussian.Basic.Canonical) : ApproximationData where
  sample := fun _ => value
  radiusSq := fun _ => 0
  radiusSq_nonneg := fun _ => by decide
  later_close := by
    intro earlier later order
    simp only [_root_.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
    exact le_rfl
  refineIndex := fun current _ _ => current
  refineIndex_ge := by
    intro current target positive
    exact Nat.le_refl current
  refineIndex_accurate := by
    intro current target positive
    exact positive
  centerBound := Data.Gaussian.Norm.Basic.normSq value
  centerBound_nonneg := Data.Gaussian.Norm.Basic.normSq_nonneg value
  sample_bounded := by
    intro index
    exact le_rfl

/-- The exact constant-one Gaussian rational approximation with zero squared-error allowance. -/
def oneApproximation : Gaussian.Sequence.ApproximationData :=
  constantApproximation 1

/-- Every finite sample of the exact constant-one approximation is one. -/
theorem one_sample (index : Nat) :
  oneApproximation.sample index = 1 := rfl
end Purelib.Approximation.Gaussian.Sequence.Constant

end

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

namespace Purelib.Approximation.Gaussian.Sequence.Constant

/-- The constant approximation retaining the displayed Gaussian rational input at every finite sample. -/
def exactInputApproximation (input :
  Data.Gaussian.Basic.Canonical) : Gaussian.Sequence.ApproximationData :=
  constantApproximation input
end Purelib.Approximation.Gaussian.Sequence.Constant

end
