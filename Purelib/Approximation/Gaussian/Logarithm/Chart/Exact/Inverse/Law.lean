module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Approximation.Gaussian.Logarithm.Chart.Branch
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Sequence.Constant
public import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Geometric.Quarter
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Law

open Purelib
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Logarithm
open Purelib.Approximation.Gaussian.Logarithm.Chart
open Purelib.Approximation.Gaussian.Logarithm.Chart.Exact.Inverse
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Gaussian.Sequence.Name
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat
open Purelib.Data.Rat.Geometric

public section

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

open Purelib.Approximation

/-- Constructive finite-request inverse law for an anchored chart: `exp(log(input; factor, correction))` is
operationally equal to the exact rational input.

For every positive rational squared tolerance the comparison computes a depth after which all displayed samples satisfy
that tolerance. -/
@[expose] def exp_charted_log_equivalent (input : Data.Gaussian.Basic.Canonical)
    (chart : Chart (Named.exact input))
    (certificate : Branch.BranchCertificate
      (Named.exact input) chart) :
    Gaussian.Equivalence.Equivalent (Sequence.expChartedLogApproximation input chart certificate)
      (Constant.exactInputApproximation input) where
  compare := by
    intro leftStart rightStart target positive
    let leftIndex := Search.firstQuarterBelow
      (Sequence.expChartedLogErrorScale input chart) leftStart target
    have leftSmall :
        Sequence.expChartedLogErrorScale input chart * (1 / 4) ^ leftIndex < target := by
      simpa only [Geometric.Basic.quarterRadius_eq_mul_pow]
        using Search.firstQuarterBelow_accurate
          (Sequence.expChartedLogErrorScale input chart)
          (Sequence.expChartedLogErrorScale_nonnegative input chart)
          leftStart target positive
    exact
      { leftIndex := leftIndex
        rightIndex := rightStart
        left_ge := Search.firstQuarterBelow_ge
          (Sequence.expChartedLogErrorScale input chart) leftStart target
        right_ge := Nat.le_refl _
        close := by
          intro leftLater rightLater leftOrder rightOrder
          change Data.Gaussian.Norm.Basic.normSq
            (Sequence.expChartedLogSample input chart certificate leftLater - input) <
              target
          exact (Sequence.expChartedLogSample_error input chart certificate leftLater).trans_lt
            ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (Quarter.quarterPower_antitone leftOrder)
              (Sequence.expChartedLogErrorScale_nonnegative input chart)).trans_lt
                leftSmall) }

/-- The productive CCL output of the anchored inverse calculation is itself operationally equal, as a CCL name, to the
exact displayed rational input. -/
@[expose] def exp_charted_log_named_equivalent (input : Data.Gaussian.Basic.Canonical)
    (chart : Chart (Named.exact input))
    (certificate : Branch.BranchCertificate
      (Named.exact input) chart) :
    Gaussian.Equivalence.NamedEquivalent (Sequence.expChartedLogNamed input chart certificate)
      (Named.exact input) :=
  Equivalent.trans
    (Equivalent.toNamed_sampling
      (Sequence.expChartedLogApproximation input chart certificate))
    (Equivalent.trans
      (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Law.exp_charted_log_equivalent input chart certificate)
      (Exact.exactInput_to_exactNamed_equivalent input))

end

end Purelib.Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Law
