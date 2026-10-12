module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Sequence.CCL.Output
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Approximation.Gaussian.Logarithm.Chart.Branch
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic

open Purelib

open Purelib.Approximation.Gaussian.Logarithm

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Logarithm.Chart.Exact.Inverse

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Data.CCL.Transducer.Machine

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

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.CCL.ExactInverse

/-- Exponentiating the exact charted logarithm name emits exactly the requested finite bit count and preserves its
initial prefix. -/
theorem expChartedLogNamed_productive (input :
  Data.Gaussian.Basic.Canonical)
    (chart : Approximation.Gaussian.Logarithm.Chart (Named.exact input))
    (certificate : Branch.BranchCertificate
      (Named.exact input) chart)
    (count : Nat) :
    (Sequence.expChartedLogNamed input chart certificate).machine.emitted.IsPrefix
        (Advance.advance
          (Sequence.expChartedLogNamed input chart certificate).machine count).emitted ∧
      (Advance.advance
          (Sequence.expChartedLogNamed input chart certificate).machine count).emitted.length =
        count :=
  (Sequence.expChartedLogApproximation input chart certificate).output_productive count
end Purelib.Approximation.Gaussian.Logarithm.Chart.CCL.ExactInverse

end
