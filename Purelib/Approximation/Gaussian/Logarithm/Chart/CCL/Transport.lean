module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
import Purelib.Approximation.Gaussian.Logarithm.Chart.CCL.Output
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Transport
import Purelib.Approximation.Gaussian.Name.CCL.Contract
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Refinement
import Purelib.Data.CCL.Transducer.Machine.Advance
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Data.CCL.Transducer.Machine

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite geometry for transporting and selecting logarithm branches

An anchored complex logarithm is local data.  This file supplies the missing
geometric constructors around that data.

* `SafeOverlapExtension` rechecks one chart's rational denominator and
  reduced-disk inequalities on a second coherent name and records an actual
  rational point admitted by both finite enclosures.  The original factor,
  correction process, and correction certificate can then be transported.
* `LocalExpInjectivity` is a displayed finite cell, membership certificates
  for two particular coherent names, and the local exponential-injectivity
  rule for that pair.  It is deliberately local and never chooses a global
  logarithm branch.
* `SelectedLogarithm.ofOverlap` combines those two pieces of finite data.  It
  constructs an anchored chart over the computed exponential and derives the
  zero-alignment certificate required for `log (exp x) = x`.

The local complex-log congruence proved first is quantitative: it compares
finite reduced-argument samples with the existing rational sensitivity bound
and finite truncation bounds.  No completed logarithm or limiting argument is
introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Transport
namespace SafeOverlapExtension

/-- The transported branch is still an ordinary productive CCL computation. -/
theorem transport_productive
  {sourceInput targetInput : CoherentNamed}
    (source : Anchored.AnchoredChart sourceInput)
    (extension : Transport.SafeOverlapExtension sourceInput targetInput source)
    (count : Nat) :
    (extension.transport source).output.name.machine.emitted.IsPrefix
        (Advance.advance
          (extension.transport source).output.name.machine count).emitted ∧
      (Advance.advance
        (extension.transport source).output.name.machine count).emitted.length =
          count :=
  CCL.Output.productive targetInput.name
    (extension.transport source).chart count

/-- Full finite request contract for the transported branch: one refinement answers the rational accuracy request, and
the ordinary CCL cursor emits the requested number of bits with exact parser semantics. -/
theorem
  transport_bitstream_and_error
    {sourceInput targetInput : CoherentNamed}
    (source : Anchored.AnchoredChart sourceInput)
    (extension : Transport.SafeOverlapExtension sourceInput targetInput source)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) :
    let refined := Refinement.refined
      (extension.transport source).output.name target positive
    (refined.process.ball refined.state).radiusSq < target ∧
      refined.machine.emitted.IsPrefix
        (Advance.advance
          refined.machine count).emitted ∧
      (Advance.advance
        refined.machine count).emitted.length = count ∧
      Semantics.Basic.ExactCursor
        refined.process refined.state
        (Advance.advance refined.machine count) :=
  CCL.Contract.refined_bitstream_and_error
    (extension.transport source).output.name target positive count
end SafeOverlapExtension

end Purelib.Approximation.Gaussian.Logarithm.Chart.Transport

end
