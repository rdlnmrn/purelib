module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Congruence
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Transport
import Purelib.Approximation.Gaussian.Name.Coherent
import Init.Prelude
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Data.Gaussian.Basic

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Name

section
@[expose] public section

/-!
# Operational congruence for anchored logarithm charts

Two finite chart constructions may use different based process state types and
different proofs of denominator and disk safety.  When their inputs are
operationally equivalent and they retain the same rational factor and
operationally equivalent branch corrections, their actual charted logarithm
outputs are operationally equivalent.

This is the schedule-coherence bridge needed by retryable anchored logarithm
preflight.  It compares finite programs directly; it does not identify
independently selected branches from equality of their exponentials.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Transport.Congruence

/-- Two safe transports from the same fixed source anchor have equivalent outputs whenever their target names are
operationally equivalent. Both transports retain the source factor and correction by construction. -/
def transportedOutput_respects
    {sourceInput leftTarget rightTarget : Coherent.CoherentNamed}
    (source : Anchored.AnchoredChart sourceInput)
    (leftExtension : Transport.SafeOverlapExtension
      sourceInput leftTarget source)
    (rightExtension : Transport.SafeOverlapExtension
      sourceInput rightTarget source)
    (targetEquivalent : Gaussian.Equivalence.NamedEquivalent leftTarget.name rightTarget.name) :
    Gaussian.Equivalence.NamedEquivalent
      (leftExtension.transport source).output.name
      (rightExtension.transport source).output.name :=
  Congruence.output_respects leftTarget rightTarget
    (leftExtension.transport source) (rightExtension.transport source)
    targetEquivalent rfl
    (NamedEquivalent.refl
      source.chart.correction)

end Purelib.Approximation.Gaussian.Logarithm.Chart.Transport.Congruence

end
