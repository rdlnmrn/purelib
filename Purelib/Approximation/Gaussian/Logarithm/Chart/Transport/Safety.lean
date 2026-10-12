module
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Safety
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Transport
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Based
import Purelib.Approximation.Gaussian.Name.Coherent.Overlap
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

section
@[expose] public section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Transport.Safety

/-- Turn a successful finite ball test and an exact overlap witness into the existing safe anchored-chart transport
datum over the target's based future. -/
def extensionOfBased
    (sourceInput targetInput : Coherent.CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (base : targetInput.name.process.State)
    {index : Nat} (certificate : Safety.Certificate source.chart.factor
      (targetInput.name.process.ball base) index)
    (overlap : Overlap.OverlapWitness sourceInput
      (CoherentNamed.based targetInput base)) :
    Transport.SafeOverlapExtension sourceInput
      (CoherentNamed.based targetInput base) source where
  overlap := overlap
  lowerSq := certificate.lowerSq
  lowerSq_positive := certificate.lowerSq_positive
  denominatorLower := by
    intro state value possible
    apply certificate.denominator_lower
    exact targetInput.name.process.possible_inside
      (state.persists possible)
  reducedBound := by
    intro numeratorSource denominatorSource numeratorPossible
      denominatorPossible
    apply certificate.reduced_bound
    · exact targetInput.name.process.possible_inside numeratorPossible
    · exact targetInput.name.process.possible_inside denominatorPossible

end Purelib.Approximation.Gaussian.Logarithm.Chart.Transport.Safety

end
