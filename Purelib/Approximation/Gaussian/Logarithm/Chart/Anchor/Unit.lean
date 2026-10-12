module
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Exact
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Logarithm.Chart.Branch
import Purelib.Data.Gaussian.Field

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Logarithm

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

section
@[expose] public section

/-!
# Exact finite seeds for anchored logarithm transport

The retryable logarithm layer needs at least one completely explicit source
anchor.  The exact rational input `1` uses the existing unit complex-log chart,
the exact-zero correction, and the proved operational identity `exp 0 = 1`.
This is local finite branch data, not a global logarithm convention.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Anchor.Unit

/-- The exact coherent input at the rational unit. -/
def exactOneInput : Coherent.CoherentNamed :=
  Coherence.exact 1

/-- A completely explicit anchored chart at `1`. Its branch correction is exact zero, whose finite automatic exponential
is operationally exact one. -/
def exactOneAnchor : Anchored.AnchoredChart
  exactOneInput where
  chart := Chart.Basic.unitChart
  certificate :=
    { factor_ne_zero := by
        change (1 : Data.Gaussian.Basic.Canonical) ≠ 0
        decide
      correction_exponential := by
        change Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
          (Exponential.Progressive.Range.Name.named
            (Named.exact 0))
          (Named.exact 1)
        exact Exponential.Progressive.Range.Exact.automaticExp_zero }
  correctionCoherent := by
    change Gaussian.Process.Coherence.Basic.Coherent
      (Named.exact 0).process
    exact Gaussian.Process.Coherence.Basic.Coherent.exact 0
end Purelib.Approximation.Gaussian.Logarithm.Chart.Anchor.Unit

end
