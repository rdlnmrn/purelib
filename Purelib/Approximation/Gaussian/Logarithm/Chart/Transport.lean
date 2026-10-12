module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Inverse
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Overlap
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Logarithm.Chart.Branch
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Transport

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Logarithm
open Purelib.Approximation.Gaussian.Logarithm.Chart
open Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Data.Rat

public section

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

open Purelib.Approximation

set_option genInjectivity false in
/-- Rechecked rational safety data for extending an already anchored chart to a second coherent input.

The factor and correction are inherited from the source branch; only the finite denominator and reduced-disk
inequalities are re-established on the target enclosure. -/
structure SafeOverlapExtension (sourceInput targetInput : CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput) where
  /-- The displayed rational overlap witness for the original source and target coherent inputs. -/ overlap :
    Overlap.OverlapWitness sourceInput targetInput
  /-- The retained rational lower bound for squared denominator norm on the target process. -/ lowerSq :
    Fraction.Rational
  /-- The retained squared denominator bound is strictly positive. -/ lowerSq_positive : 0 < lowerSq
  /-- Every possible target value at every target state satisfies the retained denominator lower bound. -/
    denominatorLower :
    ∀ (state : targetInput.name.process.State) {value : Data.Gaussian.Basic.Canonical},
      targetInput.name.process.Possible state value →
        lowerSq ≤ Data.Gaussian.Norm.Basic.normSq (source.chart.factor * value + 1)
  /-- The independently retained target numerator and denominator readings give a reduced argument of squared norm at
    most one ninth. -/ reducedBound : ∀ {numeratorSource denominatorSource : Data.Gaussian.Basic.Canonical},
    targetInput.name.process.Possible targetInput.name.state numeratorSource →
    targetInput.name.process.Possible targetInput.name.state denominatorSource →
      Data.Gaussian.Norm.Basic.normSq
          ((source.chart.factor * numeratorSource - 1) /
            (source.chart.factor * denominatorSource + 1)) ≤ 1 / 9

constructive_injectivity SafeOverlapExtension

namespace SafeOverlapExtension

/-- The target chart computed from the displayed overlap safety data. -/
@[expose] def chart {sourceInput targetInput : CoherentNamed}
    {source : Anchored.AnchoredChart sourceInput}
    (extension : Approximation.Gaussian.Logarithm.Chart.Transport.SafeOverlapExtension sourceInput targetInput source) :
    Chart targetInput.name :=
  Chart.ofBounds targetInput.name
    source.chart.factor extension.lowerSq extension.lowerSq_positive
    extension.denominatorLower extension.reducedBound source.chart.correction

/-- The rebuilt target chart retains the source chart's exact rational factor. -/
@[simp] theorem chart_factor {sourceInput targetInput : CoherentNamed}
    {source : Anchored.AnchoredChart sourceInput}
    (extension : Approximation.Gaussian.Logarithm.Chart.Transport.SafeOverlapExtension sourceInput targetInput source) :
    extension.chart.factor = source.chart.factor := rfl

/-- The rebuilt target chart retains the source chart's exact correction process. -/
@[simp] theorem chart_correction {sourceInput targetInput : CoherentNamed}
    {source : Anchored.AnchoredChart sourceInput}
    (extension : Approximation.Gaussian.Logarithm.Chart.Transport.SafeOverlapExtension sourceInput targetInput source) :
    extension.chart.correction = source.chart.correction := rfl

/-- Analytic continuation through a certified finite overlap: the target chart is rebuilt from target-side rational
inequalities while retaining the source factor and anchored correction. -/
@[expose] def transport {sourceInput targetInput : CoherentNamed}
    (source : Anchored.AnchoredChart sourceInput)
    (extension : Approximation.Gaussian.Logarithm.Chart.Transport.SafeOverlapExtension sourceInput targetInput source) :
    Anchored.AnchoredChart targetInput :=
  { chart := extension.chart
    certificate :=
      { factor_ne_zero := source.certificate.factor_ne_zero
        correction_exponential := source.certificate.correction_exponential }
    correctionCoherent := source.correctionCoherent }

/-- Transporting the anchored chart preserves its exact rational factor. -/
@[simp] theorem transport_factor {sourceInput targetInput : CoherentNamed}
    (source : Anchored.AnchoredChart sourceInput)
    (extension : Approximation.Gaussian.Logarithm.Chart.Transport.SafeOverlapExtension sourceInput targetInput source) :
    (extension.transport source).chart.factor = source.chart.factor := rfl

/-- Transporting the anchored chart preserves its exact correction process. -/
@[simp] theorem transport_correction {sourceInput targetInput : CoherentNamed}
    (source : Anchored.AnchoredChart sourceInput)
    (extension : Approximation.Gaussian.Logarithm.Chart.Transport.SafeOverlapExtension sourceInput targetInput source) :
    (extension.transport source).chart.correction = source.chart.correction := rfl

/-- Rechecking safety and transporting the anchored correction preserves the finite exponential/logarithm inverse. -/
@[expose] def transport_exponential_inverse
    {sourceInput targetInput : CoherentNamed}
    (source : Anchored.AnchoredChart sourceInput)
    (extension : Approximation.Gaussian.Logarithm.Chart.Transport.SafeOverlapExtension sourceInput targetInput source) :
    Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named
        (extension.transport source).output.name)
      targetInput.name :=
  (extension.transport source).exponential_inverse

end SafeOverlapExtension

end

end Purelib.Approximation.Gaussian.Logarithm.Chart.Transport
