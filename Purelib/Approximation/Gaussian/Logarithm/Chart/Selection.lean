module
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Exponential.LocalInjectivity
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Coherent
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
import Purelib.Approximation.Gaussian.Logarithm.Chart.Inverse
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Transport
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Difference
public import Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic
import Init.Core
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Inverse
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Approximation.Gaussian.Name.Basic

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Selection

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Approximation.Gaussian.Logarithm.Chart
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic

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

/-- The result of finite preimage selection: both the constructed anchored chart and the derived zero alignment are
retained. -/
@[expose] def SelectedLogarithm (input : CoherentNamed) : Type 1 :=
  Sigma fun branch : Anchored.AnchoredChart
    (Exponential.Progressive.Range.Coherent.exp input.name) =>
      Difference.LocalAlignment input branch.output

namespace SelectedLogarithm

/-- Read the selected anchored chart over the actual exponential input. -/
@[expose] def branch {input : CoherentNamed} (selection :
  Approximation.Gaussian.Logarithm.Chart.Selection.SelectedLogarithm input) :
    Anchored.AnchoredChart (Exponential.Progressive.Range.Coherent.exp input.name) :=
  selection.1

/-- Read the selected branch's retained zero alignment with the original input. -/
@[expose] def alignment {input : CoherentNamed} (selection :
  Approximation.Gaussian.Logarithm.Chart.Selection.SelectedLogarithm input) :
    Difference.LocalAlignment input selection.branch.output :=
  selection.2

/-- Construct the logarithm branch over the actual computed exponential by transport through a certified overlap, then
use the displayed local injectivity cell to select the preimage near `input`.

The caller supplies no `LocalAlignment`; it is computed below. -/
@[expose] def ofOverlap (input sourceInput : CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (extension : Transport.SafeOverlapExtension sourceInput
      (Exponential.Progressive.Range.Coherent.exp input.name) source)
    (injectivity : LocalInjectivity.LocalExpInjectivity
      (extension.transport source).output input) :
    Approximation.Gaussian.Logarithm.Chart.Selection.SelectedLogarithm input := by
  let branch := extension.transport source
  have exponentials : Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named branch.output.name)
      (Exponential.Progressive.Range.Name.named input.name) := by
    simpa only [branch,
      Exponential.Progressive.Range.Coherent.exp] using
      branch.exponential_inverse
  have selected : Gaussian.Equivalence.NamedEquivalent branch.output.name input.name :=
    injectivity.identify exponentials
  exact ⟨branch, Difference.difference_zero_of_equivalent input branch.output selected⟩

/-- The constructed local branch proves the reverse exponential/logarithm inverse without a caller-supplied alignment
premise. -/
@[expose] def logarithm_exponential_inverse (input : CoherentNamed)
    (selection : Approximation.Gaussian.Logarithm.Chart.Selection.SelectedLogarithm input) :
    Gaussian.Equivalence.NamedEquivalent selection.branch.output.name input.name :=
  Inverse.logarithm_exponential_inverse input
    selection.branch selection.alignment

/-- Bit-producing form of the automatically selected local inverse. -/
@[expose] def logarithm_exponential_bitLaw (input : CoherentNamed)
    (selection : Approximation.Gaussian.Logarithm.Chart.Selection.SelectedLogarithm input) :
    Law.Basic.BitLaw selection.branch.output input :=
  BitLaw.ofEquivalent
    (selection.logarithm_exponential_inverse input)

end SelectedLogarithm

end

end Purelib.Approximation.Gaussian.Logarithm.Chart.Selection
