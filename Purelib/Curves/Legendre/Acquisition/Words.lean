module
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Approximation.Gaussian.Acquisition.Signed.Requested
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Rat.Fraction

import Purelib.Approximation.Gaussian.Acquisition.Provenance
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Provenance
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Separated
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Basic
import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Positive
import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Signed
public import Purelib.Curves.Legendre.Acquisition.Words.Report
import Purelib.Curves.Legendre.Acquisition.Words.State
import Purelib.Curves.Legendre.FractionalWords.Periods
import Purelib.Curves.Legendre.GuaranteedFold
import Purelib.Curves.Legendre.SeparatedWords
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Enclosure.Signed
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Curves.Legendre.Acquisition.Automatic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Signed

open Purelib.Approximation.Gaussian.FractionalAction.Integral

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Process.Imaginary

open Purelib.Curves.Legendre

open Purelib.Data.Rat

open Purelib.Topology.Knot

section
@[expose] public section

/-!
# Evidence-directed finite Legendre words

Reuse a cached provider or separation first. Nonreal rational provenance
automatically constructs and transports an all-row provider. Otherwise one
signed numerical inspection prepares either half-plane, or returns retained
near-boundary evidence. Nonzeroness of the input alone is not used as a
certificate for every intermediate word denominator. Real inputs and
unsupported symbolic provenance may remain inconclusive by this sufficient
test; this is not a decision procedure for each particular real word.
-/

namespace Purelib.Curves.Legendre.Acquisition.Words

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic (Provider)

/-- Cache the retained all-row provider and construct the original finite word report at the same acquisition
transition. -/
def prepare {tau : Coherent.CoherentNamed} {input :
  Curves.Legendre.Acquisition.Words.State.Input tau} (step : Curves.Legendre.Acquisition.Words.State.Step input)
    (provider : Preparation.Basic.Provider tau) (word : SeparatedWords.Word) (delta : Fraction.Rational) :
      Curves.Legendre.Acquisition.Words.Report input word delta :=
  ⟨step.cache provider, .ready (SeparatedWords.acquireWithProvider provider word)⟩

/-- Inspect the original input once at the requested positive radius.

Positive and negative separation both prepare the word; near-boundary evidence retains the exact inspected next state.
-/
def numerical {tau : Coherent.CoherentNamed} (input :
  Curves.Legendre.Acquisition.Words.State.Input tau) (word : SeparatedWords.Word) (delta : Fraction.Rational) (positive
  : 0 < delta) :
    Curves.Legendre.Acquisition.Words.Report input word delta :=
  let report := Requested.acquire tau input.state delta positive
  match report.2 with
  | .positive high _ => prepare
    (Curves.Legendre.Acquisition.Words.State.Step.inspected input .positive report)
      (Separated.provider (Separation.ofPositive (report.enclosure high))) word delta
  | .negative _ upper => prepare
    (Curves.Legendre.Acquisition.Words.State.Step.inspected input .negative report)
      (Separated.provider
        (Separation.ofNegative positive (report.negative upper))) word delta
  | .near bounds => ⟨Curves.Legendre.Acquisition.Words.State.Step.inspected input .near report, .near (report.near
    bounds)⟩

/-- Prepare the original word using retained evidence before requesting a numerical inspection.

Reuse a cached provider, then retained separation, then supported rational provenance; otherwise preserve the exact
result of signed acquisition. -/
def acquire {tau : Coherent.CoherentNamed} (input :
  Curves.Legendre.Acquisition.Words.State.Input tau) (word : SeparatedWords.Word) (delta : Fraction.Rational) (positive
  : 0 < delta) :
    Curves.Legendre.Acquisition.Words.Report input word delta :=
  match input.provider with
  | some provider => prepare (Curves.Legendre.Acquisition.Words.State.Step.unchanged
    input .cached) provider word delta
  | none => match input.separation with
    | some separation => prepare
      (Curves.Legendre.Acquisition.Words.State.Step.unchanged input .separation)
        (Separated.provider separation) word delta
    | none => match Provenance.inferredProvider input.provenance with
      | some provider => prepare
        (Curves.Legendre.Acquisition.Words.State.Step.unchanged input .rational) provider word delta
      | none => numerical input word delta positive

/-- Resume acquisition from the report's actual retained next state for the next word and positive radius. -/
def Report.resume {tau : Coherent.CoherentNamed} {input :
  Curves.Legendre.Acquisition.Words.State.Input tau} {word : SeparatedWords.Word} {delta : Fraction.Rational}
    (report : Curves.Legendre.Acquisition.Words.Report input word delta) (nextWord : SeparatedWords.Word)
      (nextDelta : Fraction.Rational) (positive : 0 < nextDelta) :
    Curves.Legendre.Acquisition.Words.Report report.1.next nextWord nextDelta :=
      acquire report.1.next nextWord nextDelta positive

/-- Continue at the actual folded output, using its cached final provider. This is distinct from evaluating another word
at the original input. -/
def continueFrom {tau : Coherent.CoherentNamed} {word :
  SeparatedWords.Word}
    (report : SeparatedWords.Report tau word) : Curves.Legendre.Acquisition.Words.State.Input report.output :=
  { state := State.initial report.output
    provenance := none
    provider := some report.folded.2 }
end Purelib.Curves.Legendre.Acquisition.Words

end

section
@[expose] public section

/-!
# Finite certificate acquisition: public theorem interface

Three distinct contracts are exposed here, without a universal partiality
framework:

* `boundedDivision` makes one prescribed request and returns an ordinary
  cached quotient or whole-ball smallness with persistent candidate bounds.
* `gapDivision` turns smallness into exact branch exclusion under a proved
  zero-or-gap law. `signedGap` computes a sufficient canonical inspection
  budget from an unsigned imaginary gap.
* `exact` decides between an equivalent prepared presentation and operational
  zero for the two supported finite provenance classes. Its semantic iff
  and presentation-invariance laws do not apply to opaque inputs lacking
  this provenance, nor to the overlapping numerical small/apart verdicts.

`separatedWord` prepares an entire word in either half-plane and exposes
single/fold agreement, braid invariance, reversal, and the dual period law
through its retained report. Negative imaginary evidence is not global
non-certifiability. Precision and inspection counts below are not CPU-time,
allocation, certificate-size, or general-polynomial separation bounds.
-/

namespace Purelib.Curves.Legendre.Acquisition.Words

/-- Prepare the original finite braid word from its retained unsigned imaginary separation. -/
def separatedWord {tau : Coherent.CoherentNamed}
    (separation : Approximation.Gaussian.Process.Imaginary.Separation tau)
    (word : Braid.Word 3) : SeparatedWords.Report tau word :=
  SeparatedWords.acquire separation word

end Purelib.Curves.Legendre.Acquisition.Words

end
