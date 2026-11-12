module
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Approximation.Gaussian.Acquisition.Signed.Requested
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Rat.Fraction

import Purelib.Approximation.Gaussian.Acquisition.Provenance
import Purelib.Riemann.RootContinuation.SquareRootSidecar
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

Reuse a cached provider or separation first. Nonreal rational and admitted
irrational quadratic provenance supply all-row providers. Exact rational
readings use ordered denominator inspection, returning complete execution or
the first certified zero row with its prepared prefix. Other inputs use signed
numerical acquisition and may retain inconclusive near-boundary evidence.
Nonzeroness of the input alone is no certificate for every word denominator.
-/

namespace Purelib.Curves.Legendre.Acquisition.Words

open Purelib.Approximation
open Purelib.Riemann.RootContinuation
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic (Provider)

/-- Cache the retained all-row provider and construct the original finite word report at the same acquisition
transition. -/
def prepare {tau : CoherentNamed} {input :
  State.Input tau} (step : State.Step input)
    (provider : Provider tau) (word : SeparatedWords.Word) (delta : Rational) :
      Report input word delta :=
  ⟨step.cache provider, .ready (SeparatedWords.acquireWithProvider provider word)⟩

/-- Inspect the original input once at the requested positive radius.

Positive and negative separation both prepare the word; near-boundary evidence retains the exact inspected next state.
-/
def numerical {tau : CoherentNamed} (input :
  State.Input tau) (word : SeparatedWords.Word) (delta : Rational) (positive
  : 0 < delta) :
    Report input word delta :=
  let report := Requested.acquire tau input.state delta positive
  match report.2 with
  | .positive high _ => prepare
    (State.Step.inspected input .positive report)
      (Separated.provider (Separation.ofPositive (report.enclosure high))) word delta
  | .negative _ upper => prepare
    (State.Step.inspected input .negative report)
      (Separated.provider
        (Separation.ofNegative positive (report.negative upper))) word delta
  | .near bounds => ⟨State.Step.inspected input .near report, .near (report.near
    bounds)⟩

/-- Inspect the actual ordered rational word while retaining the complete original acquisition state unchanged. -/
def rational {tau : CoherentNamed} (input : State.Input tau) (source : RationalSidecar tau)
    (word : SeparatedWords.Word) (delta : Rational) : Report input word delta :=
  ⟨(State.Step.unchanged input .exact).cacheRational source,
    .exact ⟨source, word, rfl, Words.Rational.inspect source
      (FractionalWords.Periods.periodBraidMatrices word)⟩⟩

/-- Prepare the original word using retained evidence before requesting a numerical inspection.

Reuse a cached provider, then retained separation, then supported rational provenance; otherwise preserve the exact
result of signed acquisition. -/
def acquire {tau : CoherentNamed} (input :
  State.Input tau) (word : SeparatedWords.Word) (delta : Rational) (positive
  : 0 < delta) :
    Report input word delta :=
  match input.provider with
  | some provider => prepare (State.Step.unchanged
    input .cached) provider word delta
  | none => match input.separation with
    | some separation => prepare
      (State.Step.unchanged input .separation)
        (Separated.provider separation) word delta
    | none => match input.cachedRational with
      | some reading => rational input reading word delta
      | none => match Provenance.infer input.provenance with
        | .provider provider => prepare
            (State.Step.unchanged input .rational) provider word delta
        | .rational reading => rational input reading word delta
        | .unresolved _ => numerical input word delta positive

/-- A cached original rational reading bypasses symbolic inspection and preserves the entire numerical state. -/
theorem acquire_cached_rational {tau : CoherentNamed} (input : State.Input tau)
    (reading : RationalSidecar tau) (cached : input.cachedRational = some reading)
    (uncached : input.provider = none) (unseparated : input.separation = none)
    (word : SeparatedWords.Word) (delta : Rational) (positive : 0 < delta) :
    acquire input word delta positive = rational input reading word delta := by
  unfold acquire
  rewrite [uncached, unseparated, cached]
  rfl

/-- Exact ordered execution retains the same original reading for subsequent word requests. -/
theorem rational_cached {tau : CoherentNamed} (input : State.Input tau) (reading : RationalSidecar tau)
    (word : SeparatedWords.Word) (delta : Rational) :
    (rational input reading word delta).1.next.cachedRational = some reading := rfl

/-- An original zero-parameter root selects ordered rational inspection at its unchanged retained input state. -/
theorem acquire_zero_root {tau : CoherentNamed} (input : State.Input tau)
    (root : SquareRootSidecar.Sidecar tau) (zero : root.parameter = 0)
    (known : input.provenance = some (.squareRoot root)) (uncached : input.provider = none)
    (unseparated : input.separation = none) (word : SeparatedWords.Word) (delta : Rational) (positive : 0 < delta) :
    (acquire input word delta positive).1.route = .exact ∧
      (acquire input word delta positive).1.next.state = input.state := by
  rcases input with ⟨state, provenance, provider, separation, cachedReading⟩
  change provenance = some (.squareRoot root) at known
  cases known
  change provider = none at uncached
  cases uncached
  change separation = none at unseparated
  cases unseparated
  unfold acquire
  dsimp only
  cases cachedReading with
  | some reading => exact ⟨rfl, rfl⟩
  | none =>
      obtain ⟨reading, selected⟩ := Provenance.infer_zero_root root zero
      rewrite [selected]
      exact ⟨rfl, rfl⟩

/-- Resume acquisition from the report's actual retained next state for the next word and positive radius. -/
def Report.resume {tau : CoherentNamed} {input :
  State.Input tau} {word : SeparatedWords.Word} {delta : Rational}
    (report : Report input word delta) (nextWord : SeparatedWords.Word)
      (nextDelta : Rational) (positive : 0 < nextDelta) :
    Report report.1.next nextWord nextDelta :=
      acquire report.1.next nextWord nextDelta positive

/-- Continue at the actual folded output, using its cached final provider. This is distinct from evaluating another word
at the original input. -/
def continueFrom {tau : CoherentNamed} {word :
  SeparatedWords.Word}
    (report : SeparatedWords.Report tau word) : State.Input report.output :=
  { state := State.initial report.output
    provenance := none
    provider := some report.folded.2 }

/-- Continue at the exact cached output of the executed rational prefix, retaining its same rational reading. -/
def Report.RationalResult.continuePrefix {tau : CoherentNamed} {word : SeparatedWords.Word}
    (result : Report.RationalResult tau word) : State.Input result.execution.output :=
  { state := State.initial result.execution.output
    provenance := some (.rational result.execution.reading)
    cachedRational := some result.execution.reading }

/-- Continuing an exact executed prefix keeps its actual cached rational output evidence. -/
theorem Report.RationalResult.continuePrefix_provenance {tau : CoherentNamed} {word : SeparatedWords.Word}
    (result : Report.RationalResult tau word) :
    result.continuePrefix.provenance = some (.rational result.execution.reading) := rfl
end Purelib.Curves.Legendre.Acquisition.Words

namespace Purelib.Curves.Legendre.Acquisition.Words

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)

/-- Exact real rational acquisition retains its original state and returns ordered domain evidence. -/
private theorem start_exact_properties (input : Annotated) (value : Canonical)
    (known : input.rationalValue = some value) (real : value.im = 0)
    (word : SeparatedWords.Word) (delta : Rational) (positive : 0 < delta) :
    (acquire (State.start input) word delta positive).1.route = .exact ∧
      (acquire (State.start input) word delta positive).1.next.state = (State.start input).state ∧
      ∃ result, (acquire (State.start input) word delta positive).2 = .exact result := by
  obtain ⟨sidecar, selected, same⟩ := input.rationalValue_evidence value known
  have sidecarReal : sidecar.value.im = 0 := (congrArg Canonical.im same).trans real
  have nonreal : ¬ sidecar.value.im ≠ 0 := fun unequal => unequal sidecarReal
  unfold acquire State.start
  dsimp only
  rewrite [selected]
  unfold Provenance.infer
  dsimp only
  rewrite [dif_neg nonreal]
  exact ⟨rfl, rfl, _, rfl⟩

/-- A retained real rational reading selects complete ordered denominator inspection. -/
theorem start_exact (input : Annotated) (value : Canonical) (known : input.rationalValue = some value)
    (real : value.im = 0) (word : SeparatedWords.Word) (delta : Rational) (positive : 0 < delta) :
    (acquire (State.start input) word delta positive).1.route = .exact :=
  (start_exact_properties input value known real word delta positive).1

/-- Exact real rational acquisition preserves the entire original retained numerical state. -/
theorem start_exact_state (input : Annotated) (value : Canonical) (known : input.rationalValue = some value)
    (real : value.im = 0) (word : SeparatedWords.Word) (delta : Rational) (positive : 0 < delta) :
    (acquire (State.start input) word delta positive).1.next.state = (State.start input).state :=
  (start_exact_properties input value known real word delta positive).2.1

/-- Exact real rational acquisition returns its actual complete execution or first-pole result. -/
theorem start_exact_result (input : Annotated) (value : Canonical) (known : input.rationalValue = some value)
    (real : value.im = 0) (word : SeparatedWords.Word) (delta : Rational) (positive : 0 < delta) :
    ∃ result, (acquire (State.start input) word delta positive).2 = .exact result :=
  (start_exact_properties input value known real word delta positive).2.2

/-- Nonreal rational preparation retains both its selected route and original numerical state. -/
private theorem start_rational_properties (input : Annotated) (value : Canonical)
    (known : input.rationalValue = some value)
    (nonreal : value.im ≠ 0) (word : SeparatedWords.Word) (delta : Rational) (positive : 0 < delta) :
    (acquire (State.start input) word delta positive).1.route = .rational ∧
      (acquire (State.start input) word delta positive).1.next.state = (State.start input).state := by
  obtain ⟨sidecar, selected, same⟩ := input.rationalValue_evidence value known
  have sidecarNonreal : sidecar.value.im ≠ 0 := by
    intro zero
    exact nonreal ((congrArg Canonical.im same).symm.trans zero)
  unfold acquire State.start
  dsimp only
  rewrite [selected]
  unfold Provenance.infer
  dsimp only
  rewrite [dif_pos sidecarNonreal]
  exact ⟨rfl, rfl⟩

/-- A retained nonreal rational reading selects the exact word-preparation route. -/
theorem start_rational (input : Annotated) (value : Canonical) (known : input.rationalValue = some value)
    (nonreal : value.im ≠ 0) (word : SeparatedWords.Word) (delta : Rational) (positive : 0 < delta) :
    (acquire (State.start input) word delta positive).1.route = .rational :=
  (start_rational_properties input value known nonreal word delta positive).1

/-- Exact nonreal preparation leaves the original retained numerical state unchanged. -/
theorem start_rational_state (input : Annotated) (value : Canonical) (known : input.rationalValue = some value)
    (nonreal : value.im ≠ 0) (word : SeparatedWords.Word) (delta : Rational) (positive : 0 < delta) :
    (acquire (State.start input) word delta positive).1.next.state = (State.start input).state :=
  (start_rational_properties input value known nonreal word delta positive).2

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
    (separation : Separation tau)
    (word : Braid.Word 3) : SeparatedWords.Report tau word :=
  SeparatedWords.acquire separation word

end Purelib.Curves.Legendre.Acquisition.Words

end
