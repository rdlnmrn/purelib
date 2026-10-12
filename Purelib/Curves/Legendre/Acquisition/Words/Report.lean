module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Approximation.Gaussian.Acquisition.Provenance
import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Basic
public import Purelib.Curves.Legendre.Acquisition.Words.State
import Purelib.Curves.Legendre.FractionalWords.Periods
import Purelib.Curves.Legendre.GuaranteedFold
public import Purelib.Curves.Legendre.SeparatedWords
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Init.Core
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Output
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Curves.Legendre.Acquisition.Automatic.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Acquisition.Signed

open Purelib.Approximation.Gaussian.Name

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Acquisition.Words

open Purelib.Data.Rat

section
public section

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
open _root_.Purelib.Approximation.Gaussian.Acquisition (Provenance)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open _root_.Purelib.Approximation.Gaussian.Process.Imaginary (Separation)
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic (Provider)

namespace Report

set_option genInjectivity false in
/-- A productive retained word report or an inconclusive near-boundary certificate. -/
inductive OutcomePayload.{u} (readyType : Type u) (nearType :
  Type) : Type u
  /-- Retain the productive word report with its original cached denominator preparations. -/ | ready (result :
    readyType)
  /-- Retain the inconclusive near-boundary certificate at the exact attempted state. -/ | near (certificate : nearType)

constructive_injectivity OutcomePayload

end Report

open Purelib.Curves.Legendre.Acquisition.Words.Report (OutcomePayload)

/-- The retained acquisition transition and its productive word report or near-boundary evidence.

The original input, word and requested radius index the result; its certificate belongs to the transition's actual next
state. -/
@[expose] def Report {tau : Coherent.CoherentNamed} (input :
  State.Input tau) (word : SeparatedWords.Word) (delta : Fraction.Rational) :=
  Sigma fun step : State.Step input => OutcomePayload (SeparatedWords.Report tau word)
    (Certificate.Near tau step.next.state delta)

namespace Report

/-- The report preserves provenance and the retained next index.

A productive result retains equivalence of its single and folded outputs; a near result bounds every possible value at
the retained state between the requested imaginary limits. -/
theorem spec {tau : Coherent.CoherentNamed} {input :
  State.Input tau} {word : SeparatedWords.Word} {delta : Fraction.Rational}
    (report : Report input word delta) :
    report.1.next.provenance = input.provenance ∧
    report.1.next.state.retained.nextIndex = input.state.retained.nextIndex ∧
    match report.2 with
    | .ready ready => Nonempty (Gaussian.Equivalence.NamedEquivalent ready.single.output.name ready.output.name)
    | .near _ => ∀ {value : Data.Gaussian.Basic.Canonical}, tau.name.process.Possible
      report.1.next.state.retained.source value →
        -delta < value.im ∧ value.im < delta := by
  refine ⟨report.1.provenance_eq, report.1.index_eq, ?_⟩
  cases report.2 with
  | ready ready => exact ⟨ready.equivalent_single⟩
  | near near => exact near.bounds

end Report

end Purelib.Curves.Legendre.Acquisition.Words

end
