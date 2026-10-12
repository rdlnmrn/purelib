module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.Division.Partial.Run
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Data.Gaussian.Basic

import Purelib.Approximation.Gaussian.Acquisition.Provenance
import Purelib.Approximation.Gaussian.Division.Partial.ZeroObstruction
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Gap
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.GapDecision
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Zero
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Rational.Request.Sixth
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement (Gap State)

open Purelib

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Gap

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Evidence-directed division with reusable state

The dispatcher first reuses an exact decision, then tries inferred finite
provenance, then an optional proved candidate gap, and finally one bounded
numerical request. A small result is inconclusive, not zero. Gap exclusion
is explicitly scoped to the retained branch. Exact provenance concerns
operational identities and is never used as a pointwise candidate gap.

All routes return the retained state. Requested refinements preserve the
retry index and transport optional gap evidence. Exact decisions, including
negative ones, are cached for subsequent numerators and requests.
-/

namespace Purelib.Approximation.Gaussian.Division.Gap

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Acquisition (Provenance)
open Purelib.Approximation.Gaussian.Division (Prepared)
open Purelib.Approximation.Gaussian.Division.Prepared (Decision)
open Purelib.Approximation.Gaussian.Equivalence.Zero (ZeroIdentity)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

set_option genInjectivity false in
/-- A positive rational zero-or-gap certificate for the candidates at one exact retained channel state. -/
structure CandidateGap (channel : Coherent.CoherentNamed) (state :
  State channel) where
  /-- The retained rational squared-norm gap separating nonzero candidates from zero. -/ gap : Fraction.Rational
  /-- The retained candidate gap is strictly positive. -/ positive : 0 < gap
  /-- Every candidate at the indexed state satisfies the retained zero-or-gap law. -/
  certificate : Gap channel
    state gap

constructive_injectivity CandidateGap

/-- Transport the same candidate gap to a later state using the supplied candidate-persistence proof. -/
def CandidateGap.after {channel : Coherent.CoherentNamed} {first last
  : State channel}
    (gap : CandidateGap channel first)
    (persists : ∀ {value : Data.Gaussian.Basic.Canonical}, channel.name.process.Possible last.source value →
      channel.name.process.Possible first.source value) : CandidateGap channel last
        :=
  ⟨gap.gap, gap.positive, Gap.after gap.certificate persists⟩
end Purelib.Approximation.Gaussian.Division.Gap

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

namespace Purelib.Approximation.Gaussian.Division.Gap

/-- Perform a finite denominator decision using the supplied positive zero-or-gap certificate at the retained starting
state. -/
def gapDivision {denominator : Coherent.CoherentNamed} (start :
  State denominator)
    (gap : Fraction.Rational) (positive : 0 < gap) (certificate : Gap
        denominator start gap) :
    GapDecision.Report denominator start gap positive :=
  GapDecision.acquire start gap positive certificate

/-- Gap exclusion rules out every subsequent finite attempt on this retained branch; it is not a reinterpretation of
exhausted fuel. -/
theorem gapDivision_spec {denominator : Coherent.CoherentNamed}
  (start : State denominator)
    (gap : Fraction.Rational) (positive : 0 < gap) (certificate : Gap
        denominator start gap) :
    let result := gapDivision start gap positive certificate
    match result.2 with
    | .prepared evidence => 0 < evidence.lowerSq
    | .excluded _ => ∀ (numerator : Coherent.CoherentNamed) (fuel : Nat), ∃ final reachable,
        Run.attempt numerator denominator result.1.retained fuel =
          .exhausted final reachable := by
  dsimp only
  cases (gapDivision start gap positive certificate).2 with
  | prepared evidence => exact evidence.positive
  | excluded zero => exact fun numerator fuel =>
      ZeroObstruction.ZeroCandidates.attempt_exhausts numerator _ zero fuel
end Purelib.Approximation.Gaussian.Division.Gap

end
