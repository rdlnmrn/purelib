module
public import Purelib.Approximation.Gaussian.Acquisition.Positive.Search
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Acquisition.State.Schedule
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Rounding.Floor

import Purelib.Approximation.Gaussian.Acquisition.Positive.Obstruction
import Purelib.Approximation.Gaussian.Acquisition.Positive.Obstruction.Signed
import Purelib.Approximation.Gaussian.Acquisition.Provenance
import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Basic
public import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Canonical
import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Decision
import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.PositiveRunner
import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Schedule
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic
import Purelib.Control.FiniteRunner.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Positive

open Purelib.Approximation.Gaussian.Acquisition.Positive.Obstruction

open Purelib.Approximation.Gaussian.Acquisition.Signed

open Purelib.Approximation.Gaussian.Acquisition.Signed.Gap

open Purelib.Approximation.Gaussian.Acquisition.State

open Purelib.Approximation.Gaussian.Name

open Purelib.Data.Rat

open Purelib.Data.Rat.Rounding

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

namespace Purelib.Curves.Legendre.Acquisition.Gap

/-- Compute a finite signed inspection report from an unsigned imaginary gap.

The positive rational gap is retained at the starting state; the canonical schedule computes enough refinement to
distinguish its positive and negative outcomes. -/
def signedGap (tau : Coherent.CoherentNamed) (start :
    Approximation.Gaussian.Acquisition.State tau)
    (delta : Fraction.Rational) (positive : 0 < delta) (gap : Approximation.Gaussian.Acquisition.Signed.Gap tau start
        delta) :
    Gap.Canonical.CanonicalReport tau start delta :=
  Gap.Canonical.canonical tau start delta positive gap

/-- Computed precision and refinement budget, plus success of the original runner within one additional inspection or
all-budget exclusion at the retained negative endpoint. The sign is not an input. -/
theorem signedGap_spec (tau : Coherent.CoherentNamed) (start :
  Approximation.Gaussian.Acquisition.State tau)
    (delta : Fraction.Rational) (positive : 0 < delta) (gap : Approximation.Gaussian.Acquisition.Signed.Gap tau start
        delta) :
    let result := signedGap tau start delta positive gap
    result.final = Schedule.advanceN start result.count ∧
    result.final.ball.radiusSq < delta ^ 2 / 16 ∧
    result.count ≤ Nat.log2 (Floor.ceilNat (1 / (delta ^ 2 / 16))) + 2 ∧
    ((∃ certificate, Search.attempt tau start (result.count + 1) =
        .ready certificate) ∨
      (∀ fuel, Search.attempt tau result.final fuel =
        .exhausted (Schedule.advanceN result.final fuel))) := by
  let result := signedGap tau start delta positive gap
  refine ⟨result.final_eq, ?_, ?_, ?_⟩
  · rw [result.final_eq, result.count_eq]
    exact Schedule.canonical_accurate start delta positive
  · rw [result.count_eq]
    exact Schedule.canonicalCount_le start delta
  · cases result.outcome with
    | positive test =>
        let finished := result.finishPositive test
        exact .inl ⟨finished.val, finished.property⟩
    | negative certificate =>
        exact .inr (fun fuel => Nonpositive.attempt_exhausts
          result.final (Signed.nonpositive_of_negative
            positive certificate) fuel)
end Purelib.Curves.Legendre.Acquisition.Gap

end
