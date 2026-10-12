module
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Division.Partial.Bounded
import Purelib.Approximation.Gaussian.Division.Partial.Ready
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Small
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.SmallOrApart
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Rational.Request.Sixth
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Approximation.Gaussian.Acquisition.Provenance
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Init.Core
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement (State)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Rational.Request

open Purelib.Data.Rat

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

namespace Purelib.Approximation.Gaussian.Division.Bounded.Interface

/-- The original inspection and either a cached ordinary quotient or both forms of smallness evidence. No additional
refinement is hidden in a failed branch, and the canonical retry index is preserved. -/
def BoundedResult (numerator denominator :
  Coherent.CoherentNamed) (start : State denominator)
    (threshold : Fraction.Rational) (positive : 0 < threshold) :=
  Sigma fun report : SmallOrApart.Report denominator start threshold positive =>
    Sum (Bounded.Quotient numerator denominator report.inspection.retained)
      { _small : Approximation.Gaussian.Name.Coherent.Refinement.Small denominator report.inspection.retained threshold
          //
        Residual.SmallBall report.inspection.ball threshold }

/-- Perform one prescribed denominator inspection and retain either its cached quotient or both smallness certificates.

The returned report keeps the same inspected state and canonical retry index in either branch. -/
def boundedDivision (numerator :
  Coherent.CoherentNamed) {denominator : Coherent.CoherentNamed}
    (start : State denominator) (threshold : Fraction.Rational)
        (positive : 0 < threshold) :
    BoundedResult numerator denominator start threshold positive :=
  let report := SmallOrApart.acquire start threshold positive
  ⟨report, match selected : report.outcome with
    | .inl evidence => .inl
        (Bounded.quotient numerator report.inspection.retained evidence)
    | .inr small => .inr ⟨small, report.small_ball small selected⟩⟩

/-- One-refinement provenance, requested precision, and operation-specific soundness in one statement. Successful
outputs carry the existing `Ready` certificate, hence its automatic/manual output-compatibility laws. -/
theorem BoundedResult.spec {numerator denominator :
  Coherent.CoherentNamed} {start : State denominator}
    {threshold : Fraction.Rational} {positive : 0 < threshold}
    (result : BoundedResult numerator denominator start threshold
      positive) :
    result.1.inspection.retained.source = denominator.name.process.refine start.source (threshold / 6)
        (Sixth.requestTarget_positive positive) ∧
    result.1.inspection.retained.nextIndex = start.nextIndex ∧
    result.1.inspection.ball.radiusSq < threshold / 6 ∧
    match result.2 with
    | .inl ready => ready.output = Ready.readyName numerator denominator
        result.1.inspection.retained ready.valid.evidence
    | .inr _small => Residual.SmallBall result.1.inspection.ball threshold ∧
        ∀ (future : Gaussian.Process.Based.BasedState denominator.name.process
          result.1.inspection.retained.source) {value : Data.Gaussian.Basic.Canonical},
          denominator.name.process.Possible future.source value →
            Data.Gaussian.Norm.Basic.normSq value < threshold := by
  refine ⟨result.1.inspection.source_eq, result.1.inspection.index_eq,
    result.1.inspection.accurate, ?_⟩
  cases result.2 with
  | inl ready => exact ready.valid.output_eq
  | inr small => exact ⟨small.property, fun future _value possible => small.val.at_future future possible⟩
end Purelib.Approximation.Gaussian.Division.Bounded.Interface

end
