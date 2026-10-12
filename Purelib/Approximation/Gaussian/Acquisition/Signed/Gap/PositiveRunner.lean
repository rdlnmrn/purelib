module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Acquisition.Positive.Search
import Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Enclosure.Ball.Imaginary.Positive
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic

public import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Canonical
import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Decision
import Init.Core
import Purelib.Approximation.Gaussian.Acquisition.State.Schedule
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Control.FiniteRunner.Basic

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Positive

open Purelib.Approximation.Gaussian.Acquisition.Signed

open Purelib.Approximation.Gaussian.Enclosure.Ball.Imaginary

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Process.Imaginary

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Quantitative signed completeness from an unsigned candidate gap

A persistent rational gap removes the near-boundary alternative without
supplying the sign. Both direct requested precision and a coefficient-bounded
canonical refinement schedule construct signed evidence. The canonical
positive result supplies a budget for the original positivity `attempt`.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Canonical.CanonicalReport

namespace Gap
end Gap

/-- The positive canonical result supplies an actual budget for the original retryable positivity algorithm, which may
stop earlier than the endpoint. -/
def finishPositive {tau :
  Coherent.CoherentNamed} {start : Approximation.Gaussian.Acquisition.State tau} {delta : Fraction.Rational}
    (report : Gap.Canonical.CanonicalReport tau start delta) (test : Positive.PositiveTest report.final.ball) :
    { certificate : Positive.Basic.PositiveEnclosure tau //
      Search.attempt tau start (report.count + 1) = .ready certificate } := by
  apply Search.finishBy start report.count
  rw [← report.final_eq]
  exact test

/-- The computed canonical budget either certifies success of the original runner or supplies a persistent negative
certificate at its endpoint. -/
def finish {tau :
  Coherent.CoherentNamed} {start : Approximation.Gaussian.Acquisition.State tau} {delta : Fraction.Rational}
    (report : Gap.Canonical.CanonicalReport tau start delta) :
    Sum { certificate : Positive.Basic.PositiveEnclosure tau //
        Search.attempt tau start (report.count + 1) = .ready certificate }
      (Certificate.Negative tau report.final delta) :=
  match report.outcome with
  | .positive test => .inl (report.finishPositive test)
  | .negative certificate => .inr certificate
end Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Canonical.CanonicalReport

end
