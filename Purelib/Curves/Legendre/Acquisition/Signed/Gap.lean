module
import Purelib.Topology.Knot.Braid.ThreeStrand.Word
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Acquisition.Positive.Enclosure
import Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Legendre.Acquisition.Automatic.Basic
import Purelib.Curves.Legendre.Acquisition.Automatic.Positive

public import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Decision
import Purelib.Curves.Legendre.FractionalWords.Periods
public import Purelib.Curves.Legendre.GuaranteedFold
import Init.Core
import Purelib.Approximation.Gaussian.Enclosure.Ball.Imaginary.Positive
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Positive

open Purelib.Approximation.Gaussian.Acquisition.Signed

open Purelib.Approximation.Gaussian.Acquisition.Signed.Gap

open Purelib.Approximation.Gaussian.Name

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Acquisition

open Purelib.Curves.Legendre.Acquisition.Automatic

open Purelib.Curves.Legendre.FractionalWords

open Purelib.Data.Rat

open Purelib.Topology.Knot.Braid

section
@[expose] public section

/-!
# Quantitative signed completeness from an unsigned candidate gap

A persistent rational gap removes the near-boundary alternative without
supplying the sign. Both direct requested precision and a coefficient-bounded
canonical refinement schedule construct signed evidence. The canonical
positive result supplies a budget for the original positivity `attempt`.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Decision.Outcome

/-- Construct the productive finite word output from a positive gap outcome, or retain the original negative
certificate. -/
def transport {tau :
  Coherent.CoherentNamed} {state : Approximation.Gaussian.Acquisition.State tau} {delta : Fraction.Rational}
    (outcome : Decision.Outcome tau state delta) (word : ThreeStrand.Word) :
    Sum (Automatic.Basic.Ready tau word)
      (Certificate.Negative tau state delta) :=
  match outcome with
  | .positive test => .inl
      (Positive.guaranteed (Enclosure.enclosure state test) word)
  | .negative certificate => .inr certificate

/-- Prepare the dependent finite word fold from a positive gap outcome, or retain the original negative certificate. -/
def fold {tau : Coherent.CoherentNamed}
  {state : Approximation.Gaussian.Acquisition.State tau} {delta : Fraction.Rational}
    (outcome : Decision.Outcome tau state delta) (word : ThreeStrand.Word) :
    Sum (GuaranteedFold.Prepared tau
        (Periods.periodBraidMatrices word))
      (Certificate.Negative tau state delta) :=
  match outcome with
  | .positive test => .inl
      (GuaranteedFold.prepareWord (Enclosure.enclosure state test) word)
  | .negative certificate => .inr certificate

end Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Decision.Outcome

end
