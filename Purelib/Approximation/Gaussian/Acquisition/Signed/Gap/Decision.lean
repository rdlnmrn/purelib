module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate
import Purelib.Approximation.Gaussian.Acquisition.State
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Imaginary.Positive
public import Purelib.Approximation.Gaussian.Enclosure.Signed
import Purelib.Approximation.Gaussian.Name.Coherent

public import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Acquisition (State)

open Purelib

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Signed

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Enclosure.Ball.Imaginary

open Purelib.Approximation.Gaussian.Name

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

namespace Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Decision

namespace Gap
end Gap

set_option genInjectivity false in
/-- A signed result at the exact retained acquisition state.

The alternatives retain either positivity of its cached ball or a negative certificate for the original channel at the
displayed gap threshold. -/
inductive Outcome (tau : Coherent.CoherentNamed)
  (state : State tau) (delta : Fraction.Rational) : Type
  /-- Retain a positivity test indexed by the original cached acquisition ball. -/ | positive (test :
    Positive.PositiveTest state.ball)
  /-- Retain a negative certificate indexed by the original channel, state and gap threshold. -/ | negative (certificate
    : Certificate.Negative tau state delta)

constructive_injectivity Outcome

/-- Remove only the alternative refuted by independent finite gap evidence. -/
def certify {tau : Coherent.CoherentNamed} (state
  : State tau) (delta : Fraction.Rational) (positive : 0 < delta)
    (fine : state.ball.radiusSq < delta ^ 2 / 16) (gap : Approximation.Gaussian.Acquisition.Signed.Gap tau state delta)
    (decision : Signed.Decision state.ball delta) : Outcome tau
      state delta :=
  match decision with
  | .positive high _ => .positive (Signed.positive_test positive fine high)
  | .negative _ upper => .negative
      { upper := by
          intro value possible
          apply upper
          rw [state.ball_eq]
          exact tau.name.process.possible_inside possible }
  | .near bounds => False.elim (Approximation.Gaussian.Acquisition.Signed.Gap.incompatible_near gap
      { bounds := by
          intro value possible
          apply bounds
          rw [state.ball_eq]
          exact tau.name.process.possible_inside possible })

/-- Return whether the certified signed outcome carries the positive alternative. -/
def Outcome.isPositive {tau :
  Coherent.CoherentNamed} {state : State tau} {delta : Fraction.Rational} :
    Outcome tau state delta → Bool
  | .positive _ => true
  | .negative _ => false
end Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Decision

end
