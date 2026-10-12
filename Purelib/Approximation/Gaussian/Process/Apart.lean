module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
public import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Progressive finite enclosures for constructive CCL arithmetic

An arithmetic input is not a completed complex value.  It is a finite request
procedure: for each positive rational squared-error target it returns one
rational ball meeting that target.  A uniform rational bound on the squared
norm of the returned centres is carried explicitly.  This is the extra finite
side information needed by multiplication.

Division deliberately asks for one further side certificate: a fixed positive
lower bound for every realization of every requested denominator ball.  The
definitions below construct arbitrarily accurate output balls for all four
elementary operations.  Their error budgets are closed rational expressions,
so there is no unbounded search and no completed limit in the interface.
-/

namespace Purelib.Approximation.Gaussian.Process
section Process

set_option genInjectivity false in
/-- Uniform apartness of every finite denominator enclosure. -/
structure Apart (process : Process)
  where
  /-- The retained uniform rational lower bound on all enclosure reading squared norms. -/ lowerSq : Fraction.Rational
  /-- The uniform lower quadrance is strictly positive. -/ positive : 0 < lowerSq
  /-- Every reading in every state's observed ball meets the same retained lower quadrance. -/ lower : ∀ (state :
    process.State) {value : Data.Gaussian.Basic.Canonical},
    (process.ball state).Contains value → lowerSq ≤ Data.Gaussian.Norm.Basic.normSq value

constructive_injectivity Apart

namespace Apart.mk

end Apart.mk

namespace Apart

/-- Specialize uniform process apartness to the ball at one displayed state.

The lower quadrance and its original positivity certificate are retained unchanged. -/
def atState {process : Process}
  (apart : Apart process)
    (state : process.State) :
    Enclosure.Ball.Apart (process.ball state) :=
  { lowerSq := apart.lowerSq
    positive := apart.positive
    lower := apart.lower state }

end Apart
end Process

end Purelib.Approximation.Gaussian.Process

end
