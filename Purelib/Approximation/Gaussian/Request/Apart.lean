module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
public import Purelib.Approximation.Gaussian.Request.Basic
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

namespace Purelib.Approximation.Gaussian.Request
section Name

namespace Basic.Name

set_option genInjectivity false in
/-- A fixed positive denominator lower bound, uniformly valid for every finite request. It is stronger than centre
non-vanishing and is precisely what makes division constructively continuous on the supplied domain. -/
structure Apart (name : Gaussian.Request.Basic.Name) where
  /-- The retained uniform rational lower bound on requested enclosure reading squared norms. -/ lowerSq :
    Fraction.Rational
  /-- The retained lower quadrance is strictly positive. -/ positive : 0 < lowerSq
  /-- Every reading in every positive-target requested ball meets the retained lower quadrance. -/ lower : ∀ (target :
    Fraction.Rational) (targetPositive : 0 < target)
      {value : Data.Gaussian.Basic.Canonical},
    (name.request target targetPositive).Contains value →
      lowerSq ≤ Data.Gaussian.Norm.Basic.normSq value

constructive_injectivity Apart

end Basic.Name

namespace Basic.Name.Apart.mk

end Basic.Name.Apart.mk

namespace Apart

/-- Specialize uniform request apartness to one displayed positive-target ball, retaining the same lower quadrance. -/
def atRequest {name : Gaussian.Request.Basic.Name} (apart
  : Approximation.Gaussian.Request.Basic.Name.Apart name)
    (target : Fraction.Rational) (targetPositive : 0 < target) :
    Enclosure.Ball.Apart
      (name.request target targetPositive) :=
  { lowerSq := apart.lowerSq
    positive := apart.positive
    lower := apart.lower target targetPositive }

/-- The centre of every requested ball meets the uniform apartness lower quadrance. -/
theorem center_lower {name : Gaussian.Request.Basic.Name}
  (apart : Approximation.Gaussian.Request.Basic.Name.Apart name)
    (target : Fraction.Rational) (targetPositive : 0 < target) :
    apart.lowerSq ≤ Data.Gaussian.Norm.Basic.normSq (name.request target targetPositive).center :=
  apart.lower target targetPositive
    (name.request target targetPositive).contains_center

end Apart
end Name

end Purelib.Approximation.Gaussian.Request

end
