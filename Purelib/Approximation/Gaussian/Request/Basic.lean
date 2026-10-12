module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

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

namespace Purelib.Approximation.Gaussian.Request.Basic

set_option genInjectivity false in
/-- A finite-request rational enclosure oracle with a uniform centre bound.

Each positive squared-error request returns a ball with strictly smaller squared radius; every returned centre satisfies
the same retained rational bound. -/
structure Name where
  /-- Return a rational ball for the displayed positive squared-error request. -/ request : (target : Fraction.Rational)
    → 0 < target → Approximation.Gaussian.Enclosure.Ball
  /-- Each returned ball's squared radius is strictly below its original requested target. -/ accurate : ∀ (target :
    Fraction.Rational) (positive : 0 < target),
    (request target positive).radiusSq < target
  /-- The retained uniform rational bound on requested centre squared norms. -/ centerBound : Fraction.Rational
  /-- The retained uniform centre bound is nonnegative. -/ centerBound_nonneg : 0 ≤ centerBound
  /-- Every requested ball's centre meets the retained uniform squared-norm bound. -/ center_bounded : ∀ (target :
    Fraction.Rational) (positive : 0 < target),
    Data.Gaussian.Norm.Basic.normSq (request target positive).center ≤ centerBound

constructive_injectivity Name

namespace Name

/-- Return the fixed Gaussian rational centre as a zero-radius enclosure at every request.

The supplied nonnegative centre bound and its original squared-norm certificate are retained unchanged. -/
def centerOnly (center : Data.Gaussian.Basic.Canonical) (bound
  : Fraction.Rational)
    (boundNonnegative : 0 ≤ bound) (bounded : Data.Gaussian.Norm.Basic.normSq center ≤ bound) :
      Approximation.Gaussian.Request.Basic.Name where
  request _ _ :=
    { center := center
      radiusSq := 0
      radiusSq_nonneg := le_rfl }
  accurate _ positive := positive
  centerBound := bound
  centerBound_nonneg := boundNonnegative
  center_bounded _ _ := bounded
end Name

end Purelib.Approximation.Gaussian.Request.Basic

end
