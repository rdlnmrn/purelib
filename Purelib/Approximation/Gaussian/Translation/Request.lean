module

public import Purelib.Data.Rat.Fraction.Order.Basic

import Purelib.Data.Rat.Fraction
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Certified finite translations between refinement protocols

This module separates two operations which cannot constructively be conflated.
A direct observation map converts only the information already present in one
finite observation.  A finite realizer may first refine its source in response
to a positive rational request and records the finite work performed.

Candidate readings are Gaussian rationals.  Relations between readings remain
explicit because an affine enclosure, a projective CCL tail, and a redundant
digit cell need not use identical internal coordinates.
-/

namespace Purelib.Approximation.Gaussian.Translation

set_option genInjectivity false in
/-- A positive rational squared-precision request. -/
structure Request where
  /-- The retained rational squared-precision target. -/ targetSq : Fraction.Rational
  /-- The retained squared-precision target is strictly positive. -/ positive : 0 < targetSq

constructive_injectivity Request

namespace Request.mk

end Request.mk

end Purelib.Approximation.Gaussian.Translation

end
