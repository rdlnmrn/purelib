module

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Finite divided differences and limit-free algebraic calculus

The derivative in this module is obtained by constructing a secant kernel
before putting its two displayed arguments equal.  No quotient by `x-y`,
limit, infinitesimal, or completed function graph is used.  Ordinary finite
polynomials, signed powers, and finite Laurent term lists are all evaluated by
structural recursion.
-/

namespace Purelib.Data.Int

/-! ## Signed powers and finite Laurent term lists -/

set_option genInjectivity false in
/-- A finite signed exponent syntax with a unique representation of zero.

The nonnegative constructor stores its natural exponent directly. The negative
constructor stores a predecessor and denotes `-(predecessor + 1)`, so every
negative exponent is strictly below zero. -/
inductive Exponent where
  /-- Represent a nonnegative exponent by its natural value. -/ | nonnegative : Nat → Exponent
  /-- Represent a strictly negative exponent as minus the successor of the stored natural. -/ | negative : Nat →
    Exponent
deriving DecidableEq

constructive_injectivity Exponent

namespace Exponent.nonnegative

end Exponent.nonnegative
namespace Exponent.negative

end Exponent.negative
end Purelib.Data.Int

end
