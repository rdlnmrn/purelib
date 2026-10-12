module
import Purelib.Data.Rat.Fraction

public import Purelib.Data.Rat.Fraction.Order

open Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Finite convergence certificates

The usual monotone, Fatou, and dominated convergence theorems concern
completed limits.  This module retains their executable finite content:
displayed monotone chains have monotone rational integrals, displayed lower
envelopes satisfy the finite Fatou inequality, and an integrable rational
error envelope gives an explicit accuracy certificate.

No sequence, limit, supremum, extended value, or completed function space is
formed.
-/

namespace Purelib.Data.Rat

/-- Require each adjacent pair of a displayed rational list to be weakly increasing.

Empty and singleton lists satisfy the predicate. Longer lists retain the first weak
comparison and the same condition on the original tail. -/
def MonotoneCoordinateChain : List Rational → Prop
  | [] => True
  | [_] => True
  | first :: second :: remaining =>
      first ≤ second ∧ MonotoneCoordinateChain (second :: remaining)

namespace Content
end Content
namespace Content
end Content
namespace Content
namespace IntegralErrorBudget
end IntegralErrorBudget
namespace MonotoneIntegralBudget
end MonotoneIntegralBudget

end Content

end Purelib.Data.Rat

end
