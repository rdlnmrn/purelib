module
import Purelib.Data.Gaussian.Norm.Comparison
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Process.Recipe.Basic
import Purelib.Approximation.Rational.Geometric.Search
public import Purelib.Approximation.Rational.Request.Common
import Purelib.CCL.Progressive.IntegrationQueries
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Approximation

open Purelib.Approximation.Rational.Geometric

open Purelib.Approximation.Rational.Request

open Purelib.CCL.Progressive

open Purelib.Data.Gaussian.Basic.Canonical.Norm

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite numerical chart expressions for transducer replay

The expression contains only displayed arithmetic data and cached center
bounds.  It has no model evaluator or hidden process callback.  Its source
accuracy request is pure finite arithmetic; observing its ball performs one
explicit model query and transforms that retained reply.

These expressions are the numerical part of the existing chart operations,
not independent semantic enclosure certificates.  `Represents` below ties a
generated expression to an actual certified process.  In particular, a raw
division expression alone does not establish apartness or accuracy.  The
controller bridge must derive that representation and reject invalid numeric
decisions; this module alone is not an arbitrary-prefix replay theorem.
-/

namespace Purelib.Approximation.Gaussian.Process.Recipe
section Recipe

/-- The exact target formulas used by the current process implementations. Neither source samples nor polynomial tables
are read to compute these. -/
def sourceTarget (control : IntegrationReplay.Control)
  : Recipe → Fraction.Rational → Fraction.Rational
  | .source, target => target
  | .translate child _ _, target => child.sourceTarget control (target / 4)
  | .scale child factor _, target => child.sourceTarget control
      (target / (target + (4 * (Comparison.normSqFromReduced factor + child.centerBound control) + 2)))
  | .apart child lower, target => child.sourceTarget control
      (Common.commonTarget target (lower / 12))
  | .divide child numerator lower _, target => child.sourceTarget control
      ((target * (lower * lower)) / (4 * (Comparison.normSqFromReduced numerator + child.centerBound control + 1)))

/-- Compute a finite source index satisfying the numerical recipe's propagated target, starting no earlier than the
supplied index. -/
def refine (control : IntegrationReplay.Control)
  (recipe : Recipe) (current : Nat) (target : Fraction.Rational) : Nat :=
  Search.firstQuarterBelow control.errorScale current (recipe.sourceTarget control target)

/-- Numerical recipe refinement never decreases the original source index. -/
theorem refine_ge (control :
  IntegrationReplay.Control) (recipe : Recipe) (current : Nat) (target :
  Fraction.Rational) :
    current ≤ recipe.refine control current target := Search.firstQuarterBelow_ge _ _ _
end Recipe

end Purelib.Approximation.Gaussian.Process.Recipe

end
