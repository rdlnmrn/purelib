module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Comparison
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
public import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.Gaussian.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Gaussian.Enclosure.Ball

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

namespace Purelib.Approximation.Gaussian.Process

set_option genInjectivity false in
/-- Bounds are retained at chart construction, not recomputed by traversing the whole expression on every downstream
refinement request. -/
inductive Recipe where
  /-- Read the original source ball without applying a numerical chart transformation. -/ | source
  /-- Translate the child ball by the retained Gaussian shift and cache the supplied center bound. -/ | translate (child
    : Recipe) (shift : Data.Gaussian.Basic.Canonical) (bound :
    Fraction.Rational)
  /-- Scale the child ball by the retained Gaussian factor and cache the supplied center bound. -/ | scale (child :
    Recipe) (factor : Data.Gaussian.Basic.Canonical) (bound :
    Fraction.Rational)
  /-- Retain candidate apartness data for the child without changing its numerical ball. -/ | apart (child :
    Recipe) (candidateLower : Fraction.Rational)
  /-- Divide the retained Gaussian numerator by the child using the supplied whole-ball lower bound and cached center
    bound. -/ | divide (child : Recipe) (numerator :
    Data.Gaussian.Basic.Canonical) (wholeBallLower bound : Fraction.Rational)
deriving DecidableEq

constructive_injectivity Recipe

namespace Recipe

/-- Read the cached center bound of the numerical recipe, using the original source control at leaves. -/
def centerBound (control : IntegrationReplay.Control)
  : Recipe → Fraction.Rational
  | .source => control.centerBound
  | .translate _ _ bound => bound
  | .scale _ _ bound => bound
  | .apart child _ => child.centerBound control
  | .divide _ _ _ bound => bound

/-- Construct a translated numerical recipe with the computed squared-norm center bound. -/
def translated (control : IntegrationReplay.Control)
  (child : Recipe) (shift : Data.Gaussian.Basic.Canonical) :
  Recipe :=
  .translate child shift (2 * (child.centerBound control + Comparison.normSqFromReduced shift))

/-- Construct a scaled numerical recipe with the computed squared-norm center bound. -/
def scaled (control : IntegrationReplay.Control)
  (child : Recipe) (factor : Data.Gaussian.Basic.Canonical) :
  Recipe :=
  .scale child factor (Comparison.normSqFromReduced factor * child.centerBound control)

/-- Construct a quotient numerical recipe retaining its whole-ball denominator bound and computed center bound. -/
def divided (child :
  Recipe) (numerator : Data.Gaussian.Basic.Canonical) (wholeBallLower :
  Fraction.Rational) : Recipe :=
  .divide child numerator wholeBallLower (Comparison.normSqFromReduced numerator / wholeBallLower)

/-- Apply the finite numerical recipe to one retained source-ball reply.

The transformation reads no model and supplies no independent semantic certificate; division consumes the recipe's
displayed lower bound. -/
def transform :
  Recipe → Data.BallData → Data.BallData
  | .source, ball => ball
  | .translate child shift _, ball => (child.transform ball).translate shift
  | .scale child factor _, ball => (child.transform ball).scale factor
  | .apart child _, ball => child.transform ball
  | .divide child numerator lower _, ball => (child.transform ball).divide numerator lower
end Recipe

end Purelib.Approximation.Gaussian.Process

end
