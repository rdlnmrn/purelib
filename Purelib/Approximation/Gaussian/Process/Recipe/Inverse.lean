module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Process.Recipe.Basic
public import Purelib.Approximation.Gaussian.Process.Recipe.Cursor
import Purelib.CCL.Progressive.IntegrationQueries
public import Purelib.Data.Gaussian.Constants
public import Purelib.Data.Gaussian.Power
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

open Purelib

open Purelib.Approximation.Gaussian.Process.Recipe

open Purelib.Approximation.Gaussian.Process

open Purelib.CCL.Progressive

open Purelib.Data.Gaussian

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite numerical controller and adaptive replay

All executable state below is finite chart syntax, rational bounds, natural
source indices and bit lists.  In particular, neither a `Process` nor a
source evaluator occurs in a returned state.  Each productive chunk records
its model reads, including the second read after a residual inverse chart
change.  Buffered bits do not perform a model query.

This is the numerical interpreter.  Its connection to the certified
transducer is established separately; successful replay of an invented log
does not certify global coherence of its replies.
-/

namespace Purelib.Approximation.Gaussian.Process.Recipe.Inverse

/-- Initial apartness preparation advances the original cursor before the inverse chart's own loop refinement. The
whole-ball lower bound is one eighth of the candidate lower bound, exactly as in `apartifyApart`. -/
def inverseCursor (control : IntegrationReplay.Control)
  (cursor : Approximation.Gaussian.Process.Recipe.Cursor) (lowerSq : Fraction.Rational) (count : Nat) :
      Approximation.Gaussian.Process.Recipe.Cursor :=
  let prepared := cursor.refined control (lowerSq / 12)
  let apartRecipe := Approximation.Gaussian.Process.Recipe.apart cursor.recipe lowerSq
  ⟨(apartRecipe.divided Data.Gaussian.Basic.Canonical.gamma⁻¹ (lowerSq / 8)).scaled control (Power.natPow
    Data.Gaussian.Basic.Canonical.gamma count)⁻¹,
    prepared.index⟩
end Purelib.Approximation.Gaussian.Process.Recipe.Inverse

end
