module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Process.Recipe.Request
import Purelib.Approximation.Gaussian.Process.Recipe.Basic
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.Gaussian.Basic
import Init.Prelude
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation

open Purelib.CCL.Progressive

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

namespace Purelib.Approximation.Gaussian.Process.Recipe

set_option genInjectivity false in
/-- A finite numerical recipe and its current source-sample index.

The cursor retains executable chart syntax without a process callback or a selected completed value. -/
@[ext] structure Cursor where
  /-- The retained finite numerical chart recipe. -/ recipe : Recipe
  /-- The current index of the original source sample. -/ index : Nat
deriving DecidableEq

constructive_injectivity Cursor

namespace Cursor

/-- Refine the source index to the propagated numerical target while retaining the same recipe. -/
def refined (control : IntegrationReplay.Control)
  (cursor : Cursor) (target : Fraction.Rational) :
  Cursor :=
  ⟨cursor.recipe, cursor.recipe.refine control cursor.index target⟩

/-- Scale the retained numerical recipe while preserving the current source index. -/
def scaled (control : IntegrationReplay.Control)
  (cursor : Cursor) (factor : Data.Gaussian.Basic.Canonical) :
  Cursor :=
  ⟨cursor.recipe.scaled control factor, cursor.index⟩

/-- Translate the retained numerical recipe while preserving the current source index. -/
def translated (control : IntegrationReplay.Control)
  (cursor : Cursor) (shift : Data.Gaussian.Basic.Canonical) :
  Cursor :=
  ⟨cursor.recipe.translated control shift, cursor.index⟩

end Cursor

end Purelib.Approximation.Gaussian.Process.Recipe

end
