module
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Rat.Fraction

import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
public import Purelib.Curves.Legendre.Acquisition.Words
import Purelib.Curves.Legendre.Acquisition.Words.State
import Purelib.Curves.Legendre.SeparatedWords
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Examples.Approximation.Gaussian.Acquisition.Automation.WorkedExamples
public import Test.Curves.Legendre.SignedAcquisition
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Acquisition.Expression.Compile
import Purelib.Approximation.Gaussian.Acquisition.Provenance
import Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Basic
import Purelib.Curves.Legendre.Acquisition.Words.Report
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Knot.Braid.Basic

section
@[expose] public section

/-! # Automatic-route regressions, including symbolic and opaque inputs -/

namespace Purelib.Examples.Curves.Legendre.Acquisition.Words.AutomationExamples

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data.Rat
open Purelib.Examples

/-- Start word acquisition from the opaque signed Legendre input at the specified rational height. -/
def opaqueWord (height : Fraction.Rational)
  := Legendre.Acquisition.Words.State.start
  (Approximation.Gaussian.Acquisition.Annotated.opaque (Test.Curves.Legendre.SignedAcquisition.input height))

/-- The opaque input at height minus one is ready for every word at the unit margin. -/
theorem negative_word_ready (word :
  Legendre.SeparatedWords.Word) :
    ∃ ready, (Legendre.Acquisition.Words.acquire (opaqueWord (-1))
      word 1 (by decide)).2 = .ready ready := ⟨_, rfl⟩
/-- The opaque input at height one is ready for every word at the unit margin. -/
theorem positive_word_ready (word :
  Legendre.SeparatedWords.Word) :
    ∃ ready, (Legendre.Acquisition.Words.acquire (opaqueWord 1)
      word 1 (by decide)).2 = .ready ready := ⟨_, rfl⟩
/-- The zero-height opaque input returns a near result at the unit margin. -/
theorem zero_word_near (word :
  Legendre.SeparatedWords.Word) :
    ∃ near, (Legendre.Acquisition.Words.acquire (opaqueWord 0) word
      1 (by decide)).2 = .near near := ⟨_, rfl⟩
/-- The opaque input at height one tenth returns a near result at the unit margin. -/
theorem tiny_word_near (word :
  Legendre.SeparatedWords.Word) :
    ∃ near, (Legendre.Acquisition.Words.acquire (opaqueWord (1 /
      10)) word 1 (by decide)).2 = .near near := ⟨_, rfl⟩

/-- Start word acquisition with the exact rational parameter i/10. -/
def tinySymbolicWord :=
  Legendre.Acquisition.Words.State.start (Approximation.Gaussian.Acquisition.Annotated.rational ⟨0, 1 / 10⟩)

/-- Compile the exact arithmetic expression (1+i)-1 in the empty environment. -/
def symbolicWordExpression :=
  (Gaussian.Acquisition.Expression.Basic.Expr.add (.rational ⟨1, 1⟩) (.neg (.rational 1))).compile
  Approximation.Gaussian.Acquisition.Automation.WorkedExamples.emptyEnvironment

/-- The compiled arithmetic expression selects the exact rational acquisition route. -/
theorem arithmetic_word_symbolic (word :
  Legendre.SeparatedWords.Word) :
    (Legendre.Acquisition.Words.acquire (Legendre.Acquisition.Words.State.start
      symbolicWordExpression) word 1 (by decide)).1.route =
      .rational := rfl

/-- The inferred exact route succeeds where the chosen numerical margin is
too coarse, without replacing the original arithmetic expression. -/
theorem tiny_word_symbolic (word :
  Legendre.SeparatedWords.Word) :
    (Legendre.Acquisition.Words.acquire tinySymbolicWord word 1 (by
      decide)).1.route = .rational := rfl

/-- Resuming a negative-height acquisition for another word uses the retained cache. -/
theorem word_resume_uses_cache (first
  second : Legendre.SeparatedWords.Word) :
    (Legendre.Acquisition.Words.Report.resume (Legendre.Acquisition.Words.acquire
      (opaqueWord (-1)) first 1 (by decide)) second 1 (by
      decide)).1.route = .cached := rfl

/-- Refining the margin to one tenth makes the retained small positive input ready. -/
theorem tiny_word_resume_finer_ready (word
  : Legendre.SeparatedWords.Word) :
    ∃ ready, (Legendre.Acquisition.Words.Report.resume (Legendre.Acquisition.Words.acquire
      (opaqueWord (1 / 10)) word 1 (by decide))
      word (1 / 10) (by decide)).2 = .ready ready := ⟨_, rfl⟩

/-- Acquire the empty word from the delayed opaque signed input at unit margin. -/
def delayedWord :=
  Legendre.Acquisition.Words.acquire
  (Legendre.Acquisition.Words.State.start (Approximation.Gaussian.Acquisition.Annotated.opaque
    Test.Curves.Legendre.SignedAcquisition.delayed)) [] 1 (by decide)

/-- The delayed acquisition retains the refined source provider. -/
theorem delayed_word_refined :
  delayedWord.1.next.state.retained.source = true := rfl
/-- The retained delayed provider resumes at numerical index zero. -/
theorem delayed_word_index :
  delayedWord.1.next.state.retained.nextIndex = 0 := rfl

/-- Continuing from an existing separated-word report reuses its final provider through the cached route. -/
theorem continuation_uses_final_provider
  {tau : Gaussian.Name.Coherent.CoherentNamed} {first : Legendre.SeparatedWords.Word}
    (ready : Legendre.SeparatedWords.Report tau first) (next : Legendre.SeparatedWords.Word) :
    (Legendre.Acquisition.Words.acquire (Legendre.Acquisition.Words.continueFrom ready) next 1 (by decide)).1.route =
      .cached := rfl

end Purelib.Examples.Curves.Legendre.Acquisition.Words.AutomationExamples

end
