module
import Purelib.Examples.Curves.Legendre.Acquisition.Words.AutomationExamples
import Purelib.Examples.Approximation.Gaussian.Process.Imaginary.DelayedUnit
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Rat.Fraction

import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
import Purelib.Curves.Legendre.Acquisition.Words
import Purelib.Curves.Legendre.Acquisition.Words.State
import Purelib.Curves.Legendre.SeparatedWords
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Examples.Approximation.Gaussian.Acquisition.Automation.WorkedExamples
import Purelib.Examples.Approximation.Gaussian.Acquisition.Signed.WorkedExamples
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
import Purelib.Polynomial.Multivariate.Sparse

open Purelib.Curves.Legendre.Acquisition

/-! Regression checks for the retained curves legendre acquisition words contracts. -/

namespace TestPurelib.Curves.Legendre.Acquisition.Words

open Purelib.Examples.Curves.Legendre.Acquisition.Words.AutomationExamples

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Basic (Expr Compiled Construction)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Examples.Approximation.Gaussian.Acquisition.Automation
open Purelib.Polynomial.Multivariate (Sparse)
open Purelib.Data.Gaussian.Basic (Canonical)

/-- Resuming a negative-height acquisition for another word uses the retained cache. -/
theorem word_resume_uses_cache (first
  second : Legendre.SeparatedWords.Word) :
    (Words.Report.resume (Words.acquire
      (opaqueWord (-1)) first 1 (by decide)) second 1 (by
      decide)).1.route = .cached := rfl

/-- Refining the margin to one tenth makes the retained small positive input ready. -/
theorem tiny_word_resume_finer_ready (word
  : Legendre.SeparatedWords.Word) :
    ∃ ready, (Words.Report.resume (Words.acquire
      (opaqueWord (1 / 10)) word 1 (by decide))
      word (1 / 10) (by decide)).2 = .ready ready := ⟨_, rfl⟩

/-- The delayed acquisition retains the refined source provider. -/
theorem delayed_word_refined :
  delayedWord.1.next.state.retained.source = true := rfl

/-- The retained delayed provider resumes at numerical index zero. -/
theorem delayed_word_index :
  delayedWord.1.next.state.retained.nextIndex = 0 := rfl

/-- Continuing from an existing separated-word report reuses its final provider through the cached route. -/
theorem continuation_uses_final_provider
  {tau : CoherentNamed} {first : Legendre.SeparatedWords.Word}
    (ready : Legendre.SeparatedWords.Report tau first) (next : Legendre.SeparatedWords.Word) :
    (Words.acquire (Words.continueFrom ready) next 1 (by decide)).1.route =
      .cached := rfl

/-- The inferred word input keeps the original arithmetic channel literally unchanged. -/
theorem commuted_imaginary_original_channel (first second : CoherentNamed) :
    (commutedImaginary first second).channel =
      (Expr.add WorkedExamples.commutedSumDifference (.rational ⟨0, 1⟩)).denote
        (WorkedExamples.opaquePair first second) :=
  Expr.compile_channel (WorkedExamples.opaquePair first second)
    (.add WorkedExamples.commutedSumDifference (.rational ⟨0, 1⟩))

/-- Expanded inference retains the entire original word-input evaluator. -/
theorem expanded_imaginary_original_channel (first second : CoherentNamed) :
    (expandedImaginary first second).channel =
      (Expr.add (.sub WorkedExamples.expandedUnitExpression (.rational 1)) (.rational ⟨0, 1⟩)).denote
        (WorkedExamples.opaquePair first second) :=
  Expr.compile_channel (WorkedExamples.opaquePair first second)
    (.add (.sub WorkedExamples.expandedUnitExpression (.rational 1)) (.rational ⟨0, 1⟩))

end TestPurelib.Curves.Legendre.Acquisition.Words
