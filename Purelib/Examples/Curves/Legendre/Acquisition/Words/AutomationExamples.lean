module
import Purelib.Examples.Approximation.Gaussian.Process.Imaginary.DelayedUnit
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Rat.Fraction

import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
public import Purelib.Curves.Legendre.Acquisition.Words
import Purelib.Curves.Legendre.Acquisition.Words.State
import Purelib.Curves.Legendre.SeparatedWords
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Examples.Approximation.Gaussian.Acquisition.Automation.WorkedExamples
public import Purelib.Examples.Approximation.Gaussian.Acquisition.Signed.WorkedExamples
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Acquisition.Expression.Compile
import Purelib.Approximation.Gaussian.Acquisition.Expression.Compilation
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

section
@[expose] public section

/-!
Legendre word acquisition from opaque and symbolic imaginary inputs.
-/

namespace Purelib.Examples.Curves.Legendre.Acquisition.Words.AutomationExamples

open Purelib.Examples.Approximation.Gaussian.Acquisition.Signed.WorkedExamples (input)
open Purelib.Examples.Approximation.Gaussian.Process.Imaginary

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

/-- Start word acquisition from the opaque signed Legendre input at the specified rational height. -/
def opaqueWord (height : Fraction.Rational)
  := Words.State.start
  (Approximation.Gaussian.Acquisition.Annotated.opaque (input height))

/-- The opaque input at height minus one is ready for every word at the unit margin. -/
theorem negative_word_ready (word :
  Legendre.SeparatedWords.Word) :
    ∃ ready, (Words.acquire (opaqueWord (-1))
      word 1 (by decide)).2 = .ready ready := ⟨_, rfl⟩
/-- The opaque input at height one is ready for every word at the unit margin. -/
theorem positive_word_ready (word :
  Legendre.SeparatedWords.Word) :
    ∃ ready, (Words.acquire (opaqueWord 1)
      word 1 (by decide)).2 = .ready ready := ⟨_, rfl⟩
/-- The zero-height opaque input returns a near result at the unit margin. -/
theorem zero_word_near (word :
  Legendre.SeparatedWords.Word) :
    ∃ near, (Words.acquire (opaqueWord 0) word
      1 (by decide)).2 = .near near := ⟨_, rfl⟩
/-- The opaque input at height one tenth returns a near result at the unit margin. -/
theorem tiny_word_near (word :
  Legendre.SeparatedWords.Word) :
    ∃ near, (Words.acquire (opaqueWord (1 /
      10)) word 1 (by decide)).2 = .near near := ⟨_, rfl⟩

/-- Start word acquisition with the exact rational parameter i/10. -/
def tinySymbolicWord :=
  Words.State.start (Annotated.rational ⟨0, 1 / 10⟩)

/-- Compile the exact arithmetic expression (1+i)-1 in the empty environment. -/
def symbolicWordExpression :=
  (Expr.add (.rational ⟨1, 1⟩) (.neg (.rational 1))).compile
  WorkedExamples.emptyEnvironment

/-- The compiled arithmetic expression selects the exact rational acquisition route. -/
theorem arithmetic_word_symbolic (word :
  Legendre.SeparatedWords.Word) :
    (Words.acquire (Words.State.start
      symbolicWordExpression) word 1 (by decide)).1.route =
      .rational := rfl

/-- The inferred exact route succeeds where the chosen numerical margin is
too coarse, without replacing the original arithmetic expression. -/
theorem tiny_word_symbolic (word :
  Legendre.SeparatedWords.Word) :
    (Words.acquire tinySymbolicWord word 1 (by
      decide)).1.route = .rational := rfl

/-- Acquire the empty word from the delayed opaque signed input at unit margin. -/
def delayedWord :=
  Words.acquire
  (Words.State.start (Approximation.Gaussian.Acquisition.Annotated.opaque
    DelayedUnit.name)) [] 1 (by decide)

/-- The original opaque commuted sum difference plus the exact imaginary unit. -/
def commutedImaginary (first second : CoherentNamed) : Annotated :=
  (Expr.add WorkedExamples.commutedSumDifference (.rational ⟨0, 1⟩)).compile
    (WorkedExamples.opaquePair first second)

/-- The retained opaque polynomial expression has the exact inferred imaginary-unit reading. -/
theorem commuted_imaginary_value (first second : CoherentNamed) :
    (commutedImaginary first second).rationalValue = some ⟨0, 1⟩ := by
  unfold commutedImaginary
  apply Expr.compile_inferred_value
  · rfl
  · unfold Expr.normalize Compiled.normalize
    dsimp only
    rewrite [Construction.normalize_form]
    dsimp only [Compiled.bindings]
    change (Sparse.add (Sparse.sub
      (Sparse.add (Sparse.atom (⟨0, by decide⟩ : Fin 4))
        (Sparse.atom (⟨1, by decide⟩ : Fin 4)))
      (Sparse.add (Sparse.atom (⟨1, by decide⟩ : Fin 4))
        (Sparse.atom (⟨0, by decide⟩ : Fin 4))))
      (Sparse.constant (⟨0, 1⟩ : Canonical))).terms =
       (Sparse.constant (⟨0, 1⟩ : Canonical)).terms
    decide +kernel

/-- Polynomial inference selects the rational word route for arbitrary original opaque inputs and any finite word. -/
theorem commuted_imaginary_word_rational (first second : CoherentNamed) (word : Legendre.SeparatedWords.Word) :
    (Words.acquire (Words.State.start (commutedImaginary first second))
      word 1 (by decide)).1.route = .rational := by
  have known := commuted_imaginary_value first second
  generalize input_eq : commutedImaginary first second = input at known ⊢
  exact Words.start_rational input ⟨0, 1⟩ known (by decide) word 1 (by decide)

/-- The original expanded unit identity minus one, followed by addition of the exact imaginary unit. -/
def expandedImaginary (first second : CoherentNamed) : Annotated :=
  (Expr.add (.sub WorkedExamples.expandedUnitExpression (.rational 1)) (.rational ⟨0, 1⟩)).compile
    (WorkedExamples.opaquePair first second)

/-- The expanded opaque input receives its exact inferred imaginary-unit reading. -/
theorem expanded_imaginary_value (first second : CoherentNamed) :
    (expandedImaginary first second).rationalValue = some ⟨0, 1⟩ := by
  unfold expandedImaginary
  apply Expr.compile_inferred_value
  · rfl
  · unfold Expr.normalize Compiled.normalize
    dsimp only
    rewrite [Construction.normalize_form]
    dsimp only [Compiled.bindings]
    rewrite [Expr.retain_add, dif_neg (by decide :
      Expr.rational (⟨0, 1⟩ : Canonical) ≠
        Expr.neg (Expr.sub WorkedExamples.expandedUnitExpression (.rational 1)))]
    rewrite [Expr.retain_sub, dif_neg (by decide :
      WorkedExamples.expandedUnitExpression ≠ Expr.rational 1)]
    unfold WorkedExamples.expandedUnitExpression
    simp only [Expr.retain_sub, Expr.retain_mul, Expr.retain_add,
      Expr.retain_atom, Expr.retain_rational, -eq_self, -iff_self]
    change (Sparse.add (Sparse.sub (Sparse.sub
      (Sparse.sub
        (Sparse.mul
          (Sparse.add (Sparse.atom (⟨0, by decide⟩ : Fin 3)) (Sparse.constant 1))
          (Sparse.add (Sparse.atom (⟨0, by decide⟩ : Fin 3)) (Sparse.constant 1)))
        (Sparse.mul (Sparse.atom (⟨0, by decide⟩ : Fin 3))
          (Sparse.atom (⟨0, by decide⟩ : Fin 3))))
      (Sparse.mul (Sparse.constant 2)
          (Sparse.atom (⟨0, by decide⟩ : Fin 3)))) (Sparse.constant 1))
      (Sparse.constant (⟨0, 1⟩ : Canonical))).terms =
       (Sparse.constant (⟨0, 1⟩ : Canonical)).terms
    decide +kernel

/-- Expanded polynomial inference selects the exact rational route for every original opaque input and finite word. -/
theorem expanded_imaginary_word_rational (first second : CoherentNamed) (word : Legendre.SeparatedWords.Word) :
    (Words.acquire (Words.State.start (expandedImaginary first second))
      word 1 (by decide)).1.route = .rational := by
  have known := expanded_imaginary_value first second
  generalize input_eq : expandedImaginary first second = input at known ⊢
  exact Words.start_rational input ⟨0, 1⟩ known (by decide) word 1 (by decide)

end Purelib.Examples.Curves.Legendre.Acquisition.Words.AutomationExamples

end
