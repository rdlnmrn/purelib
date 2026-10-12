module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Affine.Integral.Bounds
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Topology.Knot.Braid.Artin

import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
public import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Absolute
import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Basic
import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Signed
import Purelib.Curves.Legendre.FractionalWords.Periods
public import Purelib.Curves.Legendre.SeparatedWords
import Purelib.Data.Rat.Fraction.Compatibility
import Test.Curves.Legendre.SignedAcquisition
public import Test.Curves.Legendre.SignedGap
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Lattice
import Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate
import Purelib.Approximation.Gaussian.Acquisition.Signed.Requested
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Output
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Basic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Reversal
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Curves.Legendre.Acquisition.Automatic.Basic
import Purelib.Curves.Legendre.GuaranteedFold
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Integral.Word
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual
import Purelib.Topology.Knot.Braid.Word.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words

open Purelib.Approximation.Gaussian.Process.Imaginary

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.FractionalWords

open Purelib.Data.Gaussian.Affine

open Purelib.Data.Rat

open Purelib.Topology.Knot.Braid

section
@[expose] public section

/-! # Unsigned word preparation, including the negative acquisition path -/

namespace Test.Curves.Legendre.Separated

open Purelib.Curves.Legendre.SeparatedWords (Word)
open Test.Curves.Legendre.SignedAcquisition (input report)
open Purelib.Approximation.Gaussian.Acquisition.State (initial)

/-- The retained unsigned separation obtained from the negative unit gap. -/
def negativeSeparation : Approximation.Gaussian.Process.Imaginary.Separation
  (Test.Curves.Legendre.SignedAcquisition.input (-1)) :=
  Approximation.Gaussian.Process.Imaginary.Separation.ofGap (State.initial (Test.Curves.Legendre.SignedAcquisition.input
      (-1))) 1 (by decide)
    (Test.Curves.Legendre.SignedGap.negative_gap _)

/-- Prepare the supplied finite word using the retained negative-input separation. -/
def negativeWord (word : SeparatedWords.Word) := SeparatedWords.acquire
  negativeSeparation word

/-- Negative signed acquisition prepares the supplied finite word. -/
theorem negative_acquisition_prepares (word : SeparatedWords.Word) :
    ∃ prepared, SeparatedWords.acquireSigned (Test.Curves.Legendre.SignedAcquisition.report (-1)) word = .inl prepared
      :=
  ⟨_, rfl⟩

/-- Positive signed acquisition prepares the supplied finite word. -/
theorem positive_acquisition_prepares (word : SeparatedWords.Word) :
    ∃ prepared, SeparatedWords.acquireSigned (Test.Curves.Legendre.SignedAcquisition.report 1) word = .inl prepared :=
  ⟨_, rfl⟩

/-- Zero signed acquisition retains its near-boundary evidence. -/
theorem zero_still_near (word : SeparatedWords.Word) :
    ∃ near, SeparatedWords.acquireSigned (Test.Curves.Legendre.SignedAcquisition.report 0) word = .inr near := ⟨_, rfl⟩

/-- The folded negative-input output is equivalent to its single-action output. -/
def negative_outputs_agree (word : SeparatedWords.Word) :
  Gaussian.Equivalence.NamedEquivalent
    (negativeWord word).single.output.name (negativeWord
      word).output.name :=
  (negativeWord word).equivalent_single

/-- Applying the prepared inverse word recovers the original negative input. -/
def negative_reversal (word : SeparatedWords.Word) :
  Gaussian.Equivalence.NamedEquivalent
    (Fold.Basic.foldAction (negativeWord word).output
      (Periods.periodBraidMatrices word.inverse)
      (negativeWord word).prepareReversal.reverse).name
        (Test.Curves.Legendre.SignedAcquisition.input (-1)).name :=
  (negativeWord word).reversal

/-- Equivalent braid words give equivalent prepared negative-input outputs. -/
def negative_braid_invariance (first second : SeparatedWords.Word)
    (relation : Artin.Equivalent first second) :
    Gaussian.Equivalence.NamedEquivalent
      (negativeWord first).output.name (negativeWord
        second).output.name :=
  (negativeWord first).respects_braid (negativeWord
    second) relation

/-- The unsigned separation certified directly by the exact negative imaginary part. -/
def absoluteNegative : Approximation.Gaussian.Process.Imaginary.Separation
  (Test.Curves.Legendre.SignedAcquisition.input (-1)) :=
  Approximation.Gaussian.Process.Imaginary.Separation.ofAbsolute (Test.Curves.Legendre.SignedAcquisition.input
      (-1)).name.state 1 (by decide) (by
    intro value possible
    change value = (⟨0, -1⟩ : Data.Gaussian.Basic.Canonical) at possible
    subst value
    decide)

/-- The constant row with coefficient negative two has squared lower bound four. -/
theorem constant_row_bound :
    Integral.Bounds.rowLower (-2) 0 absoluteNegative.gap = 4 := by decide

/-- The row with negative imaginary coefficient three has squared lower bound nine. -/
theorem negative_coefficient_bound :
    Integral.Bounds.rowLower 0 (-3) absoluteNegative.gap = 9 := by decide

/-- The exact zero input admits no positive separation certificate. -/
theorem zero_not_separated (certificate :
    Approximation.Gaussian.Process.Imaginary.Separation
  (Test.Curves.Legendre.SignedAcquisition.input 0)) : False := by
  have lower := certificate.squared_lower (value := 0) rfl
  change certificate.gap ^ 2 ≤ (0 : Fraction.Rational) ^ 2 at lower
  rw [show (0 : Fraction.Rational) ^ 2 = 0 by decide] at lower
  exact (not_lt_of_ge lower) (Fraction.Order.Arithmetic.pow_pos_direct certificate.positive 2)

end Test.Curves.Legendre.Separated

end
