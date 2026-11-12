module
import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Signed
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Approximation.Gaussian.Equivalence

import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
public import Purelib.Curves.Legendre.Acquisition.Words
import Purelib.Curves.Legendre.FractionalWords.Periods
public import Purelib.Examples.Approximation.Gaussian.Acquisition.Signed.WorkedExamples
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Basic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Reversal
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Legendre.SeparatedWords
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.LinearAlgebra.Matrix.Integral.Word

section
@[expose] public section

/-!
Negative imaginary separation, word preparation and reversal.
-/

namespace Purelib.Examples.Curves.Legendre.Acquisition.Words.WorkedExamples

open Purelib.Approximation
open Purelib.Curves
open Purelib.Examples
open Purelib.Topology

open Purelib.Examples.Approximation.Gaussian.Acquisition.Signed.WorkedExamples (input negative_gap)
open Purelib.Approximation.Gaussian.Process.Imaginary (Separation)
open Purelib.Approximation.Gaussian.Acquisition.State (initial)

/-- The retained unsigned separation obtained from the negative unit gap. -/
def negativeSeparation : Separation
  (input (-1)) :=
  Separation.ofGap (initial (input
      (-1))) 1 (by decide)
    (negative_gap _)

/-- Acquire a separated braid word from the certified negative Legendre parameter. -/
def negativeWord (word : Knot.Braid.Word 3) :=
  Legendre.Acquisition.Words.separatedWord negativeSeparation word

/-- Reversing the acquired word restores the original negative input up to named equivalence.

The reversed period matrices act on the actual acquired output and its retained reversal preparation. -/
def negative_reversal (word : Knot.Braid.Word
  3) :
    Gaussian.Equivalence.NamedEquivalent
      (Gaussian.FractionalAction.Integral.Words.Fold.Basic.foldAction
        (negativeWord word).output
        (Legendre.FractionalWords.Periods.periodBraidMatrices word.inverse)
        (negativeWord word).prepareReversal.reverse).name
          Approximation.Gaussian.Acquisition.Signed.WorkedExamples.negative.name :=
  (negativeWord word).reversal

end Purelib.Examples.Curves.Legendre.Acquisition.Words.WorkedExamples

end
