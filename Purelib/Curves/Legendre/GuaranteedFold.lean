module
public import Purelib.Curves.Legendre.Acquisition.Automatic.Fold
public import Purelib.Curves.Legendre.Acquisition.Automatic.Comparison
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Closure
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Positive
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic
public import Purelib.Curves.Legendre.Acquisition.Automatic.Positive
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Integral.Transpose
import Purelib.LinearAlgebra.Matrix.Inverse.Right
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Topology.Knot.Braid.Artin
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Generators
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Reversal
import Purelib.Curves.Legendre.FractionalWords.Periods
import Purelib.LinearAlgebra.Matrix.Integral.Word

import Purelib.Curves.Legendre.Paths
public import Purelib.Curves.Legendre.PeriodMonodromy
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Init.Core
import Init.Prelude
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Output
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Basic
import Purelib.Approximation.Gaussian.Name.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.FractionalAction.Integral

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Process.Imaginary

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Acquisition.Automatic

open Purelib.Curves.Legendre.Acquisition.Automatic.Comparison

open Purelib.Curves.Legendre.Acquisition.Automatic.Fold

open Purelib.Curves.Legendre.FractionalWords

open Purelib.LinearAlgebra.Matrix

open Purelib.LinearAlgebra.Matrix.Integral

open Purelib.LinearAlgebra.Matrix.Inverse

open Purelib.Riemann.Integration

open Purelib.Topology.Knot

open Purelib.Topology.Knot.Braid

open Purelib.Topology.Knot.Braid.ThreeStrand.Integral

@[expose] public section

/-!
# Guaranteed preparation of the entire dual word

The original positive enclosure constructs a provider. Fractional composition
preserves that provider, so a finite recursion constructs every local and
combined preparation at the exact intermediate output where it is needed.
-/

namespace Purelib.Curves.Legendre.GuaranteedFold

open Purelib.Riemann.Integration.LegendreFractionalWords
open Purelib.Riemann.Integration.LegendreModularMonodromy

/-- A Gaussian name retaining its coherent sample realization. -/
abbrev CoherentNamed := Coherent.CoherentNamed
/-- A finite two-dimensional integral matrix for the original period action. -/
abbrev IntegralMatrix := LinearAlgebra.Matrix.Basic.IntegralMatrix
/-- Exact Gaussian rational curve parameters. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- Operational equivalence of retained Gaussian names. -/
abbrev NamedEquivalent := Gaussian.Equivalence.NamedEquivalent

/-- An ordered retained right-inverse certificate for each matrix in the original finite list. -/
def Inverses : List Curves.Legendre.GuaranteedFold.IntegralMatrix → Type
  | [] => Unit
  | matrix :: remaining => Right.RightInverse matrix × Purelib.Curves.Legendre.GuaranteedFold.Inverses remaining

/-- Concatenate the retained inverse certificates in the same order as the original matrix lists. -/
def appendInverses (first second : List Curves.Legendre.GuaranteedFold.IntegralMatrix)
    (left : Curves.Legendre.GuaranteedFold.Inverses first) (right : Curves.Legendre.GuaranteedFold.Inverses second) :
      Curves.Legendre.GuaranteedFold.Inverses (first ++ second) :=
  match first with
  | [] => right
  | _ :: remaining => ⟨left.1, Purelib.Curves.Legendre.GuaranteedFold.appendInverses remaining second left.2 right⟩

/-- Compose the retained right inverses for the original ordered matrix product. -/
def productInverse : (matrices : List Curves.Legendre.GuaranteedFold.IntegralMatrix) →
    Curves.Legendre.GuaranteedFold.Inverses matrices → Right.RightInverse (Word.matrixProduct matrices)
  | [], _ => Right.identityInverse
  | _ :: remaining, ⟨head, tail⟩ => Right.mulInverse (Purelib.Curves.Legendre.GuaranteedFold.productInverse remaining
    tail) head

/-- Transpose the reversed generator matrix to obtain a right inverse of the original dual generator. -/
def dualGeneratorInverse (generator : Braid.Generator 3) :
    Right.RightInverse (Transpose.transpose
      (Generators.generatorMatrix generator)) where
  inverse := Transpose.transpose
    (Generators.generatorMatrix generator.reverse)
  identity := by
    rw [← Transpose.transpose_mul,
      (Generators.generator_reverse_matrix generator).1,
      Transpose.transpose_identity]

/-- Construct the inverse spine for the exact reversed transposed generator list of the original braid word. -/
def periodInverses : (word : Braid.Word 3) →
    Curves.Legendre.GuaranteedFold.Inverses (Periods.periodBraidMatrices word)
  | [] => ()
  | generator :: remaining =>
      Curves.Legendre.GuaranteedFold.appendInverses (Periods.periodBraidMatrices remaining)
        [Transpose.transpose
          (Generators.generatorMatrix generator)]
        (Purelib.Curves.Legendre.GuaranteedFold.periodInverses remaining) ⟨dualGeneratorInverse generator, ()⟩

/-- Retain both the complete preparation and the provider for the actual final output, allowing further words to
continue without new positivity. -/
def Prepared (tau : Curves.Legendre.GuaranteedFold.CoherentNamed) (matrices : List
  Curves.Legendre.GuaranteedFold.IntegralMatrix) :=
  Sigma fun preparations : Fold.Basic.FoldPreparations tau matrices =>
    Preparation.Basic.Provider (Fold.Basic.foldAction tau matrices preparations)

/-- A structurally recursive, search-free construction of the complete stepwise preparation. All local and combined
denominators are generated. -/
def prepare (tau : Curves.Legendre.GuaranteedFold.CoherentNamed) (provider : Preparation.Basic.Provider tau) :
    (matrices : List Curves.Legendre.GuaranteedFold.IntegralMatrix) → Curves.Legendre.GuaranteedFold.Inverses matrices →
      Curves.Legendre.GuaranteedFold.Prepared tau matrices
  | [], _ => ⟨provider Multiplication.identity Right.identityInverse, provider⟩
  | matrix :: remaining, inverses =>
      let head := provider matrix inverses.1
      let tail := Purelib.Curves.Legendre.GuaranteedFold.prepare (LegendreModularMonodromy.fractionalLinear matrix tau
        head)
        (Closure.after provider matrix inverses.1 head) remaining inverses.2
      let combined := provider (Word.matrixProduct (matrix :: remaining))
        (Curves.Legendre.GuaranteedFold.productInverse (matrix :: remaining) inverses)
      ⟨⟨head, tail.1, combined⟩, tail.2⟩

/-- Every finite dual word is fully prepared from one initial positive enclosure. The caller supplies no intermediate
denominator certificates. -/
def prepareWord {tau : Curves.Legendre.GuaranteedFold.CoherentNamed}
    (positive : Positive.Basic.PositiveEnclosure tau)
    (word : Braid.Word 3) : Curves.Legendre.GuaranteedFold.Prepared tau (Periods.periodBraidMatrices word) :=
  Curves.Legendre.GuaranteedFold.prepare tau (Positive.ofPositiveEnclosure positive) (Periods.periodBraidMatrices word)
    (Curves.Legendre.GuaranteedFold.periodInverses word)

/-- The default single-matrix evaluator and the guaranteed stepwise evaluator produce operationally equivalent outputs
without supplied preparations. -/
def equivalent_single {tau : Curves.Legendre.GuaranteedFold.CoherentNamed}
    (positive : Positive.Basic.PositiveEnclosure tau)
    (word : Braid.Word 3) :
    Curves.Legendre.GuaranteedFold.NamedEquivalent
      (Positive.guaranteed positive word).output.name
      (Fold.Basic.foldAction tau (Periods.periodBraidMatrices word) (Curves.Legendre.GuaranteedFold.prepareWord positive
        word).1).name :=
  Ready.equivalent_fold
    (Positive.guaranteed positive word)
    (Curves.Legendre.GuaranteedFold.prepareWord positive word).1

/-- Equal finite period matrices give equivalent automatically prepared stepwise outputs, independently of the initial
positivity witnesses. -/
def equivalent_words {tau : Curves.Legendre.GuaranteedFold.CoherentNamed}
    (firstPositive secondPositive :
      Positive.Basic.PositiveEnclosure tau)
    (firstWord secondWord : Braid.Word 3)
    (equal : Dual.periodMatrix firstWord =
      Dual.periodMatrix secondWord) :
    Curves.Legendre.GuaranteedFold.NamedEquivalent
      (Fold.Basic.foldAction tau (Periods.periodBraidMatrices firstWord) (Curves.Legendre.GuaranteedFold.prepareWord
        firstPositive firstWord).1).name
      (Fold.Basic.foldAction tau (Periods.periodBraidMatrices secondWord) (Curves.Legendre.GuaranteedFold.prepareWord
        secondPositive secondWord).1).name :=
  NamedEquivalent.trans
    (NamedEquivalent.symm
      (Curves.Legendre.GuaranteedFold.equivalent_single firstPositive firstWord))
    (NamedEquivalent.trans
      (Ready.respects_matrix
        (Positive.guaranteed firstPositive firstWord)
        (Positive.guaranteed secondPositive secondWord) equal)
      (Curves.Legendre.GuaranteedFold.equivalent_single secondPositive secondWord))

/-- The fully prepared stepwise computations respect finite Artin equivalence and may use independently discovered
initial positive enclosures. -/
def equivalent_braids {tau : Curves.Legendre.GuaranteedFold.CoherentNamed}
    (firstPositive secondPositive :
      Positive.Basic.PositiveEnclosure tau)
    (firstWord secondWord : Braid.Word 3)
    (relation : Artin.Equivalent firstWord secondWord) :
    Curves.Legendre.GuaranteedFold.NamedEquivalent
      (Fold.Basic.foldAction tau (Periods.periodBraidMatrices firstWord) (Curves.Legendre.GuaranteedFold.prepareWord
        firstPositive firstWord).1).name
      (Fold.Basic.foldAction tau (Periods.periodBraidMatrices secondWord) (Curves.Legendre.GuaranteedFold.prepareWord
        secondPositive secondWord).1).name :=
  Curves.Legendre.GuaranteedFold.equivalent_words firstPositive secondPositive firstWord secondWord
    (Dual.equivalent_periodMatrix_eq relation)

/-- Prepare both executions and the finite composition comparison, reusing the provider at the actual forward output for
the reverse execution. -/
def prepareReversal {tau : Curves.Legendre.GuaranteedFold.CoherentNamed}
    (positive : Positive.Basic.PositiveEnclosure tau)
    (word : Braid.Word 3) :
    Reversal.FoldReversalPreparations (Periods.periodBraidMatrices word)
      (Periods.periodBraidMatrices word.inverse) tau :=
  let provider := Positive.ofPositiveEnclosure positive
  let forward := Curves.Legendre.GuaranteedFold.prepareWord positive word
  let first := Word.matrixProduct (Periods.periodBraidMatrices word)
  let second := Word.matrixProduct (Periods.periodBraidMatrices word.inverse)
  let firstInverse := Curves.Legendre.GuaranteedFold.productInverse (Periods.periodBraidMatrices word)
    (Curves.Legendre.GuaranteedFold.periodInverses word)
  let secondInverse := Curves.Legendre.GuaranteedFold.productInverse (Periods.periodBraidMatrices word.inverse)
    (Curves.Legendre.GuaranteedFold.periodInverses word.inverse)
  let inner := FoldPreparations.combined (Periods.periodBraidMatrices word) forward.1
  { forward := forward.1
    reverse := (Curves.Legendre.GuaranteedFold.prepare (Fold.Basic.foldAction tau (Periods.periodBraidMatrices word)
      forward.1)
      forward.2 (Periods.periodBraidMatrices word.inverse) (Curves.Legendre.GuaranteedFold.periodInverses
        word.inverse)).1
    composition :=
      { inner := inner
        outer := Closure.after provider first firstInverse inner second secondInverse
        combined := provider (Multiplication.mul second first)
          (Right.mulInverse secondInverse firstInverse) } }

/-- A fully automatically prepared word followed by its inverse returns the original ratio. The same initial positivity
enclosure prepares both legs. -/
def reversal {tau : Curves.Legendre.GuaranteedFold.CoherentNamed}
    (positive : Positive.Basic.PositiveEnclosure tau)
    (word : Braid.Word 3) :
    Curves.Legendre.GuaranteedFold.NamedEquivalent
      (Fold.Basic.foldAction
        (Fold.Basic.foldAction tau (Periods.periodBraidMatrices word) (Curves.Legendre.GuaranteedFold.prepareReversal
          positive word).forward)
        (Periods.periodBraidMatrices word.inverse) (Curves.Legendre.GuaranteedFold.prepareReversal positive
          word).reverse).name
      tau.name :=
  Periods.periodBraidWord_foldReversal word tau (Curves.Legendre.GuaranteedFold.prepareReversal positive word)

/-- The fully automatic stepwise output satisfies the arbitrary closed-path dual period theorem. -/
def transport {parameter : Curves.Legendre.GuaranteedFold.Gaussian}
    {frame : Paths.Frame parameter}
    (data : PeriodMonodromy.NormalizedData frame)
    (positive : Positive.Basic.PositiveEnclosure data.ratio)
    (path : Paths.Path frame frame) :
    Curves.Legendre.GuaranteedFold.NamedEquivalent
      (CoherentNamed.mul (data.periods path 0)
        (Fold.Basic.foldAction data.ratio (Periods.periodBraidMatrices path.word)
          (Curves.Legendre.GuaranteedFold.prepareWord positive path.word).1)).name
      (data.periods path 1).name :=
  data.periodWord_productive_transport path (Curves.Legendre.GuaranteedFold.prepareWord positive path.word).1

end Purelib.Curves.Legendre.GuaranteedFold
