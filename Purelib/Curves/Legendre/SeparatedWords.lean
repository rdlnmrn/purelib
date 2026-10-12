module
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate
public import Purelib.Approximation.Gaussian.Acquisition.Signed.Requested
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Closure
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Curves.Legendre.Acquisition.Automatic.Basic
import Purelib.Curves.Legendre.Acquisition.Automatic.Comparison
import Purelib.Curves.Legendre.Acquisition.Automatic.Fold
import Purelib.LinearAlgebra.Matrix.Inverse.Right
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Topology.Knot.Braid.Artin
import Purelib.Topology.Knot.Braid.Word.Basic

public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Separated
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Reversal
import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Basic
public import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Positive
public import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Signed
import Purelib.Curves.Legendre.FractionalWords.Periods
public import Purelib.Curves.Legendre.GuaranteedFold
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.PeriodMonodromy
import Purelib.LinearAlgebra.Matrix.Integral.Word
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Init.Core
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Enclosure.Signed
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Output
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Signed

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

open Purelib.Curves.Legendre.Acquisition

open Purelib.Curves.Legendre.Acquisition.Automatic.Comparison

open Purelib.Curves.Legendre.Acquisition.Automatic.Fold

open Purelib.Curves.Legendre.FractionalWords

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Matrix

open Purelib.LinearAlgebra.Matrix.Integral

open Purelib.LinearAlgebra.Matrix.Inverse

open Purelib.Riemann.Integration

open Purelib.Topology.Knot

open Purelib.Topology.Knot.Braid

section
@[expose] public section

/-!
# Automatically prepared words in either half-plane

The finite word fold consumes an unsigned separation provider. Its combined
denominator is reused by the single-matrix output instead of preparing it a
second time. Both outputs, the final provider, and reversal data remain
ordinary inputs to the established dual period-monodromy theorems.
-/

namespace Purelib.Curves.Legendre.SeparatedWords

open Purelib.Riemann.Integration.LegendreModularMonodromy (Gaussian fractionalLinear)

/-- A finite braid word on the original three strands. -/
abbrev Word := Braid.Word 3
/-- A Gaussian name with its retained coherent approximation realization. -/
abbrev CoherentNamed := Coherent.CoherentNamed
/-- Operational equivalence between two retained Gaussian names. -/
abbrev NamedEquivalent := Gaussian.Equivalence.NamedEquivalent

set_option genInjectivity false in
/-- Keep structure generation independent of the large evaluator indices, as in the existing automatic-transport
payloads. -/
structure ReportPayload.{u, v, w} (providerType : Type u) (foldedType :
  Type v) (singleType : Type w) where
  /-- The retained all-row denominator preparation provider for the original input. -/ provider : providerType
  /-- The cached dependent fold preparations and provider for its retained output. -/ folded : foldedType
  /-- The cached single-matrix output reusing the same combined denominator preparation. -/ single : singleType

constructive_injectivity ReportPayload

/-- The retained provider, dependent fold and single-matrix output for the same original input and braid word. -/
def Report (tau : CoherentNamed) (word : Word) :=
  ReportPayload (Preparation.Basic.Provider tau)
    (GuaranteedFold.Prepared tau (Periods.periodBraidMatrices word))
    (Automatic.Basic.Ready tau word)

/-- Reuse an already acquired all-row provider, including after an earlier word. The combined preparation is not
computed twice. -/
def acquireWithProvider {tau : CoherentNamed} (provider : Preparation.Basic.Provider tau)
  (word : Word) : Report tau word :=
  let folded := GuaranteedFold.prepare tau provider (Periods.periodBraidMatrices word)
    (GuaranteedFold.periodInverses word)
  let matrix := Word.matrixProduct (Periods.periodBraidMatrices word)
  let preparation := FoldPreparations.combined (Periods.periodBraidMatrices word) folded.1
  { provider := provider
    folded := folded
    single :=
      { matrix := matrix
        matrix_eq := Periods.matrixProduct_periodBraidMatrices word
        preparation := preparation
        output := LegendreModularMonodromy.fractionalLinear matrix tau preparation
        output_eq := rfl } }

/-- All local and combined preparations are generated from one unsigned candidate gap. No sign or per-word denominator
certificate is supplied. -/
def acquire {tau : CoherentNamed} (separation :
    Approximation.Gaussian.Process.Imaginary.Separation tau) (word :
  Word) : Report tau word :=
  acquireWithProvider (Separated.provider separation) word

/-- Acquisition with an existing provider retains that exact provider. -/
@[simp] theorem acquireWithProvider_reuses_provider {tau : CoherentNamed}
    (provider : Preparation.Basic.Provider tau) (word : Word) :
      (acquireWithProvider provider word).provider = provider := rfl

/-- The single-matrix output reuses the combined preparation from the retained dependent fold. -/
@[simp] theorem acquireWithProvider_reuses_combined {tau : CoherentNamed}
    (provider : Preparation.Basic.Provider tau) (word : Word) :
      (acquireWithProvider provider word).single.preparation =
      FoldPreparations.combined (Periods.periodBraidMatrices word) (acquireWithProvider
        provider word).folded.1 := rfl

/-- Acquisition from separation reuses the retained fold combined denominator preparation. -/
@[simp] theorem acquire_reuses_combined {tau : CoherentNamed} (separation :
  Approximation.Gaussian.Process.Imaginary.Separation tau)
    (word : Word) : (acquire separation
      word).single.preparation =
      FoldPreparations.combined (Periods.periodBraidMatrices word) (acquire separation
        word).folded.1 := rfl

namespace Report

/-- Read the productive output from the retained dependent fold preparations. -/
def output {tau : Curves.Legendre.SeparatedWords.CoherentNamed} {word : Curves.Legendre.SeparatedWords.Word} (report :
  Curves.Legendre.SeparatedWords.Report tau word) : CoherentNamed :=
  Fold.Basic.foldAction tau (Periods.periodBraidMatrices word) report.folded.1

/-- The retained single-matrix and dependent-fold outputs are operationally equivalent. -/
def equivalent_single {tau : Curves.Legendre.SeparatedWords.CoherentNamed} {word : Curves.Legendre.SeparatedWords.Word}
  (report : Curves.Legendre.SeparatedWords.Report tau word) :
    Curves.Legendre.SeparatedWords.NamedEquivalent report.single.output.name report.output.name :=
  Ready.equivalent_fold report.single report.folded.1

/-- Compatibility with existing positive, automatic, and manual routes. -/
def respects_ready {tau : Curves.Legendre.SeparatedWords.CoherentNamed} {word : Curves.Legendre.SeparatedWords.Word}
  (report : Curves.Legendre.SeparatedWords.Report tau word)
    (ready : Automatic.Basic.Ready tau word) :
    Curves.Legendre.SeparatedWords.NamedEquivalent report.output.name ready.output.name :=
  NamedEquivalent.trans
    (NamedEquivalent.symm report.equivalent_single)
    (Ready.respects report.single ready)

/-- Artin-equivalent original braid words produce operationally equivalent retained fold outputs. -/
def respects_braid {tau : Curves.Legendre.SeparatedWords.CoherentNamed} {firstWord secondWord :
  Curves.Legendre.SeparatedWords.Word}
    (first : Curves.Legendre.SeparatedWords.Report tau firstWord) (second : Curves.Legendre.SeparatedWords.Report tau
      secondWord)
    (relation : Artin.Equivalent firstWord secondWord) :
    Curves.Legendre.SeparatedWords.NamedEquivalent first.output.name second.output.name :=
  NamedEquivalent.trans
    (NamedEquivalent.symm first.equivalent_single)
    (NamedEquivalent.trans
      (Ready.respects_braid first.single second.single relation) second.equivalent_single)

/-- Continue from the cached forward output/provider. The original forward word is not rerun while constructing the
inverse leg. -/
def prepareReversal {tau : Curves.Legendre.SeparatedWords.CoherentNamed} {word : Curves.Legendre.SeparatedWords.Word}
  (report : Curves.Legendre.SeparatedWords.Report tau word) :
    Reversal.FoldReversalPreparations (Periods.periodBraidMatrices word) (Periods.periodBraidMatrices word.inverse) tau
      :=
  let first := Word.matrixProduct (Periods.periodBraidMatrices word)
  let second := Word.matrixProduct (Periods.periodBraidMatrices word.inverse)
  let firstInverse := GuaranteedFold.productInverse (Periods.periodBraidMatrices word)
    (GuaranteedFold.periodInverses word)
  let secondInverse := GuaranteedFold.productInverse
    (Periods.periodBraidMatrices word.inverse) (GuaranteedFold.periodInverses word.inverse)
  let inner := FoldPreparations.combined (Periods.periodBraidMatrices word) report.folded.1
  { forward := report.folded.1
    reverse := (GuaranteedFold.prepare report.output report.folded.2
      (Periods.periodBraidMatrices word.inverse)
      (GuaranteedFold.periodInverses word.inverse)).1
    composition :=
      { inner := inner
        outer := Closure.after report.provider first firstInverse inner second secondInverse
        combined := report.provider (Multiplication.mul second first)
          (Right.mulInverse secondInverse firstInverse) } }

/-- The prepared inverse word returns an output operationally equivalent to the original input.

The reverse leg uses the retained forward output and preparations, with the original forward word preserved. -/
def reversal {tau : Curves.Legendre.SeparatedWords.CoherentNamed} {word : Curves.Legendre.SeparatedWords.Word} (report :
  Curves.Legendre.SeparatedWords.Report tau word) :
    Curves.Legendre.SeparatedWords.NamedEquivalent
      (Fold.Basic.foldAction report.output (Periods.periodBraidMatrices word.inverse)
        report.prepareReversal.reverse).name
      tau.name := Periods.periodBraidWord_foldReversal word tau report.prepareReversal

/-- The arbitrary closed-path dual period equation needs separation, not an extra sign claim. All period data and path
hypotheses remain unchanged. -/
def transport {parameter : LegendreModularMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    (data : PeriodMonodromy.NormalizedData frame)
    (path : Paths.Path frame frame) (report : Curves.Legendre.SeparatedWords.Report data.ratio path.word) :
    Curves.Legendre.SeparatedWords.NamedEquivalent
      (CoherentNamed.mul (data.periods path 0) report.output).name
      (data.periods path 1).name := data.periodWord_productive_transport path report.folded.1

end Report

/-- Both signed outcomes support word evaluation. Only near-boundary evidence is passed back without a preparation, and
it remains inconclusive. -/
def acquireSigned {tau : CoherentNamed}
    {start : Approximation.Gaussian.Acquisition.State tau}
    {delta : Fraction.Rational} {positive : 0 < delta}
    (report : Requested.Report tau start delta positive) (word : Word) :
    Sum (Report tau word) (Certificate.Near tau report.retained delta) :=
  match report.2 with
  | .positive high _ => .inl (acquire (Separation.ofPositive (report.enclosure high))
    word)
  | .negative _ upper => .inl (acquire (Separation.ofNegative positive (report.negative
    upper)) word)
  | .near bounds => .inr (report.near bounds)

end Purelib.Curves.Legendre.SeparatedWords

end

section
@[expose] public section

/-!
# Automatic discovery of the initial positive enclosure

A cached rational ball passes when its centre is above the real axis and its
squared radius is below the squared half-height. The soundness proof gives a
positive imaginary lower bound for every point in that ball. Failed tests
perform one canonical finite refinement; bounded runs retain their exact
state on exhaustion and never infer a negative positivity verdict.
-/

end

section
@[expose] public section

/-!
# Bounded signed acquisition for Legendre input ratios

Requested-precision inspection always yields one of three mathematical
outcomes. The positive branch feeds the existing guaranteed word evaluators;
negative and near-boundary branches preserve their candidate evidence and
the exact state needed for subsequent work. A negative branch is not a
claim that all fractional transformations are undefined.
-/

end

section
@[expose] public section

/-!
# Automatic finite-word dual period outputs

The public result caches the exact word matrix, its denominator preparation,
and the productive output. A positive enclosure constructs it directly;
bounded acquisition returns either this same result or an exact resumable
state. The transport proof is shared by both construction routes.
-/

end
