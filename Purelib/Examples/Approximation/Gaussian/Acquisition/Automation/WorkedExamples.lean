module
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Examples.Approximation.Gaussian.Division.Bounded.WorkedExamples
public import Purelib.Examples.Approximation.Gaussian.Division.Gap.WorkedExamples
import Purelib.Examples.Approximation.Gaussian.Division.Partial.DelayedOne

import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Compile
public import Purelib.Approximation.Gaussian.Division.Acquisition.Dispatch
import Purelib.Approximation.Gaussian.Division.Acquisition.State
import Purelib.Riemann.RootContinuation.SquareRootSidecar
import Purelib.RootIsolation.SquareRoot.Observation.Annotated
import Purelib.Approximation.Gaussian.Acquisition.Provenance
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Division.Gap
import Purelib.Approximation.Gaussian.Division.Acquisition.Report
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Process.Basic

open Purelib.Approximation.Gaussian.Acquisition.Expression.Basic (Expr)

@[expose] public section

/-! # Automatic-route regressions, including symbolic and opaque inputs -/

namespace Purelib.Examples.Approximation.Gaussian.Acquisition.Automation.WorkedExamples

open Purelib.Approximation.Gaussian.Acquisition (Annotated)

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Examples.Approximation.Gaussian.Division.Bounded.WorkedExamples (oneInput tinyInput zeroInput)
open Purelib.Examples.Approximation.Gaussian.Division.Partial.DelayedOne (delayedOne)
open Purelib.Approximation.Gaussian.Acquisition
open Purelib.Approximation.Gaussian.Name
open Purelib.Examples.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Division
open Purelib.Examples.Approximation.Gaussian.Division
open Purelib.Data.Gaussian
open Purelib.Riemann.RootContinuation

/-- A singleton expression environment retaining the supplied opaque coherent name. -/
def atomEnvironment (input :
  CoherentNamed) : Fin 1 → Annotated := fun _ =>
      Annotated.opaque input

/-- Compile subtraction of the same retained opaque atom from itself.

The original arithmetic channel is kept while symbolic provenance records cancellation. -/
def cancellation (input :
  CoherentNamed) :=
  (Expr.sub (.atom 0) (.atom 0)).compile (atomEnvironment input)

/-- Compiling self-subtraction retains the exact rational value zero. -/
theorem cancellation_value (input :
  CoherentNamed) : (cancellation input).rationalValue = some 0 :=
  Expr.compile_cancel (atomEnvironment input) (.atom 0)

/-- Acquisition recognizes compiled self-subtraction as exact zero. -/
theorem cancellation_zero (input :
  CoherentNamed) :
    (Acquisition.Dispatch.acquire Bounded.WorkedExamples.oneInput (Acquisition.State.start
      (cancellation input)) 1 (by decide)).2.status = .zero := rfl

/-- Self-subtraction follows the symbolic acquisition route. -/
theorem cancellation_symbolic
  (input : CoherentNamed) :
    (Acquisition.Dispatch.acquire Bounded.WorkedExamples.oneInput (Acquisition.State.start
      (cancellation input)) 1 (by decide)).1.route = .symbolic := rfl

/-- Cancellation retains the original input-plus-negation arithmetic channel. -/
theorem
  cancellation_original_channel
  (input : CoherentNamed) :
    (cancellation input).channel =
      CoherentNamed.add input (CoherentNamed.neg input) := rfl

/-- The Gaussian rational number two. -/
def two : Basic.Canonical := ⟨2, 0⟩

/-- The expression multiplying the same sheet-zero square root of two by itself. -/
def squaredRoot :
  Expr 0 := .mul (.root two 0) (.root
  two 0)
/-- The empty annotated expression environment. -/
def emptyEnvironment : Fin 0 →
  Annotated := Fin.elim0

/-- The compiled repeated square root retains rational value two. -/
theorem squaredRoot_value :
  (squaredRoot.compile
  emptyEnvironment).rationalValue = some two
  := by
  unfold squaredRoot
  rewrite [Expr.compile, if_pos rfl]
  exact Annotated.root_square_value two 0

/-- The compiled expression subtracting two from its repeated square root product. -/
def rootEquation :=
  (Expr.sub squaredRoot (.rational
  two)).compile emptyEnvironment

/-- The compiled square-root equation retains rational value zero. -/
theorem rootEquation_value :
  rootEquation.rationalValue = some 0 := by
  change some ((SquareRootSidecar.isolated two 0).2.parameter +
    -two) = some 0
  rw [SquareRootSidecar.isolated_parameter]
  rfl

/-- Acquisition recognizes the retained square-root equation as exact zero. -/
theorem
  rootEquation_automatically_zero :
    (Acquisition.Dispatch.acquire Bounded.WorkedExamples.oneInput (Acquisition.State.start
      rootEquation) 1 (by decide)).2.status = .zero :=
  Acquisition.Dispatch.start_rational_zero Bounded.WorkedExamples.oneInput
    rootEquation 1 (by decide)
    rootEquation_value

/-- Adding zero and multiplying by one preserve a root's squared value.

For either retained square-root sheet, squaring the resulting annotated expression recovers the original parameter two.
-/
theorem neutral_root_provenance
  (sheet : Fin 2) :
    (((Annotated.rational 0).add (Annotated.root
      two sheet)).mul (Annotated.rational
          1)).square.rationalValue
      =
      some two := congrArg some (SquareRootSidecar.isolated_parameter
        two sheet)

/-- Distinct opaque atom indices retain no cancellation provenance.

The environment may return the same coherent name, but the expression keeps the original two syntactic atom identities.
-/
theorem
  distinct_opaque_atoms_not_identified
  (input : CoherentNamed) :
    ((Expr.sub (.atom (0 : Fin 2)) (.atom 1)).compile (fun _ =>
        Annotated.opaque
      input)).provenance = none := rfl

/-- Adding roots of two distinct parameters retains no symbolic provenance. -/
theorem unsupported_root_sum :
    ((Annotated.root two 0).add
        (Annotated.root
      ⟨3, 0⟩ 0)).provenance = none := rfl

/-- A retained exact zero times an opaque input has rational value zero. -/
theorem zero_times_opaque (input :
  CoherentNamed) :
    ((Annotated.rational 0).mul (Annotated.opaque
        input)).rationalValue = some 0 := rfl

/-- An opaque input times a retained exact zero has rational value zero. -/
theorem opaque_times_zero (input :
  CoherentNamed) :
    ((Annotated.opaque input).mul
        (Annotated.rational 0)).rationalValue = some 0 := rfl

/-- The fixed tiny denominator started with opaque provenance. -/
def opaqueTiny :=
  Acquisition.State.start (Annotated.opaque Bounded.WorkedExamples.tinyInput)
/-- The same tiny rational denominator started with exact symbolic provenance. -/
def symbolicTiny :=
  Acquisition.State.start (Annotated.rational Bounded.WorkedExamples.tinyValue)

/-- Numerical acquisition classifies the opaque tiny denominator as small. -/
theorem tiny_numerical_small :
  (Acquisition.Dispatch.acquire Bounded.WorkedExamples.oneInput opaqueTiny 1 (by
  decide)).2.status = .small := rfl
/-- Symbolic acquisition prepares the exact tiny denominator. -/
theorem tiny_symbolic_ready :
  (Acquisition.Dispatch.acquire Bounded.WorkedExamples.oneInput symbolicTiny 1 (by
  decide)).2.status = .ready := rfl

/-- Numerical acquisition of opaque zero returns a smallness outcome. -/
theorem opaque_zero_only_small :
    (Acquisition.Dispatch.acquire Bounded.WorkedExamples.oneInput (Acquisition.State.start
      (Annotated.opaque Bounded.WorkedExamples.zeroInput)) 1 (by decide)).2.status =
          .small := rfl

/-- The zero denominator retaining a certified positive unit gap. -/
def gapZero :
  Acquisition.State.Input zeroInput :=
  { Acquisition.State.start (Annotated.opaque Bounded.WorkedExamples.zeroInput) with
    gap := some ⟨1, by decide, Gap.WorkedExamples.zero_gap⟩ }

/-- Gap-based acquisition identifies the retained zero branch. -/
theorem gap_zero_is_branch_zero :
  (Acquisition.Dispatch.acquire Bounded.WorkedExamples.oneInput gapZero 1 (by
  decide)).2.status = .branchZero := rfl
/-- The certified zero-gap input uses the gap acquisition route. -/
theorem gap_zero_route :
  (Acquisition.Dispatch.acquire Bounded.WorkedExamples.oneInput gapZero 1 (by
  decide)).1.route = .gap := rfl

/-- The acquisition report for a delayed denominator representing one.

Keeps the original numerical refinement and ready quotient report at threshold one. -/
def delayedDivision :=
  Acquisition.Dispatch.acquire Bounded.WorkedExamples.oneInput (Acquisition.State.start
  (Annotated.opaque Partial.DelayedOne.delayedOne)) 1 (by decide)
/-- The delayed denominator acquisition returns readiness. -/
theorem delayed_ready :
  delayedDivision.2.status = .ready := rfl
/-- The acquisition report retains the delayed denominator's refined source. -/
theorem delayed_state_retained :
  delayedDivision.1.next.state.source = true := rfl
/-- Delayed acquisition preserves its original next-index counter. -/
theorem delayed_index_unchanged :
  delayedDivision.1.next.state.nextIndex = 0 := rfl

/-- Resuming the ready delayed report uses its cached acquisition route. -/
theorem delayed_resume_uses_cache :
  (Acquisition.Dispatch.Report.resume delayedDivision
  Bounded.WorkedExamples.tinyInput 1 (by decide)).1.route = .cached := rfl

/-- Resuming the tiny denominator with its smaller certified threshold prepares it.

Reuses the original numerical report and requests the exact positive squared-norm gap of the fixed tiny input. -/
theorem tiny_resume_finer_ready :
    (Acquisition.Dispatch.Report.resume (Acquisition.Dispatch.acquire Bounded.WorkedExamples.oneInput
      opaqueTiny 1 (by decide)) Bounded.WorkedExamples.oneInput
      Gap.WorkedExamples.tinyGap
      Gap.WorkedExamples.tinyGap_positive).2.status = .ready := rfl

/-- Resuming a symbolic cancellation report uses its cached zero result. -/
theorem zero_resume_uses_cache
  (input : CoherentNamed) :
    (Acquisition.Dispatch.Report.resume (Acquisition.Dispatch.acquire Bounded.WorkedExamples.oneInput
      (Acquisition.State.start (cancellation input)) 1 (by decide))
      Bounded.WorkedExamples.tinyInput 1 (by decide)).1.route = .cached := rfl

end Purelib.Examples.Approximation.Gaussian.Acquisition.Automation.WorkedExamples

end
