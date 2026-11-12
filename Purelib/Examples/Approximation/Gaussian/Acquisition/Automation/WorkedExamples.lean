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
import Purelib.Polynomial.Multivariate.Sparse

open Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

@[expose] public section

/-!
Symbolic and opaque acquisition through retained arithmetic expressions.
-/

namespace Purelib.Examples.Approximation.Gaussian.Acquisition.Automation.WorkedExamples

open Purelib.Approximation.Gaussian.Division.Acquisition

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
open Purelib.Polynomial.Multivariate (Sparse)

/-- A singleton expression environment retaining the supplied opaque coherent name. -/
def atomEnvironment (input :
  CoherentNamed) : Fin 1 → Annotated := fun _ =>
      Annotated.opaque input

/-- Compile subtraction of the same retained opaque atom from itself.

The original arithmetic channel is kept while symbolic provenance records cancellation. -/
def cancellation (input :
  CoherentNamed) :=
  (Expr.sub (.atom ⟨0, by decide⟩) (.atom ⟨0, by decide⟩)).compile (atomEnvironment input)

/-- Compiling self-subtraction retains the exact rational value zero. -/
theorem cancellation_value (input :
  CoherentNamed) : (cancellation input).rationalValue = some 0 :=
  Expr.compile_cancel (atomEnvironment input) (.atom ⟨0, by decide⟩)

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
  unfold squaredRoot Expr.compile
  rewrite [Expr.retain_mul, dif_pos rfl]
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
    ((Expr.sub (.atom (0 : Fin 2)) (.atom ⟨1, by decide⟩)).compile (fun _ =>
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

/-- The two original opaque channels at their distinct source indices. -/
def opaquePair (first second : CoherentNamed) : Fin 2 → Annotated :=
  Fin.cases (Annotated.opaque first) (fun _ => Annotated.opaque second)

/-- A commuted sum difference that has no syntactic self-cancellation. -/
def commutedSumDifference : Expr 2 :=
  .sub (.add (.atom ⟨0, by decide⟩) (.atom ⟨1, by decide⟩)) (.add (.atom ⟨1, by decide⟩) (.atom ⟨0, by decide⟩))

/-- The unchanged original expression with automatically inferred exact zero provenance. -/
def commutedZero (first second : CoherentNamed) : Annotated :=
  commutedSumDifference.compile (opaquePair first second)

/-- Polynomial normalization infers zero for arbitrary original opaque input channels. -/
theorem commuted_zero_value (first second : CoherentNamed) :
    (commutedZero first second).rationalValue = some 0 := by
  unfold commutedZero
  apply Expr.compile_inferred_value
  · rfl
  · unfold Expr.normalize Compiled.normalize
    dsimp only
    rewrite [Construction.normalize_form]
    dsimp only [Compiled.bindings]
    change (Sparse.sub
      (Sparse.add (Sparse.atom (⟨0, by decide⟩ : Fin 4))
        (Sparse.atom (⟨1, by decide⟩ : Fin 4)))
      (Sparse.add (Sparse.atom (⟨1, by decide⟩ : Fin 4))
        (Sparse.atom (⟨0, by decide⟩ : Fin 4)))).terms = (Sparse.constant (0 : Canonical)).terms
    decide +kernel

/-- Inferred commuted cancellation reaches exact division exclusion without a supplied zero certificate. -/
theorem commuted_zero_division (first second : CoherentNamed) :
    (Dispatch.acquire oneInput (State.start (commutedZero first second)) 1 (by decide)).2.status = .zero :=
  Dispatch.start_rational_zero oneInput (commutedZero first second) 1 (by decide) (commuted_zero_value first second)

/-- An expanded shifted square whose canonical value is one at the original opaque source. -/
def expandedUnitExpression : Expr 2 :=
  .sub (.sub (.mul (.add (.atom ⟨0, by decide⟩) (.rational 1)) (.add (.atom ⟨0, by decide⟩) (.rational 1)))
    (.mul (.atom ⟨0, by decide⟩) (.atom ⟨0, by decide⟩))) (.mul (.rational 2) (.atom ⟨0, by decide⟩))

/-- Compile the original expanded arithmetic while inferring its exact unit reading. -/
def expandedUnit (first second : CoherentNamed) : Annotated :=
  expandedUnitExpression.compile (opaquePair first second)

/-- The original expanded shifted square receives the exact unit value for arbitrary opaque input channels. -/
theorem expanded_unit_value (first second : CoherentNamed) :
    (expandedUnit first second).rationalValue = some 1 := by
  unfold expandedUnit
  apply Expr.compile_inferred_value
  · rfl
  · unfold Expr.normalize Compiled.normalize
    dsimp only
    rewrite [Construction.normalize_form]
    dsimp only [Compiled.bindings]
    change (Sparse.sub
      (Sparse.sub
        (Sparse.mul
          (Sparse.add (Sparse.atom (⟨0, by decide⟩ : Fin 3)) (Sparse.constant 1))
          (Sparse.add (Sparse.atom (⟨0, by decide⟩ : Fin 3)) (Sparse.constant 1)))
        (Sparse.mul (Sparse.atom (⟨0, by decide⟩ : Fin 3))
          (Sparse.atom (⟨0, by decide⟩ : Fin 3))))
      (Sparse.mul (Sparse.constant 2)
          (Sparse.atom (⟨0, by decide⟩ : Fin 3)))).terms = (Sparse.constant (1 : Canonical)).terms
    decide +kernel

/-- The original expanded unit identity minus one, with automatically inferred exact-zero evidence. -/
def expandedZero (first second : CoherentNamed) : Annotated :=
  (Expr.sub expandedUnitExpression (.rational 1)).compile (opaquePair first second)

/-- Polynomial normalization infers the exact zero reading of the expanded identity minus one. -/
theorem expanded_zero_value (first second : CoherentNamed) :
    (expandedZero first second).rationalValue = some 0 := by
  unfold expandedZero
  apply Expr.compile_inferred_value
  · rfl
  · unfold Expr.normalize Compiled.normalize
    dsimp only
    rewrite [Construction.normalize_form]
    dsimp only [Compiled.bindings]
    change (Sparse.sub (Sparse.sub
      (Sparse.sub
        (Sparse.mul
          (Sparse.add (Sparse.atom (⟨0, by decide⟩ : Fin 3)) (Sparse.constant 1))
          (Sparse.add (Sparse.atom (⟨0, by decide⟩ : Fin 3)) (Sparse.constant 1)))
        (Sparse.mul (Sparse.atom (⟨0, by decide⟩ : Fin 3))
          (Sparse.atom (⟨0, by decide⟩ : Fin 3))))
      (Sparse.mul (Sparse.constant 2)
          (Sparse.atom (⟨0, by decide⟩ : Fin 3)))) (Sparse.constant 1)).terms = (Sparse.constant (0 : Canonical)).terms
    decide +kernel

/-- The expanded opaque identity reaches the exact division obstruction without caller-supplied zero evidence. -/
theorem expanded_zero_division (first second : CoherentNamed) :
    (Dispatch.acquire oneInput (State.start (expandedZero first second)) 1 (by decide)).2.status = .zero :=
  Dispatch.start_rational_zero oneInput (expandedZero first second) 1 (by decide) (expanded_zero_value first second)

end Purelib.Examples.Approximation.Gaussian.Acquisition.Automation.WorkedExamples

end
