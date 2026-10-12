module
import Purelib.Riemann.Integration.LegendreModularMonodromy
public import Purelib.Topology.Knot.Braid.ThreeStrand.Word
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Output
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Requirement
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.State
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Step
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.FromSearch
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Control.FiniteRunner.Basic
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual
import Init.Core
import Init.Prelude
import Purelib.Approximation.Gaussian.Division.Partial.Requirement
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Control.FiniteRunner.Progress
import Purelib.LinearAlgebra.Matrix.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Control

open Purelib.Control.FiniteRunner

open Purelib.Topology.Knot.Braid

open Purelib.Topology.Knot.Braid.ThreeStrand.Integral

section
@[expose] public section

/-!
# Automatic finite-word dual period outputs

The public result caches the exact word matrix, its denominator preparation,
and the productive output. A positive enclosure constructs it directly;
bounded acquisition returns either this same result or an exact resumable
state. The transport proof is shared by both construction routes.
-/

namespace Purelib.Curves.Legendre.Acquisition.Automatic.Basic
open Purelib.Riemann.Integration.LegendreModularMonodromy (fractionalDenominator fractionalLinear fractionalNumerator
  denominator_mul_fractionalLinear)

/-- A cached braid-word period matrix and its exact fractional-denominator search state.

The retained matrix equality connects the executable cache to the specified word; the search is indexed by that same
matrix and coherent input. -/
def State (tau : Coherent.CoherentNamed) (word :
  ThreeStrand.Word) :=
  State.StatePayload (fun matrix => matrix = Dual.periodMatrix word)
    (fun matrix => Approximation.Gaussian.FractionalAction.Integral.Acquisition.State matrix tau)

/-- Compute the period matrix once and initialize its denominator search. -/
def initial (tau : Coherent.CoherentNamed) (word :
  ThreeStrand.Word) : State tau word :=
  let matrix := Dual.periodMatrix word
  { matrix := matrix
    matrix_eq := rfl
    search := State.initial matrix tau }

/-- A prepared braid-word action with its cached matrix, denominator preparation and coherent output. -/
def Ready (tau : Coherent.CoherentNamed) (word :
  ThreeStrand.Word) :=
  Output.ReadyPayload (fun matrix => matrix = Dual.periodMatrix word)
    (fun matrix => Prepared.DenominatorPreparation (fractionalDenominator matrix tau))
    (fun matrix preparation => fractionalLinear matrix tau preparation)

/-- Finish a successful denominator search using its cached matrix and retained preparation. -/
def ready (tau : Coherent.CoherentNamed) (word :
  ThreeStrand.Word) (state : State tau word)
    (preparation : Prepared.DenominatorPreparation (fractionalDenominator state.matrix tau)) :
    Ready tau word :=
  { matrix := state.matrix
    matrix_eq := state.matrix_eq
    preparation := preparation
    output := fractionalLinear state.matrix tau preparation
    output_eq := rfl }

/-- A successful prepared braid-word output or the exact resumable search state. -/
def Result (tau : Coherent.CoherentNamed) (word :
  ThreeStrand.Word) : Type 1 :=
  LegendreTransport.ResultPayload.{1, 0} (Ready tau word)
    (State tau word)

/-- One denominator inspection returns either the final output or its next retained state. The small sum keeps runner
proofs independent of the large dependent denominator-process type. -/
def inspect (tau : Coherent.CoherentNamed) (word :
  ThreeStrand.Word) (state : State tau word) :
    Sum (Ready tau word) (State
      tau word) :=
  match Step.step state.matrix tau state.search with
  | .ready preparation => .inl (ready tau word state preparation)
  | .progressed next _ => .inr { state with search := next }

/-- Bounded automatic acquisition using only the one folded denominator. Exhaustion retains its matrix and refined state
for an exact resumption. -/
def attempt (tau : Coherent.CoherentNamed) (word :
  ThreeStrand.Word)
    (state : State tau word) (fuel : Nat) :
      Result tau word :=
  FiniteRunner.Basic.runPayload (inspect tau word) state fuel

/-- A zero-fuel attempt returns its unchanged retained search state. -/
@[simp] theorem attempt_zero (tau : Coherent.CoherentNamed)
  (word : ThreeStrand.Word)
    (state : State tau word) :
      attempt tau word state 0 = .exhausted state := rfl

/-- Splitting the single-matrix budget and resuming its exact retained state is exactly the same result as one
combined-budget run. -/
theorem attempt_add (tau : Coherent.CoherentNamed) (word :
  ThreeStrand.Word)
    (state : State tau word) (first second : Nat) :
    attempt tau word state (first + second) =
      match attempt tau word state first with
      | .ready result => .ready result
      | .exhausted retained => attempt tau word retained second := by
  unfold Result
  have law := FiniteRunner.Basic.runPayload_add (inspect tau word) state
    first second
  cases firstRun : FiniteRunner.Basic.runPayload (inspect tau word) state
    first <;>
    simpa only [attempt, firstRun] using law

/-- Manual evidence remains indexed by the exact denominator and retained search state, even though the public interface
is indexed by a braid word. -/
abbrev Requirement {tau : Coherent.CoherentNamed} {word :
  ThreeStrand.Word} (state : State tau word) :=
  Approximation.Gaussian.FractionalAction.Integral.Acquisition.Requirement state.search

/-- Manual apartness evidence indexed by the exact retained denominator requirement. -/
abbrev Evidence {tau : Coherent.CoherentNamed} {word :
  ThreeStrand.Word} {state : State tau word}
    (requirement : Requirement state) :=
  Requirement.Evidence requirement

/-- Read the current retained denominator requirement without another search step. -/
def currentRequirement {tau : Coherent.CoherentNamed} {word :
  ThreeStrand.Word}
    (state : State tau word) :
      Requirement state :=
  Requirement.currentRequirement state.search

/-- Satisfying the exact retained requirement returns an ordinary certified output immediately, with no further
automatic denominator search. -/
def resume {tau : Coherent.CoherentNamed} {word :
  ThreeStrand.Word}
    (state : State tau word) (requirement :
      Requirement state)
    (evidence : Evidence requirement) :
      Ready tau word :=
  match requirement with
  | .candidateApartness => ready tau word state
      (FromSearch.preparationAt
        state.matrix tau state.search evidence)

/-- Supplying the current requirement builds exactly the corresponding prepared output. -/
@[simp] theorem resume_eq_ready {tau :
  Coherent.CoherentNamed} {word : ThreeStrand.Word}
    (state : State tau word) (evidence :
      Evidence
      (currentRequirement state)) :
    resume state
      (currentRequirement state) evidence =
      ready tau word state (FromSearch.preparationAt
        state.matrix tau state.search evidence) := rfl

namespace Ready

/-- Reindex the retained preparation without recomputing the matrix. -/
def periodPreparation {tau : Coherent.CoherentNamed}
  {word : ThreeStrand.Word}
    (result : Curves.Legendre.Acquisition.Automatic.Basic.Ready tau word) :
    Prepared.DenominatorPreparation (fractionalDenominator
      (Dual.periodMatrix word) tau) := by
  rw [← result.matrix_eq]
  exact result.preparation

/-- The retained word denominator multiplied by the cached output agrees with its word numerator.

The matrix and output equalities transport the prepared fractional-action identity to the originally requested braid
word. -/
def output_equation {tau : Coherent.CoherentNamed}
  {word : ThreeStrand.Word}
    (result : Curves.Legendre.Acquisition.Automatic.Basic.Ready tau word) :
    Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul
        (fractionalDenominator
          (Dual.periodMatrix word) tau)
        result.output).name
      (fractionalNumerator
        (Dual.periodMatrix word) tau).name := by
  have denominatorEq := congrArg (fun matrix => fractionalDenominator matrix tau)
    result.matrix_eq
  have numeratorEq := congrArg (fun matrix => fractionalNumerator matrix tau)
    result.matrix_eq
  rw [result.output_eq, ← denominatorEq, ← numeratorEq]
  exact denominator_mul_fractionalLinear _ _ result.preparation
end Ready
end Purelib.Curves.Legendre.Acquisition.Automatic.Basic

end
