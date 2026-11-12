module

public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Algebraic
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.State

/-!
# Algebraic evidence through an already prepared fractional word

The evidence follows each original prepared action in order. It consumes the
same intermediate denominator preparations as the existing word evaluator,
without replacing the word by a single product-matrix quotient.
-/

public section

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Words

open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

/-- The actual stepwise word output and algebraic evidence at that same output. -/
@[expose] def Step.Output (tau : CoherentNamed) (matrices : List IntegralMatrix)
    (preparations : Step.StepPreparations tau matrices) : Type 1 :=
  Σ output : { value : CoherentNamed // value = Step.stepAction tau matrices preparations },
    Provenance.Algebraic.Sidecar output.val

/-- Carry the original algebraic input through an existing stepwise preparation schedule.

Each original matrix occurrence consumes its own supplied preparation and
the same retained output and evidence become the inputs to the next occurrence.
The final output is retained together with its original evaluator identity. -/
@[expose, noinline, nospecialize] def Step.sidecar : {tau : CoherentNamed} →
    (input : Provenance.Algebraic.Sidecar tau) → (matrices : List IntegralMatrix) →
    (preparations : Step.StepPreparations tau matrices) →
      Step.Output tau matrices preparations
  | tau, input, [], _ => ⟨⟨tau, rfl⟩, input⟩
  | _, input, matrix :: remaining, ⟨head, tail⟩ => by
      let rows := Integral.Algebraic.readRows input matrix
      let output := rows.output head
      have same := output.1.property
      cases same
      exact Step.sidecar output.2 remaining tail

/-- Carry algebraic evidence through the original stepwise view of a completed fold. -/
@[expose] def Fold.Basic.sidecar {tau : CoherentNamed} (input : Provenance.Algebraic.Sidecar tau)
    (matrices : List IntegralMatrix) (preparations : Fold.Basic.FoldPreparations tau matrices) :
    Step.Output tau matrices (Fold.Basic.FoldPreparations.toSteps matrices preparations) :=
  Step.sidecar input matrices (Fold.Basic.FoldPreparations.toSteps matrices preparations)

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Words

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Algebraic

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Division
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)
open Purelib.Riemann.Integration.LegendreModularMonodromy (fractionalDenominator)
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold

/-- Start the existing suffix cursor at this action's actual retained output.

The returned cursor keeps the same original matrix and denominator preparation.
The caller can retain the action alongside it for the suffix's algebraic input. -/
@[expose, noinline, nospecialize] def Action.startSuffix {tau : CoherentNamed} {matrix : IntegralMatrix}
    {preparation : Prepared.DenominatorPreparation (fractionalDenominator matrix tau)}
    (action : Action tau matrix preparation) (remaining : List IntegralMatrix) :
    State.Cursor tau (matrix :: remaining) :=
  .tail ⟨preparation, action.1.property ▸ State.initial action.1.val remaining⟩

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Algebraic

end
