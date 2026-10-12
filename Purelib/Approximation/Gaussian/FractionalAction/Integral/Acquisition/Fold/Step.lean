module
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Cached
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.State
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Step
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.LinearAlgebra.Matrix.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.State
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Control.FiniteRunner.Progress
import Purelib.LinearAlgebra.Matrix.Integral.Word
import Purelib.LinearAlgebra.Matrix.Multiplication

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold

open Purelib.Approximation.Gaussian.Name

open Purelib.LinearAlgebra.Matrix

open Purelib.LinearAlgebra.Matrix.Integral

section
@[expose] public section

/-!
# Resumable automatic acquisition for stepwise dual words

Each cursor retains completed head and suffix preparations, plus the exact
current denominator search state. Exhausting a budget preserves the cursor;
resumption neither reconstructs earlier outputs nor starts their searches
again. The final preparation is consumed directly by the existing arbitrary
finite-word period theorem.
-/

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Step
open Purelib.Riemann.Integration.LegendreModularMonodromy (fractionalLinear)

/-- One bounded work unit, possibly descending into the retained suffix. Only one denominator inspection occurs during a
unit. -/
def step (tau :
  Coherent.CoherentNamed) : (matrices : List LinearAlgebra.Matrix.Basic.IntegralMatrix) →
    State.Cursor tau matrices → State.Cursor tau matrices
  | [], .inr preparations => .inr preparations
  | [], .inl state =>
      match Acquisition.Step.step _ tau state with
      | .ready preparation => .inr preparation
      | .progressed next _ => .inl next
  | _ :: _, .ready preparations => .ready preparations
  | matrix :: remaining, .head state =>
      match Acquisition.Step.step matrix tau state with
      | .ready preparation => .tail ⟨preparation,
          State.initial (fractionalLinear matrix tau preparation) remaining⟩
      | .progressed next _ => .head next
  | matrix :: remaining, .tail ⟨head, cursor⟩ =>
      match State.finished? (fractionalLinear matrix tau head) remaining cursor with
      | some tail => .combined ⟨head, tail,
          Cached.cachedInitial tau (Word.matrixProduct (matrix :: remaining))⟩
      | none => .tail ⟨head, step
        (fractionalLinear matrix tau head) remaining cursor⟩
  | _ :: _, .combined ⟨head, tail, state⟩ =>
      match Acquisition.Step.step state.matrix tau state.search with
      | .ready preparation => .ready ⟨head, tail, Cached.cachedPreparation state preparation⟩
      | .progressed next _ => .combined ⟨head, tail, { state with search := next }⟩
end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Step

end
