module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Cached
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.State
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Init.Core
import Init.Prelude
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.LinearAlgebra.Matrix.Integral.Word

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic (FoldPreparations)
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

open Purelib

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words

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

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.State
open Purelib.Riemann.Integration.LegendreModularMonodromy (fractionalDenominator fractionalLinear)

set_option genInjectivity false in
/-- The four stages of dependent fractional-word acquisition.

A cursor retains either the head search, a prepared head with a suffix cursor, the combined-matrix search after the
suffix completes, or all finished preparations. -/
inductive CursorPayload (headType
  : Type) (tailType combinedType readyType : Type 1) : Type 1
  /-- The head denominator is still being acquired. -/ | head (state : headType)
  /-- The prepared head and the current suffix acquisition state are retained. -/ | tail (state : tailType)
  /-- The head and suffix are prepared; acquisition of the folded denominator remains. -/ | combined (state :
    combinedType)
  /-- All precisely indexed fold preparations have been retained. -/ | ready (preparations : readyType)

constructive_injectivity CursorPayload

/-- Finite dependent acquisition cursor; every preparation is indexed by the literal intermediate name at which division
will execute. -/
def Cursor (tau :
  Coherent.CoherentNamed) : List IntegralMatrix → Type 1
  | [] => Sum (Approximation.Gaussian.FractionalAction.Integral.Acquisition.State Multiplication.identity tau)
      (FoldPreparations tau [])
  | matrix :: remaining => CursorPayload
      (Approximation.Gaussian.FractionalAction.Integral.Acquisition.State matrix tau)
      (Sigma fun head : Prepared.DenominatorPreparation (fractionalDenominator matrix tau) =>
        Cursor (fractionalLinear matrix
          tau head) remaining)
      (Sigma fun head : Prepared.DenominatorPreparation (fractionalDenominator matrix tau) =>
        Sigma fun _tail : FoldPreparations (fractionalLinear matrix tau head) remaining =>
          Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining)))
      (FoldPreparations tau (matrix :: remaining))

/-- Initialize a finite-word cursor at the head denominator, or the identity denominator for an empty word. -/
def initial (tau :
  Coherent.CoherentNamed) : (matrices : List IntegralMatrix) →
  Cursor tau matrices
  | [] => .inl (Acquisition.State.initial _ tau)
  | _ :: _ => .head (Acquisition.State.initial _ tau)

/-- Read completed fold preparations from a cursor without performing another denominator inspection. -/
def finished? (tau :
  Coherent.CoherentNamed) : (matrices : List IntegralMatrix) →
    Cursor tau matrices → Option
      (FoldPreparations tau matrices)
  | [], .inl _ => none
  | [], .inr preparations => some preparations
  | _ :: _, .ready preparations => some preparations
  | _ :: _, .head _ => none
  | _ :: _, .tail _ => none
  | _ :: _, .combined _ => none
end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.State

end
