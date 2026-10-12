module
public import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Basic

section
@[expose] public section

/-!
# Gaussian conjugation through finite Horner folds

Conjugating a finite Gaussian Horner fold conjugates its coefficients and
initial accumulator while retaining their original order.
-/

namespace Purelib.Data.Gaussian.Conjugate.Evaluation

/-- Conjugate a finite Gaussian Horner fold by conjugating its coefficients and initial
accumulator.

The original fold evaluates at the conjugated argument; double conjugation recovers
the supplied argument while preserving coefficient order and every finite step. -/
public theorem conj_evalFold (argument :
  Canonical) :
    ∀ (coefficients : List Canonical) (accumulator : Canonical),
      Canonical.conj (coefficients.foldl
        (fun value coefficient => value * Canonical.conj argument + coefficient)
        accumulator) =
      coefficients.foldl
        (fun value coefficient => value * argument + Canonical.conj coefficient)
        (Canonical.conj accumulator)
  | [], _ => rfl
  | coefficient :: remaining, accumulator => by
      simp only [List.foldl_cons]
      rw [Purelib.Data.Gaussian.Conjugate.Evaluation.conj_evalFold argument remaining]
      apply congrArg (fun initial => remaining.foldl
        (fun value next => value * argument + Canonical.conj next) initial)
      rw [Canonical.conj_add, Canonical.conj_mul, Canonical.conj_conj]

end Purelib.Data.Gaussian.Conjugate.Evaluation

end
