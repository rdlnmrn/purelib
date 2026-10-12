module
public import Purelib.Data.Gaussian.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic

section
@[expose] public section

/-!
# Gaussian addition folds

A finite Gaussian addition fold separates its original accumulator from the
fold started at zero, preserving the input list and its order.
-/

namespace Purelib.Data.Gaussian.Sum

/-- Separate the initial accumulator from a finite Gaussian addition fold.

Folding addition through a list of canonical Gaussian rationals from any accumulator equals that accumulator plus the
same fold started at zero. The list order is preserved. -/
public theorem foldl_add_from (values : List Canonical)
    (accumulator : Canonical) :
    values.foldl (fun a b => a + b) accumulator =
      accumulator + values.foldl (fun a b => a + b) 0 := by
  induction values generalizing accumulator with
  | nil =>
      change accumulator = accumulator + 0
      ring1
  | cons value remaining inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis]
      rw [List.foldl_cons, show (0 : Canonical) + value = value by ring1]
      rw [inductionHypothesis value]
      ring1

end Purelib.Data.Gaussian.Sum

end
