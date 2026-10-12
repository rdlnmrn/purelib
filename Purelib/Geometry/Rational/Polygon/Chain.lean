module
public import Purelib.Data.Gaussian.Basic
import Init.Prelude

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

section
@[expose] public section

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

namespace Purelib.Geometry.Rational.Polygon.Chain

/-- Terminal vertex of the same finite open chain. -/
def terminal : Canonical → List
  Canonical → Canonical
  | start, [] => start
  | _, finish :: remaining => terminal finish remaining

/-- Repeating the initial point at the front of a chain does not change its terminal point. -/
@[simp] theorem terminal_cons_self
    (point : Data.Gaussian.Basic.Canonical) (remaining : List Data.Gaussian.Basic.Canonical) :
    terminal point (point :: remaining) = terminal point
      remaining := rfl

/-- The terminal point of a concatenated chain is obtained by continuing the second chain from the terminal point of the
first. -/
theorem terminal_append :
    ∀ (start : Data.Gaussian.Basic.Canonical) (first second : List Data.Gaussian.Basic.Canonical),
      terminal start (first ++ second) =
        terminal (terminal start first) second
  | start, [], second => rfl
  | start, finish :: remaining, second => by
      simp only [List.cons_append, terminal]
      exact terminal_append finish remaining second

/-- Appending a final singleton makes that point the terminal vertex. -/
@[simp] theorem terminal_append_singleton
    (start base : Data.Gaussian.Basic.Canonical) (vertices : List Data.Gaussian.Basic.Canonical) :
    terminal start (vertices ++ [base]) = base := by
  induction vertices generalizing start with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, terminal]
      exact inductionHypothesis head

/-- Concatenate one or more copies of a displayed closed vertex list. `additional` is the number of copies after the
first; each non-final copy includes its return to `base`, while `closedRaw` supplies the final return. -/
def repeatClosedVertices (base : Canonical)
  (vertices : List Canonical) :
    Nat → List Canonical
  | 0 => vertices
  | additional + 1 =>
      vertices ++ base :: repeatClosedVertices base vertices additional
end Purelib.Geometry.Rational.Polygon.Chain

end
