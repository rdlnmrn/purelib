module
import Purelib.Algebra.NatCast
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

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

namespace Purelib.Polynomial.Winding.Polygon.Repeat

open Purelib.Data.List in
open Purelib.Algebra in
/-- Repeating one explicit closed polygon adds its raw winding exactly. -/
theorem closedRaw_repeatClosedVertices
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (base : Gaussian.Basic.Canonical)
    (vertices : List Gaussian.Basic.Canonical) : ∀ additional : Nat,
    Winding.Polygon.Basic.closedRaw p base (Polygon.Chain.repeatClosedVertices base vertices additional) =
      ((additional + 1 : Nat) : Int) * Winding.Polygon.Basic.closedRaw p base vertices
  | 0 => by
      simp only [Polygon.Chain.repeatClosedVertices]
      ring1
  | additional + 1 => by
      simp only [Polygon.Chain.repeatClosedVertices, Winding.Polygon.Basic.closedRaw]
      rw [show
        (vertices ++ base :: Polygon.Chain.repeatClosedVertices base vertices additional) ++
            [base] =
          (vertices ++ [base]) ++
            (Polygon.Chain.repeatClosedVertices base vertices additional ++ [base]) by
        simp only [Append.append_assoc, List.cons_append, List.nil_append, -eq_self, -iff_self]
        rfl]
      rw [Winding.Polygon.Basic.chainRaw_append p base (vertices ++ [base])
        (Polygon.Chain.repeatClosedVertices base vertices additional ++ [base]),
        Polygon.Chain.terminal_append_singleton]
      change Winding.Polygon.Basic.closedRaw p base vertices +
          Winding.Polygon.Basic.closedRaw p base (Polygon.Chain.repeatClosedVertices base vertices additional) =
        ((additional + 1 + 1 : Nat) : Int) * Winding.Polygon.Basic.closedRaw p base vertices
      rw [closedRaw_repeatClosedVertices p base vertices additional]
      have castSuccessors : ((additional + 1 + 1 : Nat) : Int) =
          (additional : Int) + 1 + 1 := by
        simp only [NatCast.add, Nat.cast_one, -eq_self, -iff_self]
        rfl
      have castAdditional : ((additional + 1 : Nat) : Int) =
          (additional : Int) + 1 := by
        simp only [NatCast.add, Nat.cast_one, -eq_self, -iff_self]
        rfl
      rw [castSuccessors, castAdditional]
      ring1
end Purelib.Polynomial.Winding.Polygon.Repeat

end
