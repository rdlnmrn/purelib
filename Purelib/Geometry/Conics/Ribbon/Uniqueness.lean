module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Geometry.Conics.Ribbon.Basic
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Plane.Conic.Center
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra.Field

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Conics

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

section
@[expose] public section

/-!
# Divine Proportions, Exercise 15.6: ribbons

A ribbon is kept as finite coefficient data for the cleared equation
`(ax+by+c)² = K(a²+b²)`.  The presentation retains its arbitrary nonzero
conic scale, while equality of displayed lines remains the quotient-free
relation `Line.Equivalent`.
-/

namespace Purelib.Geometry

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Conics.Ribbon.Uniqueness

/-- Uniqueness part of Exercise 15.6: the line is unique up to its displayed coefficient proportion, and the ribbon
quadrance is literally unique. -/
theorem uniqueness
    (source : Conic K) (twoNonzero : (2 : K) ≠ 0)
    {firstLine secondLine : Plane.Line K}
    {firstQuadrance secondQuadrance : K}
    (firstPresentation : Ribbon.IsPresentation source firstLine firstQuadrance)
    (secondPresentation : Ribbon.IsPresentation source secondLine secondQuadrance) :
    firstLine.Equivalent secondLine ∧
      firstQuadrance = secondQuadrance := by
  rcases firstPresentation with ⟨first⟩
  rcases secondPresentation with ⟨second⟩
  have sameContains : ∀ point : Plane.Point K,
      firstLine.Contains point ↔ secondLine.Contains point := by
    intro point
    calc
      firstLine.Contains point ↔ source.IsCenter point :=
        (first.isCenter_iff_contains twoNonzero point).symm
      _ ↔ secondLine.Contains point :=
        second.isCenter_iff_contains twoNonzero point
  have linesEquivalent :=
    Purelib.Geometry.Plane.Line.Relations.line_equivalent_of_same_contains firstLine secondLine sameContains
  rcases Relations.line_coefficient_scale_of_equivalent firstLine secondLine
      linesEquivalent with ⟨lineScale, secondA, secondB, secondC⟩
  have weightedScalesEqual :
      first.scale = second.scale * lineScale ^ 2 := by
    rcases firstLine.direction_nonzero with firstANonzero | firstBNonzero
    · have firstASquareNonzero : firstLine.a ^ 2 ≠ 0 := by
        simpa only [pow_two] using
          Algebra.Field.ExplicitField.mul_ne_zero firstANonzero firstANonzero
      apply (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] {factor left right : K} (factorNonzero : factor ≠
        0) (productsEqual : factor * left = factor * right) =>
        (Purelib.Algebra.Field.ExplicitField.eq_of_mul_eq_mul_left (K := K) (left := left) (right := right) (factor :=
        factor) factorNonzero productsEqual : left = right)) firstASquareNonzero
      calc
        firstLine.a ^ 2 * first.scale = source.d := by
          rw [first.dEquation]
          ring1
        _ = second.scale * secondLine.a ^ 2 := second.dEquation
        _ = firstLine.a ^ 2 * (second.scale * lineScale ^ 2) := by
          rw [secondA]
          ring1
    · have firstBSquareNonzero : firstLine.b ^ 2 ≠ 0 := by
        simpa only [pow_two] using
          Algebra.Field.ExplicitField.mul_ne_zero firstBNonzero firstBNonzero
      apply (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] {factor left right : K} (factorNonzero : factor ≠
        0) (productsEqual : factor * left = factor * right) =>
        (Purelib.Algebra.Field.ExplicitField.eq_of_mul_eq_mul_left (K := K) (left := left) (right := right) (factor :=
        factor) factorNonzero productsEqual : left = right)) firstBSquareNonzero
      calc
        firstLine.b ^ 2 * first.scale = source.f := by
          rw [first.fEquation]
          ring1
        _ = second.scale * secondLine.b ^ 2 := second.fEquation
        _ = firstLine.b ^ 2 * (second.scale * lineScale ^ 2) := by
          rw [secondB]
          ring1
  have secondNorm :
      Basic.lineNorm secondLine = lineScale ^ 2 * Basic.lineNorm firstLine := by
    unfold Basic.lineNorm
    rw [secondA, secondB]
    ring1
  have scaledConstantsEqual :
      first.scale *
          (firstLine.c ^ 2 - firstQuadrance * Basic.lineNorm firstLine) =
        first.scale *
          (firstLine.c ^ 2 - secondQuadrance * Basic.lineNorm firstLine) := by
    calc
      first.scale *
          (firstLine.c ^ 2 - firstQuadrance * Basic.lineNorm firstLine) =
        source.c := first.cEquation.symm
      _ = second.scale *
          (secondLine.c ^ 2 - secondQuadrance * Basic.lineNorm secondLine) :=
        second.cEquation
      _ = (second.scale * lineScale ^ 2) *
          (firstLine.c ^ 2 - secondQuadrance * Basic.lineNorm firstLine) := by
        rw [secondC, secondNorm]
        ring1
      _ = first.scale *
          (firstLine.c ^ 2 - secondQuadrance * Basic.lineNorm firstLine) := by
        rw [← weightedScalesEqual]
  have constantsEqual :=
    (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] {factor left right : K} (factorNonzero : factor ≠ 0)
      (productsEqual : factor * left = factor * right) => (Purelib.Algebra.Field.ExplicitField.eq_of_mul_eq_mul_left (K
      := K) (left := left) (right := right) (factor := factor) factorNonzero productsEqual : left = right))
      first.scaleNonzero scaledConstantsEqual
  have normProductZero :
      Basic.lineNorm firstLine * (firstQuadrance - secondQuadrance) = 0 := by
    calc
      Basic.lineNorm firstLine * (firstQuadrance - secondQuadrance) =
          -((firstLine.c ^ 2 - firstQuadrance * Basic.lineNorm firstLine) -
            (firstLine.c ^ 2 - secondQuadrance * Basic.lineNorm firstLine)) := by
        ring1
      _ = 0 := by rw [constantsEqual]; ring1
  have quadranceDifferenceZero :=
    Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left first.lineNonNull normProductZero
  refine ⟨linesEquivalent, ?_⟩
  calc
    firstQuadrance =
        (firstQuadrance - secondQuadrance) + secondQuadrance := by ring1
    _ = secondQuadrance := by rw [quadranceDifferenceZero]; ring1

/-- Exercise 15.6 packaged from the definition: a ribbon has a unique line and quadrance, and every point on that line
is an explicit center. -/
theorem exercise_15_6
    (source : Conic K) (twoNonzero : (2 : K) ≠ 0)
    (isRibbon : Ribbon.IsRibbon source) :
    ∃ line : Plane.Line K, ∃ ribbonQuadrance : K,
      Ribbon.IsPresentation source line ribbonQuadrance ∧
        (∀ otherLine : Plane.Line K, ∀ otherQuadrance : K,
          Ribbon.IsPresentation source otherLine otherQuadrance →
            line.Equivalent otherLine ∧
              ribbonQuadrance = otherQuadrance) ∧
        ∀ point : Plane.Point K,
          line.Contains point → source.IsCenter point := by
  rcases isRibbon with ⟨line, ribbonQuadrance, presentation⟩
  refine ⟨line, ribbonQuadrance, presentation, ?_, ?_⟩
  · intro otherLine otherQuadrance otherPresentation
    exact Geometry.Conics.Ribbon.Uniqueness.uniqueness source twoNonzero presentation otherPresentation
  · intro point onLine
    rcases presentation with ⟨presentation⟩
    exact (presentation.isCenter_iff_contains twoNonzero point).2 onLine

end Conics.Ribbon.Uniqueness

end Purelib.Geometry

end
