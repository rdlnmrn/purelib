module

import Purelib.Algebra.Field.Squares
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

section
@[expose] public section

/-!
# Divine Proportions, Chapter 14 examples

The prime-field exclusions are stated through the exact finite Frobenius law
used by Euler's square test.  This avoids enumerating a carrier or searching
globally for roots.  The positive examples retain the literal source lines.
-/

namespace Purelib.Geometry.Plane.Line.Nullity

section

section

variable {K : Type*} [ExplicitField K] [Nontrivial K] [DecidableEq K]

omit [Nontrivial K] in
/-- Transfer non-nullness across one quotient-free line equivalence without choosing a projective representative. -/
public theorem printedLine_nonNull_of_equivalent
    (actual printed : Geometry.Plane.Line K) (equivalent : actual.Equivalent printed)
    (actualNonNull : ¬ actual.IsNull) : ¬ printed.IsNull := by
  rcases Relations.line_coefficient_scale_of_equivalent actual printed equivalent with
    ⟨scale, printedA, printedB, _printedC⟩
  intro printedNull
  have scaledNormZero :
      scale ^ 2 * (actual.a ^ 2 + actual.b ^ 2) = 0 := by
    calc
      scale ^ 2 * (actual.a ^ 2 + actual.b ^ 2) =
          printed.a ^ 2 + printed.b ^ 2 := by
        rw [printedA, printedB]
        ring1
      _ = 0 := printedNull
  have actualNormNonzero : actual.a ^ 2 + actual.b ^ 2 ≠ 0 :=
    actualNonNull
  have scaleSquareZero : scale ^ 2 = 0 := by
    by_cases scaleSquareZero : scale ^ 2 = 0
    · exact scaleSquareZero
    · exact False.elim
        ((ExplicitField.mul_ne_zero scaleSquareZero actualNormNonzero)
          scaledNormZero)
  have scaleZero := (fun {K : Type _} [ExplicitField K] [DecidableEq K] {value : K} (squareZero :
    value ^ 2 = 0) => (Purelib.Algebra.Field.Squares.eq_zero_of_square_eq_zero (K := K) value squareZero : value = 0))
    scaleSquareZero
  have printedAZero : printed.a = 0 := by
    rw [printedA, scaleZero]
    ring1
  have printedBZero : printed.b = 0 := by
    rw [printedB, scaleZero]
    ring1
  exact printed.direction_nonzero.elim
    (fun nonzero => nonzero printedAZero)
    (fun nonzero => nonzero printedBZero)

end

end

end Purelib.Geometry.Plane.Line.Nullity

end
