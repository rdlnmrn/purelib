module
public import Purelib.Polynomial.Recurrence.Spread.Basic
import Purelib.Polynomial.Recurrence.Spread.Composition

import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring
import Purelib.Polynomial.Recurrence.Spread.Triple

open Purelib.Algebra.Field

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Appendix B: the ellipson

This module formalizes every finite algebraic assertion in Appendix B: the
defining surface, its full coordinate symmetry, its tetrahedral intersection
with the algebraic boundary of the unit cube, the coordinate-plane ellipse
sections and their four tangencies, the oblique section, and its rational
polar equation.  The volume calculation in Exercise B.1 is an analytic
integral and remains outside the agreed finite boundary.
-/

section

section

variable {K : Type*} [ExplicitField K]

namespace Purelib.Polynomial.Recurrence.Spread.Values.Ellipson

/-- The left side of the oblique equation is exactly the third spread
polynomial, as asserted in Appendix B. -/
theorem oblique_left_is_third_spread_polynomial (spread : K)
  :
    Recurrence.Spread.Basic.spreadPolynomial 3 spread = spread * (3 - 4 * spread) ^ 2 := by
  simp only [Recurrence.Spread.Basic.spreadPolynomial]
  ring1

end Purelib.Polynomial.Recurrence.Spread.Values.Ellipson

end
end

end

section
@[expose] public section

/-!
# Divine Proportions, Theorem 96: regular stars of order five

The five cyclic reflection equations and all ten nonparallel pairs are stored
as finite data.  The executable reflection iterator is then related to these
displayed representatives using quotient-free line congruence.
-/

section

variable {K : Type*} [ExplicitField K]

namespace Purelib.Polynomial.Recurrence.Spread.Values

/-- The explicit factorization `S₅(s)=s(5-20s+16s²)²`. -/
theorem spreadPolynomial_five_formula (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial 5 value = value * (5 - 20 * value + 16 * value ^ 2) ^ 2 := by
  simp only [Recurrence.Spread.Basic.spreadPolynomial]
  ring1

end Purelib.Polynomial.Recurrence.Spread.Values

end

end

section
@[expose] public section

/-!
# Divine Proportions, Theorem 97: regular stars of order seven

Only the seven required lines are quantified over, through `Fin 7`.  Their
coefficients are obtained by the executable finite reflection iterator; the
two closing equations record exactly the wraparound needed for the cyclic
star.  No completed two-sided reflection sequence is introduced.
-/

section

variable {K : Type*} [ExplicitField K]

namespace Purelib.Polynomial.Recurrence.Spread.Values

/-- The explicit factorization
`S₇(s)=s(7-56s+112s²-64s³)²`. -/
theorem spreadPolynomial_seven_formula (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial 7 value =
      value *
        (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) ^ 2 := by
  simp only [Recurrence.Spread.Basic.spreadPolynomial]
  ring1

end Purelib.Polynomial.Recurrence.Spread.Values

end

section
variable {K : Type*} [ExplicitField K]

section

open _root_.Purelib.Geometry

namespace Purelib.Polynomial.Recurrence.Spread.Values

/-- The second spread polynomial is four times the argument times its complement. -/
public theorem spreadPolynomial_two_formula (value
  : K) :
    Recurrence.Spread.Basic.spreadPolynomial 2 value = 4 * value * (1 - value) := by
  simp only [Recurrence.Spread.Basic.spreadPolynomial]
  ring1

end Purelib.Polynomial.Recurrence.Spread.Values

end
end

section

variable {K : Type*} [ExplicitField K]

namespace Purelib.Geometry

/-- The third spread polynomial is the argument times the square of three minus four times the argument. -/
private theorem spreadPolynomial_three_formula (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial 3 value = value * (3 - 4 * value) ^ 2 := by
  simp only [Recurrence.Spread.Basic.spreadPolynomial]
  ring1

end Purelib.Geometry

end

section
variable {K : Type*} [ExplicitField K]

section

open _root_.Purelib.Geometry

namespace Purelib.Polynomial.Recurrence.Spread.Values

/-- The fourth spread polynomial is sixteen times the argument, its complement and the square of one minus twice the
argument. -/
public theorem spreadPolynomial_four_formula
  (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial 4 value =
      16 * value * (1 - value) * (1 - 2 * value) ^ 2 := by
  simp only [Recurrence.Spread.Basic.spreadPolynomial]
  ring1
/-- The sixth spread polynomial is four times the argument, its complement and the square of three minus sixteen times
the argument plus sixteen times its square. -/
public theorem spreadPolynomial_six_formula (value
  : K) :
    Recurrence.Spread.Basic.spreadPolynomial 6 value =
      4 * value * (1 - value) *
        (3 - 16 * value + 16 * value ^ 2) ^ 2 := by
  simp only [Recurrence.Spread.Basic.spreadPolynomial]
  ring1

end Purelib.Polynomial.Recurrence.Spread.Values

end
end

section

variable {K : Type*} [ExplicitField K]

end

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: the spread coefficient array

Exercise 8.9 writes every spread polynomial as a finite binomial-coefficient
sum.  Its displayed coefficient contains a quotient.  We first identify it
with the integral entry obtained by adding two shifted copies of Pascal's
triangle.  This gives a division-free theorem over every commutative ring;
the source's quotient notation is recovered only when its finitely many
denominators are supplied as nonzero.
-/

section

namespace Purelib.Polynomial.Recurrence.Spread.Values

/-- The source's worked scaled-polynomial example
`S₃*(r) = 4S₃(r/4) = 9r - 6r² + r³`. -/
theorem scaledSpreadPolynomial_three
    {K : Type*} [ExplicitField K]
    (value : K) (fourNonzero : (4 : K) ≠ 0) :
    4 * Recurrence.Spread.Basic.spreadPolynomial 3 (value / 4) =
      9 * value - 6 * value ^ 2 + value ^ 3 := by
  let quarter := value / 4
  have recoverValue : value = 4 * quarter := by
    unfold quarter
    calc
      value = value / 4 * 4 :=
        (ExplicitField.div_mul_cancel value fourNonzero).symm
      _ = 4 * (value / 4) := by ring1
  change 4 * Recurrence.Spread.Basic.spreadPolynomial 3 quarter =
    9 * value - 6 * value ^ 2 + value ^ 3
  rw [recoverValue]
  simp only [Recurrence.Spread.Basic.spreadPolynomial]
  ring1

end Purelib.Polynomial.Recurrence.Spread.Values

end

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8 worked examples

The displayed formulas are finite polynomial identities over an arbitrary
constructive explicit field.  In particular, they may be evaluated over the
project's constructive rationals or any of its explicit finite fields.
-/

section

section

variable {K : Type*} [ExplicitField K]

namespace Purelib.Polynomial.Recurrence.Spread.Values

/-- The quadratic spread polynomial in both displayed forms. -/
theorem spreadPolynomial_two (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial 2 value = 4 * value - 4 * value ^ 2 ∧
      Recurrence.Spread.Basic.spreadPolynomial 2 value = 4 * value * (1 - value) := by
  simp only [Recurrence.Spread.Basic.spreadPolynomial]
  exact ⟨by ring1, by ring1⟩

/-- The cubic spread polynomial used in Example 8.5. -/
theorem spreadPolynomial_three (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial 3 value = value * (3 - 4 * value) ^ 2 := by
  simp only [Recurrence.Spread.Basic.spreadPolynomial]
  ring1

/-- The third spread polynomial has coefficients nine, minus twenty-four and sixteen. -/
theorem spreadPolynomial_three_expanded (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial 3 value =
      9 * value - 24 * value ^ 2 + 16 * value ^ 3 := by
  rw [spreadPolynomial_three]
  ring1

/-- The quartic spread polynomial in both displayed forms. -/
theorem spreadPolynomial_four (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial 4 value =
        16 * value - 80 * value ^ 2 + 128 * value ^ 3 - 64 * value ^ 4 ∧
      Recurrence.Spread.Basic.spreadPolynomial 4 value =
        16 * value * (1 - value) * (1 - 2 * value) ^ 2 := by
  simp only [Recurrence.Spread.Basic.spreadPolynomial]
  exact ⟨by ring1, by ring1⟩

/-- The quintic spread polynomial used in Example 8.5. -/
theorem spreadPolynomial_five (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial 5 value =
      value * (5 - 20 * value + 16 * value ^ 2) ^ 2 := by
  simp only [Recurrence.Spread.Basic.spreadPolynomial]
  ring1

/-- The fifth spread polynomial has the displayed exact quintic coefficient expansion. -/
theorem spreadPolynomial_five_expanded (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial 5 value =
      25 * value - 200 * value ^ 2 + 560 * value ^ 3 -
        640 * value ^ 4 + 256 * value ^ 5 := by
  rw [spreadPolynomial_five]
  ring1

/-- The sextic spread polynomial in both displayed forms. -/
theorem spreadPolynomial_six (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial 6 value =
        36 * value - 420 * value ^ 2 + 1792 * value ^ 3 -
          3456 * value ^ 4 + 3072 * value ^ 5 - 1024 * value ^ 6 ∧
      Recurrence.Spread.Basic.spreadPolynomial 6 value =
        4 * value * (1 - value) * (1 - 4 * value) ^ 2 *
          (3 - 4 * value) ^ 2 := by
  simp only [Recurrence.Spread.Basic.spreadPolynomial]
  exact ⟨by ring1, by ring1⟩

/-- The seventh spread polynomial in both displayed forms. -/
theorem spreadPolynomial_seven (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial 7 value =
        49 * value - 784 * value ^ 2 + 4704 * value ^ 3 -
          13440 * value ^ 4 + 19712 * value ^ 5 -
          14336 * value ^ 6 + 4096 * value ^ 7 ∧
      Recurrence.Spread.Basic.spreadPolynomial 7 value =
        value * (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) ^ 2 := by
  simp only [Recurrence.Spread.Basic.spreadPolynomial]
  exact ⟨by ring1, by ring1⟩

/-- Example 8.5's first computation of `S₁₅` as `S₃(S₅(s))`. -/
theorem example_8_5_fifteen_composition (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial 15 value =
      value * (5 - 20 * value + 16 * value ^ 2) ^ 2 *
        (3 - 4 * value *
          (5 - 20 * value + 16 * value ^ 2) ^ 2) ^ 2 := by
  calc
    Recurrence.Spread.Basic.spreadPolynomial 15 value =
        Recurrence.Spread.Basic.spreadPolynomial 3 (Recurrence.Spread.Basic.spreadPolynomial 5 value) :=
      (Recurrence.Spread.Composition.spread_polynomial_composition 3 5 value).symm
    _ = Recurrence.Spread.Basic.spreadPolynomial 5 value *
        (3 - 4 * Recurrence.Spread.Basic.spreadPolynomial 5 value) ^ 2 :=
      spreadPolynomial_three _
    _ = value * (5 - 20 * value + 16 * value ^ 2) ^ 2 *
        (3 - 4 * value *
          (5 - 20 * value + 16 * value ^ 2) ^ 2) ^ 2 := by
      rw [spreadPolynomial_five]
      ring1

/-- The fully factored `S₁₅` formula displayed in Example 8.5. -/
theorem example_8_5_fifteen_factored (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial 15 value =
      value * (3 - 4 * value) ^ 2 *
        (5 - 20 * value + 16 * value ^ 2) ^ 2 *
        (1 - 32 * value + 224 * value ^ 2 - 448 * value ^ 3 +
          256 * value ^ 4) ^ 2 := by
  rw [example_8_5_fifteen_composition]
  ring1

/-- Example 8.5's finite `S₃₀ = S₂(S₁₅)` step. -/
theorem example_8_5_thirty_composition (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial 30 value =
      4 * Recurrence.Spread.Basic.spreadPolynomial 15 value *
        (1 - Recurrence.Spread.Basic.spreadPolynomial 15 value) := by
  calc
    Recurrence.Spread.Basic.spreadPolynomial 30 value =
        Recurrence.Spread.Basic.spreadPolynomial 2 (Recurrence.Spread.Basic.spreadPolynomial 15 value) :=
      (Recurrence.Spread.Composition.spread_polynomial_composition 2 15 value).symm
    _ = 4 * Recurrence.Spread.Basic.spreadPolynomial 15 value *
        (1 - Recurrence.Spread.Basic.spreadPolynomial 15 value) :=
      spreadPolynomial_two_formula
        (Recurrence.Spread.Basic.spreadPolynomial 15 value)

/-- The fully factored `S₃₀` formula displayed in Example 8.5. -/
theorem example_8_5_thirty_factored (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial 30 value =
      4 * value * (1 - value) * (3 - 4 * value) ^ 2 *
        (5 - 20 * value + 16 * value ^ 2) ^ 2 *
        (1 - 32 * value + 224 * value ^ 2 - 448 * value ^ 3 +
          256 * value ^ 4) ^ 2 *
        (1 - 4 * value) ^ 2 *
        (1 - 12 * value + 16 * value ^ 2) ^ 2 *
        (1 - 96 * value + 416 * value ^ 2 - 576 * value ^ 3 +
          256 * value ^ 4) ^ 2 := by
  rw [example_8_5_thirty_composition,
    example_8_5_fifteen_factored]
  ring1

end Purelib.Polynomial.Recurrence.Spread.Values

end

end

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 2 finite-field examples

The source's characteristic-seven arithmetic and characteristic-nineteen
polynomial data are recorded by exact finite calculations.  The `S₅` table is
a literal list evaluation, not a claim that a list enumerates an ambient
carrier.  The characteristic-nineteen factorization is proved as a direct
polynomial identity; no carrier enumeration or root search is used.
-/

section

section

variable {K : Type*} [ExplicitField K] [Nontrivial K]

namespace Purelib.Polynomial.Recurrence.Spread.Values

/-- The finite expression plotted in Example 2.16. -/
def spreadFiveExpression {R : Type*} [CommRing R] (value : R) : R :=
  value * (16 * value ^ 2 - 20 * value + 5) ^ 2

omit [Nontrivial K] in
/-- Example 2.16: the fifth spread polynomial is exactly the displayed finite
quintic expression; the source's decimal plot adds no further algebraic
claim. -/
theorem example_2_16 (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial 5 value = spreadFiveExpression value := by
  simp only [Recurrence.Spread.Basic.spreadPolynomial]
  unfold spreadFiveExpression
  ring1

end Purelib.Polynomial.Recurrence.Spread.Values

end

end

end
