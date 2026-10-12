module

import Purelib.Algebra.Field.Squares
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Nat.Order
import Purelib.Algebra.Group.Negation
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Trigonometry

section
@[expose] public section

/-!
# Divine Proportions, §12.5: the incenter spread theorem

This module formalizes the source's translated-coordinate proof.  The
incenter is the origin; `firstMirror` and `secondMirror` are the first two
vertex bisectors, and `target` is the side joining their triangle vertices.
Reflecting `target` in those mirrors gives the other two sides.  The displayed
third line joins the origin to their intersection.

The key computation is denominator-free: the third line's spread with the
first reflected side equals the cross of the two initial mirrors.  Fibonacci's
spread-plus-cross identity then gives the printed complementary spread.
-/

namespace Purelib.Geometry.Trigonometry.Spread.Triple

variable {K : Type*} [ExplicitField K]

/-- The symmetric triple-spread polynomial in three displayed scalars.

It retains the squared sum, twice the sum of individual squares and four
times the product. Its zero equation defines the displayed spread triple. -/
def TripleSpread.tripleSpreadFunction (a b c : K) : K :=
  (a + b + c) ^ 2 - 2 * (a ^ 2 + b ^ 2 + c ^ 2) - 4 * a * b * c

/-- Three displayed scalars form a spread triple when the triple-spread polynomial vanishes. -/
def TripleSpread.SpreadTriple (a b c : K) : Prop :=
  Geometry.Trigonometry.Spread.Triple.TripleSpread.tripleSpreadFunction a b c = 0

/-- Compute how complementing the third argument changes the triple-spread polynomial.

The complemented value and original value sum to `2(a+b+c) - 2(a²+b²+c²) - 1` over the supplied explicit field (Exercise
12.6). -/
theorem exercise_12_6_identity (a b c : K) :
    Spread.Triple.TripleSpread.tripleSpreadFunction a b (1 - c) =
      2 * (a + b + c) - 2 * (a ^ 2 + b ^ 2 + c ^ 2) - 1 -
        Spread.Triple.TripleSpread.tripleSpreadFunction a b c := by
  unfold Spread.Triple.TripleSpread.tripleSpreadFunction
  ring1

/-- Exercise 12.6, the three complementary triple-spread values agree. -/
theorem exercise_12_6 (a b c : K) :
    Spread.Triple.TripleSpread.tripleSpreadFunction a b (1 - c) =
        Spread.Triple.TripleSpread.tripleSpreadFunction a (1 - b) c ∧
      Spread.Triple.TripleSpread.tripleSpreadFunction a (1 - b) c =
        Spread.Triple.TripleSpread.tripleSpreadFunction (1 - a) b c := by
  constructor <;> unfold Spread.Triple.TripleSpread.tripleSpreadFunction <;> ring1

end Purelib.Geometry.Trigonometry.Spread.Triple

end

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

namespace Purelib.Geometry.Trigonometry.Spread.Triple.Ellipson

section

variable {K : Type*} [ExplicitField K]

/-- The residual of the ellipson's Triple-spread equation. -/
def polynomial (x y z : K) : K :=
  (x + y + z) ^ 2 - 2 * (x ^ 2 + y ^ 2 + z ^ 2) - 4 * x * y * z

/-- The ellipson consists of the zeros of its defining polynomial. -/
def Contains (x y z : K) : Prop :=
  polynomial x y z = 0

/-! ## Symmetry and the tetrahedral cube boundary -/

/-- The defining polynomial is invariant under every permutation of its three coordinates. -/
theorem polynomial_permutations (x y z : K) :
    polynomial x y z = polynomial x z y ∧
      polynomial x y z = polynomial y x z ∧
      polynomial x y z = polynomial y z x ∧
      polynomial x y z = polynomial z x y ∧
      polynomial x y z = polynomial z y x := by
  unfold polynomial
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

/-- Consequently the ellipson has the full coordinate-permutation symmetry visible in its equation. -/
theorem contains_permutations (x y z : K) :
    (Contains x y z ↔ Contains x z y) ∧
      (Contains x y z ↔ Contains y x z) ∧
      (Contains x y z ↔ Contains y z x) ∧
      (Contains x y z ↔ Contains z x y) ∧
      (Contains x y z ↔ Contains z y x) := by
  rcases polynomial_permutations x y z with
    ⟨first, second, third, fourth, fifth⟩
  unfold Contains
  constructor
  · rw [first]
  constructor
  · rw [second]
  constructor
  · rw [third]
  constructor
  · rw [fourth]
  · rw [fifth]
end
end Purelib.Geometry.Trigonometry.Spread.Triple.Ellipson

end

section
@[expose] public section

/-!
# Divine Proportions, Theorem 58: finite reflection chains

The book writes a two-sided infinite reflection sequence.  The constructive
content needed by Theorem 58 is instead an executable finite iterator: after
`n` calls it contains exactly the adjacent pair `(lₙ,lₙ₊₁)`.  No completed
sequence is defined or quantified over.
-/

namespace Purelib.Geometry.Trigonometry.Spread.Triple

variable {K : Type*} [ExplicitField K]

/-- The next entry of a spread triple is one of two explicitly related roots.

The retained previous triple and the sum equation for the two possible
roots factor the candidate's quadratic equation. A zero factor identifies
the candidate with the previous or next root. -/
public theorem
  spreadTriple_recursive_alternatives
  [DecidableEq K]
    (previous current step next candidate : K)
    (previousTriple : Spread.Triple.TripleSpread.SpreadTriple previous step current)
    (candidateTriple : Spread.Triple.TripleSpread.SpreadTriple current step candidate)
    (sumEquation :
      previous + next = 2 * (current + step - 2 * current * step)) :
    candidate = previous ∨ candidate = next := by
  have nextResolved :
      next = 2 * (current + step - 2 * current * step) - previous := by
    calc
      next = previous + next - previous := by ring1
      _ = 2 * (current + step - 2 * current * step) - previous := by
        rw [sumEquation]
  have productZero : (candidate - previous) * (candidate - next) = 0 := by
    rw [nextResolved]
    calc
      (candidate - previous) *
          (candidate -
            (2 * (current + step - 2 * current * step) - previous)) =
        -Spread.Triple.TripleSpread.tripleSpreadFunction current step candidate +
          Spread.Triple.TripleSpread.tripleSpreadFunction previous step current := by
            unfold Spread.Triple.TripleSpread.tripleSpreadFunction
            ring1
      _ = 0 := by
        unfold Spread.Triple.TripleSpread.SpreadTriple at previousTriple candidateTriple
        rw [previousTriple, candidateTriple]
        ring1
  by_cases firstFactorZero : candidate - previous = 0
  · left
    calc
      candidate = (candidate - previous) + previous := by ring1
      _ = previous := by rw [firstFactorZero]; ring1
  · right
    have secondFactorZero : candidate - next = 0 := by
      by_cases factorZero : candidate - next = 0
      · exact factorZero
      · exact False.elim
          ((ExplicitField.mul_ne_zero firstFactorZero factorZero)
            productZero)
    calc
      candidate = (candidate - next) + next := by ring1
      _ = next := by rw [secondFactorZero]; ring1

end Purelib.Geometry.Trigonometry.Spread.Triple

end

section
@[expose] public section

/-!
# Divine Proportions, §7.7: quadruple spread and cross formulas

The scalar elimination is kept separate from the geometric specialization.
Two displayed spread triples give two explicit quadratic equations with a
common root; the finite quadratic-compatibility calculation then yields the
four-variable polynomial.
-/

namespace Purelib.Geometry.Trigonometry.Spread.Triple

variable {K : Type*} [ExplicitField K]

/-- Move the last entry of a spread triple to the first position. -/
public theorem spreadTriple_reorder {a
  b c : K}
    (triple : Spread.Triple.TripleSpread.SpreadTriple a b c) : Spread.Triple.TripleSpread.SpreadTriple c a b := by
  unfold Spread.Triple.TripleSpread.SpreadTriple Spread.Triple.TripleSpread.tripleSpreadFunction at triple ⊢
  calc
    (c + a + b) ^ 2 - 2 * (c ^ 2 + a ^ 2 + b ^ 2) - 4 * c * a * b =
        (a + b + c) ^ 2 - 2 * (a ^ 2 + b ^ 2 + c ^ 2) - 4 * a * b * c := by
          ring1
    _ = 0 := triple

/-- Swapping the last two entries preserves the spread-triple relation. -/
public theorem spreadTriple_swap_last
  {a b c : K}
    (triple : Spread.Triple.TripleSpread.SpreadTriple a b c) : Spread.Triple.TripleSpread.SpreadTriple a c b := by
  unfold Spread.Triple.TripleSpread.SpreadTriple Spread.Triple.TripleSpread.tripleSpreadFunction at triple ⊢
  calc
    (a + c + b) ^ 2 - 2 * (a ^ 2 + c ^ 2 + b ^ 2) - 4 * a * c * b =
        (a + b + c) ^ 2 - 2 * (a ^ 2 + b ^ 2 + c ^ 2) - 4 * a * b * c := by
          ring1
    _ = 0 := triple

end Purelib.Geometry.Trigonometry.Spread.Triple

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 7: the triple spread formula

The proof is performed directly on the six finite line coefficients.  A
single explicit common denominator replaces the book's auxiliary triangle,
and every cancellation is witnessed by the three non-null hypotheses.
-/

namespace Purelib.Geometry.Trigonometry.Spread.Triple

variable {K : Type*} [ExplicitField K]

/-- The spread-triple relation is invariant under swapping its outer entries. -/
theorem spreadTriple_swap_first_third {a b c : K}
    (triple : Spread.Triple.TripleSpread.SpreadTriple a b c) : Spread.Triple.TripleSpread.SpreadTriple c b a := by
  unfold Spread.Triple.TripleSpread.SpreadTriple Spread.Triple.TripleSpread.tripleSpreadFunction at triple ⊢
  calc
    (c + b + a) ^ 2 - 2 * (c ^ 2 + b ^ 2 + a ^ 2) - 4 * c * b * a =
        (a + b + c) ^ 2 - 2 * (a ^ 2 + b ^ 2 + c ^ 2) - 4 * a * b * c := by
      ring1
    _ = 0 := triple

/-- The spread-triple relation is invariant under a cyclic rotation. -/
theorem spreadTriple_rotate {a b c : K}
    (triple : Spread.Triple.TripleSpread.SpreadTriple a b c) : Spread.Triple.TripleSpread.SpreadTriple b c a := by
  unfold Spread.Triple.TripleSpread.SpreadTriple Spread.Triple.TripleSpread.tripleSpreadFunction at triple ⊢
  calc
    (b + c + a) ^ 2 - 2 * (b ^ 2 + c ^ 2 + a ^ 2) - 4 * b * c * a =
        (a + b + c) ^ 2 - 2 * (a ^ 2 + b ^ 2 + c ^ 2) - 4 * a * b * c := by
      ring1
    _ = 0 := triple

/-- The four-by-four determinant displayed in Exercise 7.1, expanded along its first row. -/
def tripleSpreadDeterminant (a b c : K) : K :=
  -a * (a * (0 * 2 - 1 * 1) - c * (b * 2 - 1 * 1) +
      1 * (b * 1 - 0 * 1)) +
    b * (a * (c * 2 - 1 * 1) - 0 * (b * 2 - 1 * 1) +
      1 * (b * 1 - c * 1)) -
    (a * (c * 1 - 0 * 1) - 0 * (b * 1 - 0 * 1) +
      c * (b * 1 - c * 1))

/-- Exercise 7.1: the main polynomial, Archimedes, complement, and determinant forms of the triple-spread function. -/
theorem exercise_7_1 (a b c : K) :
    Spread.Triple.TripleSpread.tripleSpreadFunction a b c =
        QuadTriple.Basic.archimedesFunction a b c - 4 * a * b * c ∧
      Spread.Triple.TripleSpread.tripleSpreadFunction a b c =
        2 * (a * c + b * c + a * b) -
          (a ^ 2 + b ^ 2 + c ^ 2) - 4 * a * b * c ∧
      Spread.Triple.TripleSpread.tripleSpreadFunction a b c =
        4 * (a * b + b * c + c * a) - (a + b + c) ^ 2 -
          4 * a * b * c ∧
      Spread.Triple.TripleSpread.tripleSpreadFunction a b c =
        4 * (1 - a) * (1 - b) * (1 - c) -
          (a + b + c - 2) ^ 2 ∧
      Spread.Triple.TripleSpread.tripleSpreadFunction a b c = -tripleSpreadDeterminant a b c := by
  unfold Spread.Triple.TripleSpread.tripleSpreadFunction QuadTriple.Basic.archimedesFunction
    tripleSpreadDeterminant
  exact ⟨by ring1, by ring1, by ring1, by ring1, by ring1⟩

/-- Expand the triple-spread polynomial into its factored third-argument form.

The identity separates the factor `1-c` and the correction term `c(c-a-b)(1-a-b)`, with no nonzero hypotheses (Exercise
7.2). -/
theorem exercise_7_2 (a b c : K) :
    Spread.Triple.TripleSpread.tripleSpreadFunction a b c =
      ((a + b - c) * c + (c - a + b) * (c - b + a)) * (1 - c) -
        c * (c - (a + b)) * (1 - (a + b)) := by
  unfold Spread.Triple.TripleSpread.tripleSpreadFunction
  ring1

/-- A spread triple with third entry zero has equal first and second entries.

The equivalence includes the converse: every pair of equal field elements completes a spread triple with zero (Exercise
7.3). -/
theorem spreadTriple_zero_iff [DecidableEq K] (a b : K) :
    Spread.Triple.TripleSpread.SpreadTriple a b 0 ↔ a = b := by
  constructor
  · intro triple
    have differenceZero : a - b = 0 := by
      apply ((fun {K : Type _} [ExplicitField K] [DecidableEq K] (value : K) =>
        (Purelib.Algebra.Field.Squares.square_eq_zero_iff (K := K) value : value ^ 2 = 0 ↔ value = 0)) (K := K) (a -
        b)).1
      unfold Spread.Triple.TripleSpread.SpreadTriple at triple
      calc
        (a - b) ^ 2 = -Spread.Triple.TripleSpread.tripleSpreadFunction a b 0 := by
          unfold Spread.Triple.TripleSpread.tripleSpreadFunction
          ring1
        _ = 0 := by rw [triple]; ring1
    calc
      a = (a - b) + b := by ring1
      _ = b := by rw [differenceZero]; ring1
  · intro equal
    unfold Spread.Triple.TripleSpread.SpreadTriple Spread.Triple.TripleSpread.tripleSpreadFunction
    rw [equal]
    ring1

/-- A spread triple with third entry one has complementary first and second entries.

The equivalence includes the converse: two field elements complete a spread triple with one exactly when their sum is
one (Exercise 7.3). -/
theorem spreadTriple_one_iff [DecidableEq K] (a b : K) :
    Spread.Triple.TripleSpread.SpreadTriple a b 1 ↔ a + b = 1 := by
  constructor
  · intro triple
    have differenceZero : a + b - 1 = 0 := by
      apply ((fun {K : Type _} [ExplicitField K] [DecidableEq K] (value : K) =>
        (Purelib.Algebra.Field.Squares.square_eq_zero_iff (K := K) value : value ^ 2 = 0 ↔ value = 0)) (K := K) (a + b -
        1)).1
      unfold Spread.Triple.TripleSpread.SpreadTriple at triple
      calc
        (a + b - 1) ^ 2 = -Spread.Triple.TripleSpread.tripleSpreadFunction a b 1 := by
          unfold Spread.Triple.TripleSpread.tripleSpreadFunction
          ring1
        _ = 0 := by rw [triple]; ring1
    calc
      a + b = (a + b - 1) + 1 := by ring1
      _ = 1 := by rw [differenceZero]; ring1
  · intro sumOne
    unfold Spread.Triple.TripleSpread.SpreadTriple Spread.Triple.TripleSpread.tripleSpreadFunction
    calc
      (a + b + 1) ^ 2 - 2 * (a ^ 2 + b ^ 2 + 1 ^ 2) -
          4 * a * b * 1 = -(a + b - 1) ^ 2 := by ring1
      _ = 0 := by rw [sumOne]; ring1

/-- A spread triple gives the product identity for its three complemented entries.

The square of the coordinate sum minus two equals four times the product of
the three complements. The supplied triple-spread equation vanishes exactly
in the scalar difference between these two displayed expressions. -/
theorem spreadTriple_complement_form {a b c : K}
    (triple : Geometry.Trigonometry.Spread.Triple.TripleSpread.SpreadTriple a b c) :
    (a + b + c - 2) ^ 2 = 4 * (1 - a) * (1 - b) * (1 - c) := by
  have differenceZero :
      4 * (1 - a) * (1 - b) * (1 - c) -
          (a + b + c - 2) ^ 2 = 0 := by
    calc
      4 * (1 - a) * (1 - b) * (1 - c) -
          (a + b + c - 2) ^ 2 = Geometry.Trigonometry.Spread.Triple.TripleSpread.tripleSpreadFunction a b c := by
            exact (exercise_7_1 a b c).2.2.2.1.symm
      _ = 0 := triple
  calc
    (a + b + c - 2) ^ 2 =
        4 * (1 - a) * (1 - b) * (1 - c) -
          (4 * (1 - a) * (1 - b) * (1 - c) -
            (a + b + c - 2) ^ 2) := by ring1
    _ = 4 * (1 - a) * (1 - b) * (1 - c) := by rw [differenceZero]; ring1

/-- The triple-spread equation implies five displayed quadratic identities.

The supplied spread triple determines the normalized quadratic in its third
entry, three translated-coordinate square identities and the square identity
centered at `a+b-2ab`, over the same explicit field. -/
theorem exercise_7_6 {a b c : K} (triple :
  Spread.Triple.TripleSpread.SpreadTriple a b c) :
    c ^ 2 - 2 * c * (a + b - 2 * a * b) + (a - b) ^ 2 = 0 ∧
      (c - a + b) ^ 2 = 4 * (1 - a) * b * c ∧
      (c - b + a) ^ 2 = 4 * a * (1 - b) * c ∧
      (c - a - b) ^ 2 = 4 * a * b * (1 - c) ∧
      (c - (a + b - 2 * a * b)) ^ 2 =
        4 * a * b * (1 - a) * (1 - b) := by
  unfold Spread.Triple.TripleSpread.SpreadTriple at triple
  constructor
  · calc
      c ^ 2 - 2 * c * (a + b - 2 * a * b) + (a - b) ^ 2 =
          -Spread.Triple.TripleSpread.tripleSpreadFunction a b c := by
            unfold Spread.Triple.TripleSpread.tripleSpreadFunction
            ring1
      _ = 0 := by rw [triple]; ring1
  constructor
  · have differenceZero :
        (c - a + b) ^ 2 - 4 * (1 - a) * b * c = 0 := by
      calc
      (c - a + b) ^ 2 - 4 * (1 - a) * b * c =
          -Spread.Triple.TripleSpread.tripleSpreadFunction a b c := by
            unfold Spread.Triple.TripleSpread.tripleSpreadFunction
            ring1
      _ = 0 := by rw [triple]; ring1
    calc
      (c - a + b) ^ 2 =
          ((c - a + b) ^ 2 - 4 * (1 - a) * b * c) +
            4 * (1 - a) * b * c := by ring1
      _ = 4 * (1 - a) * b * c := by rw [differenceZero]; ring1
  constructor
  · have differenceZero :
        (c - b + a) ^ 2 - 4 * a * (1 - b) * c = 0 := by
      calc
      (c - b + a) ^ 2 - 4 * a * (1 - b) * c =
          -Spread.Triple.TripleSpread.tripleSpreadFunction a b c := by
            unfold Spread.Triple.TripleSpread.tripleSpreadFunction
            ring1
      _ = 0 := by rw [triple]; ring1
    calc
      (c - b + a) ^ 2 =
          ((c - b + a) ^ 2 - 4 * a * (1 - b) * c) +
            4 * a * (1 - b) * c := by ring1
      _ = 4 * a * (1 - b) * c := by rw [differenceZero]; ring1
  constructor
  · have differenceZero :
        (c - a - b) ^ 2 - 4 * a * b * (1 - c) = 0 := by
      calc
      (c - a - b) ^ 2 - 4 * a * b * (1 - c) =
          -Spread.Triple.TripleSpread.tripleSpreadFunction a b c := by
            unfold Spread.Triple.TripleSpread.tripleSpreadFunction
            ring1
      _ = 0 := by rw [triple]; ring1
    calc
      (c - a - b) ^ 2 =
          ((c - a - b) ^ 2 - 4 * a * b * (1 - c)) +
            4 * a * b * (1 - c) := by ring1
      _ = 4 * a * b * (1 - c) := by rw [differenceZero]; ring1
  · have differenceZero :
        (c - (a + b - 2 * a * b)) ^ 2 -
          4 * a * b * (1 - a) * (1 - b) = 0 := by
      calc
      (c - (a + b - 2 * a * b)) ^ 2 -
          4 * a * b * (1 - a) * (1 - b) =
        -Spread.Triple.TripleSpread.tripleSpreadFunction a b c := by
          unfold Spread.Triple.TripleSpread.tripleSpreadFunction
          ring1
      _ = 0 := by rw [triple]; ring1
    calc
      (c - (a + b - 2 * a * b)) ^ 2 =
          ((c - (a + b - 2 * a * b)) ^ 2 -
            4 * a * b * (1 - a) * (1 - b)) +
              4 * a * b * (1 - a) * (1 - b) := by ring1
      _ = 4 * a * b * (1 - a) * (1 - b) := by
        rw [differenceZero]
        ring1

/-- Transfer cleared polynomial identities to a common-denominator spread triple.

The denominator must be nonzero; the numerator product and squared-sum identities then give the Triple-spread equation
for the three fractions. -/
public theorem triple_fraction_identity
    (a b c denominator product : K)
    (denominatorNonzero : denominator ≠ 0)
    (productEquation : a * b * c = denominator * product ^ 2)
    (polynomialIdentity :
      (a + b + c) ^ 2 =
        2 * (a ^ 2 + b ^ 2 + c ^ 2) + 4 * product ^ 2) :
    (a / denominator + b / denominator + c / denominator) ^ 2 =
      2 * ((a / denominator) ^ 2 +
        (b / denominator) ^ 2 + (c / denominator) ^ 2) +
      4 * (a / denominator) * (b / denominator) * (c / denominator) := by
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have cubicReduction :
      (a * denominator⁻¹) * (b * denominator⁻¹) *
          (c * denominator⁻¹) =
        product ^ 2 * denominator⁻¹ ^ 2 := by
    calc
      (a * denominator⁻¹) * (b * denominator⁻¹) *
          (c * denominator⁻¹) =
        (a * b * c) * denominator⁻¹ ^ 3 := by ring1
      _ = (denominator * product ^ 2) * denominator⁻¹ ^ 3 := by
        rw [productEquation]
      _ = product ^ 2 * (denominator * denominator⁻¹) *
          denominator⁻¹ ^ 2 := by ring1
      _ = product ^ 2 * denominator⁻¹ ^ 2 := by
        rw [denominatorCancel, mul_one]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    (a * denominator⁻¹ + b * denominator⁻¹ + c * denominator⁻¹) ^ 2 =
        (a + b + c) ^ 2 * denominator⁻¹ ^ 2 := by ring1
    _ =
        (2 * (a ^ 2 + b ^ 2 + c ^ 2) + 4 * product ^ 2) *
          denominator⁻¹ ^ 2 := by rw [polynomialIdentity]
    _ =
        2 * ((a * denominator⁻¹) ^ 2 +
          (b * denominator⁻¹) ^ 2 + (c * denominator⁻¹) ^ 2) +
          4 * (product ^ 2 * denominator⁻¹ ^ 2) := by ring1
    _ =
        2 * ((a * denominator⁻¹) ^ 2 +
          (b * denominator⁻¹) ^ 2 + (c * denominator⁻¹) ^ 2) +
          4 * ((a * denominator⁻¹) * (b * denominator⁻¹) *
            (c * denominator⁻¹)) := by
              rw [cubicReduction]
    _ =
        2 * ((a * denominator⁻¹) ^ 2 +
          (b * denominator⁻¹) ^ 2 + (c * denominator⁻¹) ^ 2) +
          4 * (a * denominator⁻¹) * (b * denominator⁻¹) *
            (c * denominator⁻¹) := by ring1

end Purelib.Geometry.Trigonometry.Spread.Triple

end

section
@[expose] public section

/-!
# Divine Proportions, Theorem 110: cyclic quadrilateral spreads

The six subtended spreads are finite field scalars.  Their four triangle
views are stored as explicit `SpreadTriple` certificates; Theorem 110 is then
exactly two applications of the Two spread triples theorem.

For an actual displayed cyclic quadrilateral on a non-null circle,
`normalizedCyclicSubtendedSpreads` constructs those six scalars as
`Q(A_i,A_j)/(4*K)` and derives every triple certificate from the finite
Subtended spread theorem.  The nonzero circle quadrance is visible because
over a general finite field a null circle can have null chords, for which the
book's spread quotients are not defined.
-/

namespace Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

variable {K : Type*} [ExplicitField K]

section

/-- Swapping the last two entries preserves the spread-triple relation. -/
private theorem spreadTriple_swap_last {a b c : K}
    (triple : Geometry.Trigonometry.Spread.Triple.TripleSpread.SpreadTriple a b c) :
      Geometry.Trigonometry.Spread.Triple.TripleSpread.SpreadTriple a c b := by
  exact Geometry.Trigonometry.Spread.Triple.spreadTriple_rotate
    (Geometry.Trigonometry.Spread.Triple.spreadTriple_rotate
      (Geometry.Trigonometry.Spread.Triple.spreadTriple_swap_first_third triple))
end

end Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

end
