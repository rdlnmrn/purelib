import mathlib.Tactic.QuotientFreeOmega
import DivineProportions.Trigonometry.SpreadCoefficient

/-!
# Divine Proportions, Chapter 8: finite generating prefixes

Exercise 8.10 presents an infinite generating series.  The finite constructive
content is stronger computationally: for every requested cutoff we evaluate
exactly that prefix and exhibit its complete three-term boundary remainder.
The source's rational expression is recovered coefficient-by-coefficient as
the remainder moves strictly beyond the requested prefix; no infinite series
or completed power-series object is introduced.
-/

namespace DivineProportions

/-- The first `count` positive-index spread-polynomial terms, evaluated at a
requested finite indeterminate value `variable`. -/
def spreadGeneratingPrefix
    {R : Type*} [CommRing R]
    (count : Nat) (value indeterminate : R) : R :=
  RFAP.finitePrefixSum count (fun index =>
    spreadPolynomial (index + 1) value * indeterminate ^ (index + 1))

@[simp] theorem spreadGeneratingPrefix_zero
    {R : Type*} [CommRing R] (value indeterminate : R) :
    spreadGeneratingPrefix 0 value indeterminate = 0 := rfl

theorem spreadGeneratingPrefix_succ
    {R : Type*} [CommRing R]
    (count : Nat) (value indeterminate : R) :
    spreadGeneratingPrefix (count + 1) value indeterminate =
      spreadGeneratingPrefix count value indeterminate +
        spreadPolynomial (count + 1) value *
          indeterminate ^ (count + 1) := by
  unfold spreadGeneratingPrefix
  rw [RFAP.finitePrefixSum_succ_last]

/-- The denominator printed in Exercise 8.10. -/
def spreadGeneratingDenominator
    {R : Type*} [CommRing R] (value indeterminate : R) : R :=
  (1 - indeterminate) ^ 3 +
    4 * value * indeterminate * (1 - indeterminate)

/-- Exercise 8.10 as an exact finite identity.  The three displayed boundary
terms are the entire difference between the requested prefix and the book's
formal rational expression. -/
theorem exercise_8_10_finite
    {R : Type*} [CommRing R]
    (count : Nat) (value indeterminate : R) :
    spreadGeneratingDenominator value indeterminate *
        spreadGeneratingPrefix count value indeterminate =
      value * indeterminate * (1 + indeterminate) -
        spreadPolynomial (count + 1) value *
          indeterminate ^ (count + 1) +
        (spreadPolynomial count value +
            spreadPolynomial (count + 1) value - 2 * value) *
          indeterminate ^ (count + 2) -
        spreadPolynomial count value * indeterminate ^ (count + 3) := by
  induction count with
  | zero =>
      simp only [spreadGeneratingPrefix_zero, spreadPolynomial_zero,
        spreadPolynomial_one, zero_mul, mul_zero, zero_add,
        sub_zero, pow_one]
      ring1
  | succ count inductionHypothesis =>
      rw [spreadGeneratingPrefix_succ, mul_add,
        inductionHypothesis]
      rw [show count + 1 + 1 = count + 2 by omega0,
        show count + 1 + 2 = count + 3 by omega0,
        show count + 1 + 3 = count + 4 by omega0]
      rw [spreadPolynomial_succ_succ]
      rw [show indeterminate ^ (count + 2) =
          indeterminate ^ (count + 1) * indeterminate by rw [pow_succ],
        show indeterminate ^ (count + 3) =
          indeterminate ^ (count + 1) * indeterminate ^ 2 by
            rw [show count + 3 = count + 1 + 2 by omega0, pow_add],
        show indeterminate ^ (count + 4) =
          indeterminate ^ (count + 1) * indeterminate ^ 3 by
            rw [show count + 4 = count + 1 + 3 by omega0, pow_add]]
      unfold spreadGeneratingDenominator
      ring1

end DivineProportions
