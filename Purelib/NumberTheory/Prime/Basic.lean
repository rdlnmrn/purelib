module

public import Mathlib.Algebra.Group.Irreducible.Defs
public import Purelib.Algebra.Semiring.Nat
import Purelib.Data.Nat.Divisibility
import Purelib.Data.Nat.Division
public import Purelib.Data.Nat.Parity

/-!
# Primality in the retained natural multiplication structure

The prime predicate uses the original natural multiplication, unit and powers,
with their direct retained monoid certificates. It is the same irreducibility
proposition as natural primality; no alternate natural carrier or factor
algorithm is introduced.
-/

namespace Purelib.NumberTheory

open Purelib.Algebra

/-- A natural prime is irreducible under the original natural multiplication.

The retained monoid has the same executable multiplication, unit and powers
as the original natural parent. Only its structural law certificates determine
this predicate's dependency route. -/
@[expose, reducible] public def Prime (value : Nat) : Prop :=
  @Irreducible Nat Semiring.Nat.monoid value

namespace Prime

open Purelib.Data.Nat

/-- A unit under retained natural multiplication has natural value one.

Its original inverse certifies that its value divides one. Direct natural
mutual divisibility identifies that same value with the natural unit. -/
private theorem unit_eq_one {value : Nat}
    (unit : @IsUnit Nat Semiring.Nat.monoid value) : value = 1 := by
  obtain ⟨retained, equal⟩ := unit
  exact equal.symm.trans (Divisibility.eq_one_of_dvd_one
    ⟨retained.inv, retained.val_inv.symm⟩)

/-- A retained natural prime is at least two.

Zero factors into two copies of itself and one is already a unit. Both
cases contradict the original irreducibility fields; every remaining
natural has two displayed successors. -/
public theorem two_le {value : Nat} (prime : NumberTheory.Prime value) : 2 ≤ value := by
  cases value with
  | zero =>
      cases prime.isUnit_or_isUnit (a := 0) (b := 0) rfl with
      | inl unit => exact (prime.not_isUnit unit).elim
      | inr unit => exact (prime.not_isUnit unit).elim
  | succ value =>
      cases value with
      | zero =>
          exact (prime.not_isUnit
            ⟨{ val := 1, inv := 1, val_inv := rfl, inv_val := rfl }, rfl⟩).elim
      | succ value => exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le value))

/-- A retained natural prime is positive.

Its two-successor lower bound excludes zero. The strict comparison concerns
the same displayed natural and retained prime witness. -/
public theorem pos {value : Nat} (prime : NumberTheory.Prime value) : 0 < value :=
  Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) (two_le prime)

/-- A retained natural prime is greater than one.

The original two-successor lower bound concerns the same natural value
and retained irreducibility witness. Its predecessor comparison excludes
both zero and the multiplicative unit. -/
public theorem one_lt {value : Nat} (prime : NumberTheory.Prime value) : 1 < value :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) (two_le prime)

/-- A retained natural prime is nonzero.

Its same original positive value excludes the zero constructor. The result
uses the retained primality certificate without another divisibility procedure. -/
public theorem ne_zero {value : Nat} (prime : NumberTheory.Prime value) : value ≠ 0 :=
  Nat.ne_of_gt (pos prime)

/-- A retained natural prime is different from one.

Its strict lower bound excludes the multiplicative unit at the same supplied
natural value, without changing the retained irreducibility witness. -/
public theorem ne_one {value : Nat} (prime : NumberTheory.Prime value) : value ≠ 1 :=
  Nat.ne_of_gt (one_lt prime)

/-- A retained natural prime does not divide one.

A divisor of the unit has value one. This contradicts the strict lower bound
of the same supplied prime certificate. -/
public theorem not_dvd_one {value : Nat} (prime : NumberTheory.Prime value) : ¬ value ∣ 1 := by
  intro divides
  exact ne_one prime (Divisibility.eq_one_of_dvd_one divides)

/-- A divisor of a retained natural prime is either one or that same prime.

The supplied original divisibility witness gives a factorization. A unit
left factor is one; a unit right factor is one, retaining and identifying
the original left divisor with the original prime value. -/
public theorem eq_one_or_self_of_dvd {value : Nat} (prime : NumberTheory.Prime value)
    (divisor : Nat) (divides : divisor ∣ value) : divisor = 1 ∨ divisor = value := by
  obtain ⟨factor, equation⟩ := divides
  cases prime.isUnit_or_isUnit equation with
  | inl unit => exact Or.inl (unit_eq_one unit)
  | inr unit =>
      have one := unit_eq_one unit
      cases one
      exact Or.inr ((Nat.mul_one divisor).symm.trans equation.symm)

/-- A natural at least two with only trivial divisors is prime.

The bound excludes the natural unit. Every supplied factorization gives a
left divisor; if it is the original value, positive multiplication
cancellation identifies the original right factor with one. -/
public theorem of_divisors {value : Nat} (atLeastTwo : 2 ≤ value)
    (divisors : ∀ divisor, divisor ∣ value → divisor = 1 ∨ divisor = value) :
    NumberTheory.Prime value := by
  refine ⟨?_, ?_⟩
  · intro unit
    have one := unit_eq_one unit
    cases one
    exact Nat.not_succ_le_self 1 atLeastTwo
  · intro left right equation
    cases divisors left ⟨right, equation⟩ with
    | inl one =>
        cases one
        exact Or.inl
          ⟨{ val := 1, inv := 1, val_inv := rfl, inv_val := rfl }, rfl⟩
    | inr original =>
        cases original
        have positive : 0 < value :=
          Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) atLeastTwo
        have one : right = 1 := Nat.eq_of_mul_eq_mul_left positive
          (equation.symm.trans (Nat.mul_one value).symm)
        cases one
        exact Or.inr
          ⟨{ val := 1, inv := 1, val_inv := rfl, inv_val := rfl }, rfl⟩

/-- A retained natural prime other than two has its original oddness witness.

The original remainder modulo two is either zero or one. A zero remainder
would make two an original divisor, forcing the excluded prime value; a unit
remainder reconstructs the retained half from the original quotient. -/
public theorem odd_of_ne_two {value : Nat} (prime : NumberTheory.Prime value)
    (notTwo : value ≠ 2) : Parity.Odd value := by
  cases Parity.consecutive value with
  | inl even =>
      have divides : 2 ∣ value := Divisibility.of_mod_eq_zero even.1
      cases eq_one_or_self_of_dvd prime 2 divides with
      | inl isOne => exact False.elim (Nat.noConfusion (Nat.succ.inj isOne))
      | inr isValue => exact (notTwo isValue.symm).elim
  | inr odd =>
      refine ⟨value / 2, ?_⟩
      have reconstruct := Division.mod_add_div value 2
      rw [odd.1] at reconstruct
      exact reconstruct.symm.trans (Nat.add_comm _ _)

/-- The product of a finite natural list of primes is positive.

Each supplied prime is positive. Structural multiplication preserves positivity of the exact ordered finite product. -/
public theorem prod_pos {primes : List Nat}
    (primesPrime : ∀ prime ∈ primes, NumberTheory.Prime prime) :
    0 < primes.prod := by
  induction primes with
  | nil => decide
  | cons head tail inductionHypothesis =>
      rw [List.prod_cons]
      exact Nat.mul_pos
        (primesPrime head List.mem_cons_self).pos
        (inductionHypothesis fun prime member =>
          primesPrime prime (List.mem_cons_of_mem head member))

/-- Distinct primes do not divide one another.

The right prime has only its unit and itself as divisors. The left prime is not a unit, and the supplied inequality
excludes the remaining divisor. -/
public theorem not_dvd_of_ne {left right : Nat}
    (leftPrime : NumberTheory.Prime left) (rightPrime : NumberTheory.Prime right)
    (different : left ≠ right) : ¬ left ∣ right := by
  intro divides
  cases rightPrime.eq_one_or_self_of_dvd left divides with
  | inl one => exact leftPrime.ne_one one
  | inr same => exact different same

end Prime
end Purelib.NumberTheory
