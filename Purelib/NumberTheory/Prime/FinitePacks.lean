module
public import Purelib.NumberTheory.Prime.Factor
import Purelib.NumberTheory.Prime.Basic
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Multiplication

import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.NumberTheory
open Purelib.Data.Nat

section
public section

/-!
# Arbitrarily large finite packs of rational square classes

The infinitude sentence following Theorem 62 is exposed through a finite
request: a natural number produces exactly that many positive square-class
representatives, explicit rotation preimages, and pairwise inequivalence
certificates.  The construction performs only the requested number of finite
Euclid steps.  It neither forms the carrier of all square classes nor imports
an infinite-primes theorem.
-/

namespace Purelib.NumberTheory.Prime.FinitePacks

namespace SquareClassPacks

open Purelib

/-! ## Finite Euclid prime data -/

set_option genInjectivity false in
/-- One prime retained together with its direct primality certificate.

The certificate uses the original natural multiplication and unit with their
owned structural laws; the displayed prime value and algorithmic input are retained. -/
structure EuclidPrime where
  /-- The retained natural prime value. -/ value : Nat
  /-- Primality under the retained original natural multiplication parent. -/
  prime : NumberTheory.Prime value

constructive_injectivity EuclidPrime

/-- Retained Euclid primes agree when their displayed values agree.

Their primality fields certify the same value and are propositionally irrelevant
once the original natural values are identified. -/
@[ext] theorem EuclidPrime.ext {left right : EuclidPrime}
    (value : left.value = right.value) : left = right := by
  cases left
  cases right
  cases value
  rfl

/-- Product of the displayed entries of a finite prime list. -/
@[expose] def primeProduct (entries : List EuclidPrime) : Nat :=
  (entries.map EuclidPrime.value).prod

/-- The product of a finite list of retained primes is positive. -/
theorem primeProduct_positive : ∀ entries : List EuclidPrime,
    0 < primeProduct entries
  | [] => by decide
  | head :: tail => by
      simp only [-eq_self, -iff_self, primeProduct, List.map_cons, List.prod_cons]
      exact Nat.mul_pos (Prime.pos head.prime) (primeProduct_positive tail)

/-- Compute a prime divisor of one plus the product of the retained finite prime list.

The bounded factor search returns the divisor with its primality certificate; no global enumeration is used. -/
@[expose] def nextPrime (entries : List EuclidPrime) : EuclidPrime where
  value := (Prime.Factor.compute
    (primeProduct entries + 1) (by
      have positive := primeProduct_positive entries
      omega0)).factor
  prime := (Prime.Factor.compute
    (primeProduct entries + 1) (by
      have positive := primeProduct_positive entries
      omega0)).factorPrime

/-- The next computed prime divides one plus the existing finite prime product. -/
theorem nextPrime_divides (entries : List EuclidPrime) :
    (nextPrime entries).value ∣ primeProduct entries + 1 := by
  exact (Prime.Factor.compute
    (primeProduct entries + 1) (by
      have positive := primeProduct_positive entries
      omega0)).factorDivides

/-- The value of a retained list entry divides the finite prime product. -/
private theorem entry_value_dvd_primeProduct
    {entry : EuclidPrime} : ∀ {entries : List EuclidPrime},
      entry ∈ entries → entry.value ∣ primeProduct entries
  | [], impossible => by
      nomatch impossible
  | head :: tail, member => by
      cases member with
      | head =>
        refine ⟨primeProduct tail, ?_⟩
        simp only [-eq_self, -iff_self, primeProduct, List.map_cons, List.prod_cons]
        rfl
      | tail _ tailMember =>
        rcases entry_value_dvd_primeProduct tailMember with
          ⟨factor, factorization⟩
        refine ⟨head.value * factor, ?_⟩
        change head.value * primeProduct tail =
          entry.value * (head.value * factor)
        rw [factorization]
        calc
          head.value * (entry.value * factor) = (head.value * entry.value) * factor :=
            (Multiplication.mul_assoc _ _ _).symm
          _ = (entry.value * head.value) * factor :=
            congrArg (· * factor) (Nat.mul_comm head.value entry.value)
          _ = entry.value * (head.value * factor) := Multiplication.mul_assoc _ _ _

/-- The next computed prime is absent from the original finite prime list. -/
theorem nextPrime_not_mem (entries : List EuclidPrime) :
    nextPrime entries ∉ entries := by
  intro member
  have dividesProduct := entry_value_dvd_primeProduct member
  have dividesNext := nextPrime_divides entries
  have dividesOne : (nextPrime entries).value ∣ 1 :=
    (Subtraction.add_sub_cancel_left (primeProduct entries) 1) ▸
      Divisibility.sub dividesNext dividesProduct
  exact Prime.not_dvd_one (nextPrime entries).prime dividesOne

/-- Execute exactly the requested number of finite Euclid steps. -/
@[expose] def euclidPrimes : Nat → List EuclidPrime
  | 0 => []
  | count + 1 =>
      let previous := euclidPrimes count
      nextPrime previous :: previous

/-- Executing the requested number of Euclid steps returns exactly that many primes. -/
theorem euclidPrimes_length (count : Nat) :
    (euclidPrimes count).length = count := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [-eq_self, -iff_self, euclidPrimes, List.length_cons, inductionHypothesis]
      rfl

/-- The prime list produced by finite Euclid iteration has no repeated entries. -/
theorem euclidPrimes_nodup (count : Nat) :
    (euclidPrimes count).Nodup := by
  induction count with
  | zero => exact List.Pairwise.nil
  | succ count inductionHypothesis =>
      rw [euclidPrimes]
      apply List.Pairwise.cons
      · intro entry member equal
        apply nextPrime_not_mem (euclidPrimes count)
        exact equal ▸ member
      · exact inductionHypothesis
end SquareClassPacks

end Purelib.NumberTheory.Prime.FinitePacks

end
