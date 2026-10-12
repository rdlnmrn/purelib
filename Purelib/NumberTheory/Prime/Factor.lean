module
import Purelib.Data.List.Membership
import Purelib.Tactic.Ring

public import Purelib.NumberTheory.Prime.Basic
public import Purelib.Data.Nat.Divisibility
public import Purelib.Data.List.Range.Basic
public import Purelib.Data.List.Search
import Purelib.Data.Nat.Coprime.Basic
import Purelib.Data.Nat.GCD.Extended

-- Existing clients retain public access to integer order and cast certificates.
public import Purelib.Data.Int.Order
import Batteries.Data.Nat.Basic
public import Mathlib.Data.Nat.Prime.Defs
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

/-!
# Bounded constructive prime factors

This module returns one prime divisor of a displayed natural number at least
two.  Composite inputs are reduced by an explicit search through
`List.range value`; recursion is on the strictly smaller displayed factor.
It deliberately does not use `Nat.minFac`, whose upstream proof closure
contains choice through the implementation of minimal factors.
-/

@[expose] public section

namespace Purelib.NumberTheory.Prime.Factor

open Purelib.Data.Nat

set_option genInjectivity false in
/-- A retained prime divisor of one displayed natural number.

The original natural factor carries its prime witness and divisibility
witness at the same original source. The primality predicate retains the
original natural multiplication parent and is definitionally natural primality. -/
structure Output (source : Nat) where
  /-- The retained natural prime divisor. -/ factor : Nat
  /-- The retained divisor is prime. -/ factorPrime : NumberTheory.Prime factor
  /-- The retained prime divides the original source natural. -/ factorDivides : factor ∣ source

constructive_injectivity Output

section
open Purelib.NumberTheory
/-- Find one prime divisor using a bounded proper-factor scan and well-founded recursion.

The original range scan accepts the same lower-bound and zero-remainder
Boolean tests. Its first accepted proper factor drives the same recursive
call; an empty scan certifies that the original source itself is prime. -/
def compute : (source : Nat) → 2 ≤ source → Output source :=
  Nat.strongRec (motive := fun source => 2 ≤ source → Output source)
    fun source recurse sourceAtLeastTwo => by
      let acceptedFactor : Nat → Bool := fun factor =>
        decide (2 ≤ factor) && decide (source % factor = 0)
      cases factorFound : (List.range source).find? acceptedFactor with
      | none =>
          have rejected := Data.List.Search.find?_eq_none.mp factorFound
          have sourcePrime : NumberTheory.Prime source := by
            apply Prime.of_divisors sourceAtLeastTwo
            intro divisor divisorDivides
            by_cases divisorOne : divisor = 1
            · exact Or.inl divisorOne
            · by_cases divisorSource : divisor = source
              · exact Or.inr divisorSource
              · have sourcePositive : 0 < source :=
                  Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) sourceAtLeastTwo
                have divisorPositive : 0 < divisor := by
                  cases divisor with
                  | zero =>
                      obtain ⟨factor, equation⟩ := divisorDivides
                      have vanishes : source = 0 := equation.trans (Nat.zero_mul factor)
                      have impossible : 0 < 0 := vanishes ▸ sourcePositive
                      exact (Nat.lt_irrefl 0 impossible).elim
                  | succ divisor => exact Nat.zero_lt_succ divisor
                have divisorAtLeastTwo : 2 ≤ divisor := by
                  cases divisor with
                  | zero => exact (Nat.lt_irrefl 0 divisorPositive).elim
                  | succ divisor =>
                      cases divisor with
                      | zero => exact (divisorOne rfl).elim
                      | succ divisor =>
                          exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le divisor))
                have divisorAtMostSource : divisor ≤ source :=
                  Divisibility.le_of_dvd sourcePositive divisorDivides
                have divisorBelow : divisor < source := by
                  cases Nat.lt_or_eq_of_le divisorAtMostSource with
                  | inl below => exact below
                  | inr equal => exact (divisorSource equal).elim
                have divisorMember : divisor ∈ List.range source :=
                  Data.List.Range.Basic.mem_range.mpr divisorBelow
                have divisorRejected := rejected divisor divisorMember
                have divisorModulo : source % divisor = 0 :=
                  Divisibility.mod_eq_zero_of_dvd divisorDivides
                have divisorAccepted : acceptedFactor divisor = true := by
                  change (decide (2 ≤ divisor) && decide (source % divisor = 0)) = true
                  rewrite [decide_eq_true divisorAtLeastTwo, decide_eq_true divisorModulo]
                  rfl
                rw [divisorAccepted] at divisorRejected
                exact False.elim (Bool.noConfusion divisorRejected)
          exact ⟨source, sourcePrime, Divisibility.refl source⟩
      | some factor =>
          have factorAccepted := Data.List.Search.find?_eq_some_accepts_certificate factorFound
          have factorMember := Data.List.Search.find?_eq_some_mem_certificate factorFound
          have factorConditions : 2 ≤ factor ∧ source % factor = 0 := by
            change (decide (2 ≤ factor) && decide (source % factor = 0)) = true at factorAccepted
            cases atLeastTwo : decide (2 ≤ factor) with
            | false =>
                rw [atLeastTwo] at factorAccepted
                exact Bool.noConfusion factorAccepted
            | true =>
                rw [atLeastTwo] at factorAccepted
                exact ⟨of_decide_eq_true atLeastTwo, of_decide_eq_true factorAccepted⟩
          have factorBelow : factor < source :=
            Data.List.Range.Basic.mem_range.mp factorMember
          have factorDividesSource : factor ∣ source :=
            Divisibility.of_mod_eq_zero factorConditions.2
          let smaller := recurse factor factorBelow factorConditions.1
          exact
            { factor := smaller.factor
              factorPrime := smaller.factorPrime
              factorDivides := Divisibility.trans smaller.factorDivides
                factorDividesSource }

/-- The retained prime factor returned by the bounded search is at least two.

The original output's prime witness excludes zero and one. The bound
concerns that same returned factor, without searching again or choosing
an alternative divisor of the original source. -/
theorem compute_factor_at_least_two (source : Nat)
    (sourceAtLeastTwo : 2 ≤ source) :
    2 ≤ (compute source sourceAtLeastTwo).factor :=
  Prime.two_le (compute source sourceAtLeastTwo).factorPrime

/-! ## Choice-free prime cancellation -/

end

/-- Cancel a displayed factor not divisible by a prime.

The original extended Euclidean result retains integer coefficients for
the prime and left factor. The prime divisor alternative makes their gcd
one, so those same coefficients supply the directed cancellation witness. -/
theorem prime_dvd_right_of_dvd_mul_of_not_dvd
    {prime left right : Nat} (primeIsPrime : NumberTheory.Prime prime)
    (notDividesLeft : ¬ prime ∣ left)
    (dividesProduct : prime ∣ left * right) : prime ∣ right := by
  let result := Data.Nat.GCD.Extended.compute prime left
  have specification := Data.Nat.GCD.Extended.compute_spec prime left
  have gcdAlternative := NumberTheory.Prime.eq_one_or_self_of_dvd primeIsPrime
    result.gcd specification.2.1
  rcases gcdAlternative with gcdOne | gcdPrime
  · let coprime : Data.Nat.Coprime.Basic.CoprimeCertificate prime left :=
      { left := result.left
        right := result.right
        identity := by
          rw [← specification.1, gcdOne]
          rfl }
    apply coprime.dvd_of_dvd_mul_right
    simpa only [Nat.mul_comm] using dividesProduct
  · apply False.elim
    apply notDividesLeft
    rw [← gcdPrime]
    exact specification.2.2

open Purelib.NumberTheory in
/-- A prime detected in the square of one displayed natural already divides that natural.

The original modulo-zero decision supplies the same quotient divisibility
witness when successful. Otherwise the retained nondivisibility certificate
and original square witness force divisibility through prime cancellation. -/
theorem prime_dvd_of_dvd_square {prime value : Nat}
    (primeIsPrime : NumberTheory.Prime prime)
    (dividesSquare : prime ∣ value * value) : prime ∣ value := by
  by_cases modulo : value % prime = 0
  · exact Divisibility.of_mod_eq_zero modulo
  · have notDivides : ¬ prime ∣ value :=
      fun divides => modulo (Divisibility.mod_eq_zero_of_dvd divides)
    exact prime_dvd_right_of_dvd_mul_of_not_dvd primeIsPrime
      notDivides dividesSquare

end Purelib.NumberTheory.Prime.Factor

end

namespace Purelib.NumberTheory.Prime.Factor
open Purelib.NumberTheory
open Purelib.Data.List

/-- A prime absent from a list of primes does not divide its product.

The supplied factor cancellation excludes the current prime head and passes the exact product divisibility witness to
the retained tail. -/
public theorem not_dvd_prod_of_not_mem {prime : Nat}
    (primeIsPrime : NumberTheory.Prime prime) : ∀ {values : List Nat},
    (∀ value ∈ values, NumberTheory.Prime value) → prime ∉ values →
      ¬ prime ∣ values.prod
  | [], _allPrime, _notMember => primeIsPrime.not_dvd_one
  | head :: tail, allPrime, notMember => by
      intro divides
      have primeDifferentHead : prime ≠ head := by
        intro equal
        apply notMember
        exact equal ▸ List.mem_cons_self
      have notDividesHead : ¬ prime ∣ head :=
        Prime.not_dvd_of_ne primeIsPrime
          (allPrime head List.mem_cons_self) primeDifferentHead
      have dividesTail : prime ∣ tail.prod :=
        prime_dvd_right_of_dvd_mul_of_not_dvd
          primeIsPrime notDividesHead (by
            simpa only [List.prod_cons] using divides)
      exact not_dvd_prod_of_not_mem primeIsPrime
        (fun value member =>
          allPrime value (List.mem_cons_of_mem head member))
        (fun member => notMember (List.mem_cons_of_mem head member))
        dividesTail

/-- Remove one prime from a duplicate-free prime product with a cofactor not divisible by it.

The retained membership and primality hypotheses produce the exact factorization witness. -/
public theorem cofactor_of_mem {prime : Nat}
    (primeIsPrime : NumberTheory.Prime prime) : ∀ {values : List Nat},
    values.Nodup → (∀ value ∈ values, NumberTheory.Prime value) →
      prime ∈ values →
      ∃ cofactor : Nat,
        values.prod = prime * cofactor ∧ ¬ prime ∣ cofactor
  | [], _nodup, _allPrime, impossible => by nomatch impossible
  | head :: tail, nodup, allPrime, member => by
      have nodupParts := List.pairwise_cons.mp nodup
      rcases Membership.mem_cons.mp member with equal | tailMember
      · subst head
        refine ⟨tail.prod, rfl, ?_⟩
        apply not_dvd_prod_of_not_mem primeIsPrime
        · intro value valueMember
          exact allPrime value (List.mem_cons_of_mem prime valueMember)
        · intro primeMember
          exact nodupParts.1 prime primeMember rfl
      · rcases cofactor_of_mem primeIsPrime nodupParts.2
          (fun value valueMember =>
            allPrime value (List.mem_cons_of_mem head valueMember))
          tailMember with ⟨cofactor, productEquation, notDividesCofactor⟩
        have primeDifferentHead : prime ≠ head := by
          intro equal
          exact nodupParts.1 prime tailMember equal.symm
        have notDividesHead : ¬ prime ∣ head :=
          Prime.not_dvd_of_ne primeIsPrime
            (allPrime head List.mem_cons_self) primeDifferentHead
        refine ⟨head * cofactor, ?_, ?_⟩
        · simp only [List.prod_cons]
          rw [productEquation]
          ring1
        · intro divides
          have dividesCofactor :=
            prime_dvd_right_of_dvd_mul_of_not_dvd
                primeIsPrime notDividesHead divides
          exact notDividesCofactor dividesCofactor

end Purelib.NumberTheory.Prime.Factor
