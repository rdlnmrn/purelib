import mathlib.RFAP.ConstructivePrimeFactor
import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# Constructive prime-parity decompositions

This module factors one supplied positive natural only as far as that finite
input requires.  A displayed prime is divided out completely by well-founded
recursion, and the outer decomposition retains exactly the primes having odd
exponent.  The result caches a square root and the identity
`source = root^2 * primes.prod`; it forms no global prime enumeration or
factorization object.
-/

namespace RFAP.ConstructivePrimeParity

/-- Complete extraction of one displayed prime power. -/
structure PrimePowerSplit (prime source : Nat) where
  exponent : Nat
  remainder : Nat
  equation : source = prime ^ exponent * remainder
  remainder_positive : 0 < remainder
  not_dvd_remainder : ¬ prime ∣ remainder
  exponent_positive_of_dvd : prime ∣ source → 0 < exponent

/-- Divide out every occurrence of one displayed prime. -/
def primePowerSplit (prime : Nat) (primeIsPrime : Nat.Prime prime) :
    (source : Nat) → 0 < source → PrimePowerSplit prime source :=
  Nat.strongRec (motive := fun source =>
    0 < source → PrimePowerSplit prime source)
    fun source recurse sourcePositive => by
      by_cases divides : prime ∣ source
      · let quotient := source / prime
        have primePositive : 0 < prime := primeIsPrime.pos
        have primeAtMostSource : prime ≤ source :=
          Nat.le_of_dvd sourcePositive divides
        have quotientPositive : 0 < quotient := by
          unfold quotient
          exact Nat.div_pos primeAtMostSource primePositive
        have quotientBelow : quotient < source := by
          unfold quotient
          exact Nat.div_lt_self sourcePositive primeIsPrime.one_lt
        let previous := recurse quotient quotientBelow quotientPositive
        have sourceEquation : source = prime * quotient := by
          exact (Nat.mul_div_cancel' divides).symm
        exact
          { exponent := previous.exponent + 1
            remainder := previous.remainder
            equation := by
              calc
                source = prime * quotient := sourceEquation
                _ = prime *
                    (prime ^ previous.exponent * previous.remainder) := by
                  exact congrArg (fun value : Nat => prime * value)
                    previous.equation
                _ = prime ^ (previous.exponent + 1) *
                    previous.remainder := by
                  rw [Nat.pow_succ]
                  ring1
            remainder_positive := previous.remainder_positive
            not_dvd_remainder := previous.not_dvd_remainder
            exponent_positive_of_dvd := fun _ => by omega0 }
      · exact
          { exponent := 0
            remainder := source
            equation := by simp only [Nat.pow_zero, Nat.one_mul]
            remainder_positive := sourcePositive
            not_dvd_remainder := divides
            exponent_positive_of_dvd := fun sourceDivides =>
              (divides sourceDivides).elim }

/-- A finite square-free kernel decomposition of one positive natural. -/
structure Decomposition (source : Nat) where
  root : Nat
  primes : List Nat
  primes_prime : ∀ prime ∈ primes, Nat.Prime prime
  primes_nodup : primes.Nodup
  equation : source = root ^ 2 * primes.prod

private theorem mem_dvd_prod {prime : Nat} : ∀ {values : List Nat},
    prime ∈ values → prime ∣ values.prod
  | [], impossible => by nomatch impossible
  | head :: tail, member => by
      rw [List.mem_cons] at member
      rcases member with equal | tailMember
      · subst head
        exact ⟨tail.prod, by simp only [List.prod_cons]⟩
      · rcases mem_dvd_prod tailMember with ⟨factor, equation⟩
        refine ⟨head * factor, ?_⟩
        simp only [List.prod_cons]
        rw [equation]
        ring1

private theorem pow_even (base half : Nat) :
    base ^ (2 * half) = (base ^ half) ^ 2 := by
  rw [show 2 * half = half * 2 by omega0, Nat.pow_mul]

private theorem pow_odd (base half : Nat) :
    base ^ (2 * half + 1) = base * (base ^ half) ^ 2 := by
  rw [Nat.pow_succ, pow_even]
  ring1

/-- Compute the odd-prime support and the complementary square root of one
positive natural by factoring only successively smaller displayed
remainders. -/
def decompose : (source : Nat) → 0 < source → Decomposition source :=
  Nat.strongRec (motive := fun source => 0 < source → Decomposition source)
    fun source recurse sourcePositive => by
      by_cases sourceOne : source = 1
      · subst source
        exact
          { root := 1
            primes := []
            primes_prime := by intro prime member; nomatch member
            primes_nodup := List.Pairwise.nil
            equation := by decide }
      · have sourceAtLeastTwo : 2 ≤ source := by omega0
        let selected := RFAP.ConstructivePrimeFactor.compute source
          sourceAtLeastTwo
        let split := primePowerSplit selected.factor selected.factorPrime
          source sourcePositive
        have selectedDivides : selected.factor ∣ source :=
          selected.factorDivides
        have exponentPositive : 0 < split.exponent :=
          split.exponent_positive_of_dvd selectedDivides
        have primePowerAtLeastTwo : 2 ≤ selected.factor ^ split.exponent := by
          have factorLePower : selected.factor ≤
              selected.factor ^ split.exponent := by
            obtain ⟨power, powerEquation⟩ :=
              Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt exponentPositive)
            rw [powerEquation, Nat.pow_succ]
            exact Nat.le_mul_of_pos_left selected.factor
              (Nat.pow_pos selected.factorPrime.pos)
          exact selected.factorPrime.two_le.trans factorLePower
        have remainderBelow : split.remainder < source := by
          have strictProduct : split.remainder <
              selected.factor ^ split.exponent * split.remainder := by
            simpa only [Nat.one_mul] using
              Nat.mul_lt_mul_of_pos_right
                (Nat.lt_of_lt_of_le Nat.one_lt_two primePowerAtLeastTwo)
                split.remainder_positive
          rw [← split.equation] at strictProduct
          exact strictProduct
        let previous := recurse split.remainder remainderBelow
          split.remainder_positive
        let half := split.exponent / 2
        by_cases exponentEven : split.exponent % 2 = 0
        · have exponentEquation : split.exponent = 2 * half := by
            unfold half
            omega0
          exact
            { root := selected.factor ^ half * previous.root
              primes := previous.primes
              primes_prime := previous.primes_prime
              primes_nodup := previous.primes_nodup
              equation := by
                calc
                  source = selected.factor ^ split.exponent *
                      split.remainder := split.equation
                  _ = selected.factor ^ split.exponent *
                      (previous.root ^ 2 * previous.primes.prod) := by
                    exact congrArg
                      (fun value : Nat =>
                        selected.factor ^ split.exponent * value)
                      previous.equation
                  _ = (selected.factor ^ half * previous.root) ^ 2 *
                      previous.primes.prod := by
                    rw [exponentEquation, pow_even]
                    ring1 }
        · have exponentEquation : split.exponent = 2 * half + 1 := by
            unfold half
            omega0
          have factorNotMember : selected.factor ∉ previous.primes := by
            intro member
            have factorDividesProduct := mem_dvd_prod member
            have productDividesRemainder : previous.primes.prod ∣
                split.remainder := by
              refine ⟨previous.root ^ 2, ?_⟩
              calc
                split.remainder = previous.root ^ 2 *
                    previous.primes.prod := previous.equation
                _ = previous.primes.prod * previous.root ^ 2 := by ring1
            exact split.not_dvd_remainder
              (dvd_trans factorDividesProduct productDividesRemainder)
          exact
            { root := selected.factor ^ half * previous.root
              primes := selected.factor :: previous.primes
              primes_prime := by
                intro prime member
                rw [List.mem_cons] at member
                rcases member with equal | tailMember
                · exact equal ▸ selected.factorPrime
                · exact previous.primes_prime prime tailMember
              primes_nodup := by
                exact List.pairwise_cons.mpr
                  ⟨(fun prime member equal =>
                    factorNotMember (equal ▸ member)),
                    previous.primes_nodup⟩
              equation := by
                calc
                  source = selected.factor ^ split.exponent *
                      split.remainder := split.equation
                  _ = selected.factor ^ split.exponent *
                      (previous.root ^ 2 * previous.primes.prod) := by
                    exact congrArg
                      (fun value : Nat =>
                        selected.factor ^ split.exponent * value)
                      previous.equation
                  _ = (selected.factor ^ half * previous.root) ^ 2 *
                      (selected.factor :: previous.primes).prod := by
                    rw [exponentEquation, pow_odd, List.prod_cons]
                    ring1 }

/-- The square-free odd-prime kernel of one displayed natural.  Zero is
returned only for the zero input; positive inputs execute `decompose`. -/
def oddPrimeKernel (source : Nat) : Nat :=
  if sourcePositive : 0 < source then
    (decompose source sourcePositive).primes.prod
  else
    0

theorem oddPrimeKernel_of_positive (source : Nat) (sourcePositive : 0 < source) :
    oddPrimeKernel source = (decompose source sourcePositive).primes.prod := by
  simp only [oddPrimeKernel, dif_pos sourcePositive]

end RFAP.ConstructivePrimeParity
