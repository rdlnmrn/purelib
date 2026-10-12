module
public import Purelib.NumberTheory.Prime.Factor
public import Purelib.Data.Int.Division

public import Purelib.Data.Nat.Division
public import Purelib.Algebra.Semiring.Normalization
import Purelib.Algebra.Semiring.Nat
import Purelib.Data.Nat.Divisibility
import Purelib.Data.Nat.Multiplication
import Purelib.Data.Nat.Parity
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.NumberTheory
open Purelib.Data.Nat
open Purelib.Algebra

/-!
# Constructive prime-parity decompositions

This module factors one supplied positive natural only as far as that finite
input requires.  A displayed prime is divided out completely by well-founded
recursion, and the outer decomposition retains exactly the primes having odd
exponent.  The result caches a square root and the identity
`source = root^2 * primes.prod`; it forms no global prime enumeration or
factorization object.
-/

public section

namespace Purelib.NumberTheory.Prime.Parity

attribute [local instance high] Semiring.Nat.commSemiring
attribute [local instance high] CommSemiring.toSemiring Semiring.toMonoid
attribute [local instance high] Monoid.toSemigroup Divisibility.decidable

set_option genInjectivity false in
/-- Complete extraction of one displayed prime power.

The extracted exponent and positive remainder retain their equation with
that same source. The remainder has no further occurrence of the supplied
prime, and a divisible source has a positive extracted exponent. -/
structure PrimePowerSplit (prime source : Nat) where
  /-- The extracted exponent of the supplied prime. -/ exponent : Nat
  /-- The retained positive remainder after removing that prime power. -/ remainder : Nat
  /-- The original source is the extracted prime power times the retained remainder. -/ equation : source = prime ^
    exponent * remainder
  /-- The retained remainder is positive. -/ remainder_positive : 0 < remainder
  /-- The supplied prime no longer divides the retained remainder. -/ not_dvd_remainder : ¬ prime ∣ remainder
  /-- Divisibility of the original source forces a positive extracted exponent. -/ exponent_positive_of_dvd : prime ∣
    source → 0 < exponent

constructive_injectivity PrimePowerSplit

/-- Divide out every occurrence of one displayed prime.

Each successful divisibility decision recurses on the original quotient
of the same positive source. Its exponent increases once while the
retained remainder and its certificates come from that quotient run. -/
@[expose] def primePowerSplit (prime : Nat) (primeIsPrime : NumberTheory.Prime prime) :
    (source : Nat) → 0 < source → PrimePowerSplit prime source :=
  Nat.strongRec (motive := fun source =>
    0 < source → PrimePowerSplit prime source)
    fun source recurse sourcePositive => by
      by_cases divides : prime ∣ source
      · let quotient := source / prime
        have primePositive : 0 < prime := primeIsPrime.pos
        have primeAtMostSource : prime ≤ source :=
          Divisibility.le_of_dvd sourcePositive divides
        have quotientPositive : 0 < quotient := by
          unfold quotient
          exact Division.div_pos primeAtMostSource primePositive
        have quotientBelow : quotient < source := by
          unfold quotient
          exact Division.div_lt_self sourcePositive primeIsPrime.one_lt
        let previous := recurse quotient quotientBelow quotientPositive
        have sourceEquation : source = prime * quotient := by
          exact (Division.div_mul_cancel divides).symm.trans
            (Nat.mul_comm quotient prime)
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
            exponent_positive_of_dvd := fun _ => Nat.zero_lt_succ _ }
      · exact
          { exponent := 0
            remainder := source
            equation := (Nat.one_mul source).symm
            remainder_positive := sourcePositive
            not_dvd_remainder := divides
            exponent_positive_of_dvd := fun sourceDivides =>
              (divides sourceDivides).elim }

set_option genInjectivity false in
/-- A finite square-free kernel decomposition of one positive natural.

The retained root and ordered list of distinct prime support entries
satisfy the original square-times-product equation. Their correctness
certificates concern that exact source and the same natural operations. -/
structure Decomposition (source : Nat) where
  /-- The retained natural root of the square factor. -/ root : Nat
  /-- The retained primes with odd exponent in the source. -/ primes : List Nat
  /-- Every retained support entry is prime. -/ primes_prime : ∀ prime ∈ primes, NumberTheory.Prime prime
  /-- The retained prime support has no repeated entries. -/ primes_nodup : primes.Nodup
  /-- The original source is the retained root squared times the support product. -/ equation : source = root ^ 2 *
    primes.prod

constructive_injectivity Decomposition

/-- Compute the odd-prime support and complementary square root of a positive natural.

The original least-factor selection and complete prime-power extraction
recurse on successively smaller retained remainders. The half exponent
and its parity choose the same ordered support list and cached root. -/
@[expose] def decompose : (source : Nat) → 0 < source → Decomposition source :=
  Nat.strongRec (motive := fun source => 0 < source → Decomposition source)
    fun source recurse sourcePositive => by
      by_cases sourceOne : source = 1
      · subst source
        exact
          { root := 1
            primes := []
            primes_prime := by intro prime member; nomatch member
            primes_nodup := List.Pairwise.nil
            equation := rfl }
      · have sourceAtLeastTwo : 2 ≤ source :=
          Nat.succ_le_of_lt (Nat.lt_of_le_of_ne
            (Nat.succ_le_of_lt sourcePositive) (Ne.symm sourceOne))
        let selected := Prime.Factor.compute source
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
            calc
              split.exponent = split.exponent % 2 + 2 * (split.exponent / 2) :=
                (Division.mod_add_div split.exponent 2).symm
              _ = 2 * half := by rw [exponentEven, Nat.zero_add]
          have evenPower : selected.factor ^ (2 * half) =
              (selected.factor ^ half) ^ 2 :=
            Semiring.Normalization.pow_bit0 rfl (Multiplication.pow_two _).symm
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
                    rw [exponentEquation, evenPower]
                    ring1 }
        · have exponentRemainder : split.exponent % 2 = 1 := by
            cases Parity.consecutive split.exponent with
            | inl even => exact (exponentEven even.1).elim
            | inr odd => exact odd.1
          have exponentEquation : split.exponent = 2 * half + 1 := by
            calc
              split.exponent = split.exponent % 2 + 2 * (split.exponent / 2) :=
                (Division.mod_add_div split.exponent 2).symm
              _ = 2 * half + 1 := by rw [exponentRemainder, Nat.add_comm]
          have oddPower : selected.factor ^ (2 * half + 1) =
              selected.factor * (selected.factor ^ half) ^ 2 :=
            Semiring.Normalization.pow_bit1 rfl
              (Multiplication.pow_two _).symm (Nat.mul_comm _ _)
          have factorNotMember : selected.factor ∉ previous.primes := by
            intro member
            have factorDividesProduct := Divisibility.mem_dvd_prod member
            have productDividesRemainder : previous.primes.prod ∣
                split.remainder := by
              refine ⟨previous.root ^ 2, ?_⟩
              calc
                split.remainder = previous.root ^ 2 *
                    previous.primes.prod := previous.equation
                _ = previous.primes.prod * previous.root ^ 2 := by ring1
            exact split.not_dvd_remainder
              (Divisibility.trans factorDividesProduct productDividesRemainder)
          exact
            { root := selected.factor ^ half * previous.root
              primes := selected.factor :: previous.primes
              primes_prime := by
                intro prime member
                cases member with
                | head => exact selected.factorPrime
                | tail _ tailMember => exact previous.primes_prime prime tailMember
              primes_nodup := by
                exact List.Pairwise.cons
                  (fun prime member equal => factorNotMember (equal ▸ member))
                  previous.primes_nodup
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
                    rw [exponentEquation, oddPower, List.prod_cons]
                    ring1 }

/-- Read the square-free odd-prime kernel of one displayed natural.

The original positive-input decision runs the retained decomposition and
reads its support product. The zero input retains the original zero
outcome without starting a factorization. -/
@[expose] def oddPrimeKernel (source : Nat) : Nat :=
  if sourcePositive : 0 < source then
    (decompose source sourcePositive).primes.prod
  else
    0

/-- A positive input reads the product of its retained prime-parity support.

The original positive branch selects exactly the decomposition of that
same source. Its retained ordered support supplies the kernel readback. -/
theorem oddPrimeKernel_of_positive (source : Nat) (sourcePositive : 0 < source) :
    oddPrimeKernel source = (decompose source sourcePositive).primes.prod := by
  unfold oddPrimeKernel
  exact dif_pos sourcePositive

end Purelib.NumberTheory.Prime.Parity

end
