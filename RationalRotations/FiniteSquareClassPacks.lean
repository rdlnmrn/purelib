import RationalRotations.RationalSurjectivity
import mathlib.RFAP.ConstructivePrimeFactor

/-!
# Arbitrarily large finite packs of rational square classes

The infinitude sentence following Theorem 62 is exposed through a finite
request: a natural number produces exactly that many positive square-class
representatives, explicit rotation preimages, and pairwise inequivalence
certificates.  The construction performs only the requested number of finite
Euclid steps.  It neither forms the carrier of all square classes nor imports
an infinite-primes theorem.
-/

namespace RationalRotations

namespace FiniteSquareClassPacks

abbrev Scalar := RFAP.ConstructiveFraction.Rational

/-! ## Finite Euclid prime data -/

/-- One prime retained together with its direct primality certificate. -/
@[ext]
structure EuclidPrime where
  value : Nat
  prime : Nat.Prime value

/-- Product of the displayed entries of a finite prime list. -/
def primeProduct (entries : List EuclidPrime) : Nat :=
  (entries.map EuclidPrime.value).prod

theorem primeProduct_positive : ∀ entries : List EuclidPrime,
    0 < primeProduct entries
  | [] => by decide
  | head :: tail => by
      simp only [primeProduct, List.map_cons, List.prod_cons]
      exact Nat.mul_pos head.prime.pos (primeProduct_positive tail)

/-- The next finite Euclid step: take a prime factor of one plus the product
of the already displayed primes.  `Nat.minFac` is an executable bounded
factor search; no global prime enumeration is used. -/
def nextPrime (entries : List EuclidPrime) : EuclidPrime where
  value := (RFAP.ConstructivePrimeFactor.compute
    (primeProduct entries + 1) (by
      have positive := primeProduct_positive entries
      omega0)).factor
  prime := (RFAP.ConstructivePrimeFactor.compute
    (primeProduct entries + 1) (by
      have positive := primeProduct_positive entries
      omega0)).factorPrime

theorem nextPrime_divides (entries : List EuclidPrime) :
    (nextPrime entries).value ∣ primeProduct entries + 1 := by
  exact (RFAP.ConstructivePrimeFactor.compute
    (primeProduct entries + 1) (by
      have positive := primeProduct_positive entries
      omega0)).factorDivides

private theorem entry_value_dvd_primeProduct
    {entry : EuclidPrime} : ∀ {entries : List EuclidPrime},
      entry ∈ entries → entry.value ∣ primeProduct entries
  | [], impossible => by
      nomatch impossible
  | head :: tail, member => by
      rw [List.mem_cons] at member
      rcases member with equal | tailMember
      · subst entry
        refine ⟨primeProduct tail, ?_⟩
        simp only [primeProduct, List.map_cons, List.prod_cons]
      · rcases entry_value_dvd_primeProduct tailMember with
          ⟨factor, factorization⟩
        refine ⟨head.value * factor, ?_⟩
        change head.value * primeProduct tail =
          entry.value * (head.value * factor)
        rw [factorization]
        ring1

theorem nextPrime_not_mem (entries : List EuclidPrime) :
    nextPrime entries ∉ entries := by
  intro member
  have dividesProduct := entry_value_dvd_primeProduct member
  have dividesNext := nextPrime_divides entries
  have dividesOne : (nextPrime entries).value ∣ 1 :=
    (Nat.dvd_add_iff_right dividesProduct).2 dividesNext
  exact (nextPrime entries).prime.not_dvd_one dividesOne

/-- Execute exactly the requested number of finite Euclid steps. -/
def euclidPrimes : Nat → List EuclidPrime
  | 0 => []
  | count + 1 =>
      let previous := euclidPrimes count
      nextPrime previous :: previous

theorem euclidPrimes_length (count : Nat) :
    (euclidPrimes count).length = count := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [euclidPrimes, List.length_cons, inductionHypothesis]

theorem euclidPrimes_nodup (count : Nat) :
    (euclidPrimes count).Nodup := by
  induction count with
  | zero => exact List.Pairwise.nil
  | succ count inductionHypothesis =>
      rw [euclidPrimes]
      apply List.pairwise_cons.mpr
      constructor
      · intro entry member equal
        apply nextPrime_not_mem (euclidPrimes count)
        exact equal ▸ member
      · exact inductionHypothesis

/-! ## Positive square-class entries -/

/-- The positive rational square class represented by one displayed prime. -/
def positivePrimeClass (prime : EuclidPrime) :
    TheoremSixtyTwo.PositiveSquareClassRepresentative where
  representative :=
    { value := (prime.value : Scalar)
      nonzero := (RFAP.ConstructiveFraction.natCast_pos_direct
        prime.prime.pos).ne' }
  positive := RFAP.ConstructiveFraction.natCast_pos_direct prime.prime.pos

/-- One finite square-class entry caches both the positive target and the
explicit four-square preimage produced for it. -/
structure PositiveSquareClassEntry where
  prime : EuclidPrime
  target : TheoremSixtyTwo.PositiveSquareClassRepresentative
  target_eq : target = positivePrimeClass prime
  preimage : NonNullProportion Scalar
  preimage_eq : preimage = TheoremSixtyTwo.preimage
    TheoremSixtyTwo.lagrangeAlgorithm target
  quadranceClass_value : preimage.quadranceClass.value =
    target.representative.value

/-- Construct and retain the four-square preimage of a displayed prime class. -/
def positiveSquareClassEntry (prime : EuclidPrime) :
    PositiveSquareClassEntry where
  prime := prime
  target := positivePrimeClass prime
  target_eq := rfl
  preimage := TheoremSixtyTwo.preimage
    TheoremSixtyTwo.lagrangeAlgorithm (positivePrimeClass prime)
  preimage_eq := rfl
  quadranceClass_value :=
    TheoremSixtyTwo.preimage_quadranceClass
      TheoremSixtyTwo.lagrangeAlgorithm (positivePrimeClass prime)

theorem PositiveSquareClassEntry.target_value
    (entry : PositiveSquareClassEntry) :
    entry.target.representative.value = (entry.prime.value : Scalar) := by
  rw [entry.target_eq]
  rfl

private theorem distinct_primes_not_equivalent
    (left right : EuclidPrime) (different : left ≠ right) :
    ¬ (positivePrimeClass left).representative.Equivalent
      (positivePrimeClass right).representative := by
  intro equivalent
  rcases equivalent with ⟨factor, _factorNonzero, classEquation⟩
  change (right.value : Scalar) =
    factor ^ 2 * (left.value : Scalar) at classEquation
  have primeValuesDifferent : left.value ≠ right.value := by
    intro equal
    apply different
    exact EuclidPrime.ext equal
  let reduced := RFAP.ConstructiveFraction.representative factor
  have cleared := RFAP.ConstructiveFraction.representative_mul_den factor
  change factor * (reduced.den : Scalar) = (reduced.num : Scalar) at cleared
  have rationalEquation :
      (right.value : Scalar) * (reduced.den : Scalar) ^ 2 =
        (reduced.num : Scalar) ^ 2 * (left.value : Scalar) := by
    calc
      (right.value : Scalar) * (reduced.den : Scalar) ^ 2 =
          (factor ^ 2 * (left.value : Scalar)) *
            (reduced.den : Scalar) ^ 2 := by
              rw [classEquation]
      _ = (factor * (reduced.den : Scalar)) ^ 2 *
            (left.value : Scalar) := by ring1
      _ = (reduced.num : Scalar) ^ 2 * (left.value : Scalar) := by
            rw [cleared]
  have integerEquation :
      (right.value : Int) *
          ((reduced.den : Int) * (reduced.den : Int)) =
        (reduced.num * reduced.num) * (left.value : Int) := by
    apply RFAP.ConstructiveFraction.intCast_injective_direct
    rw [RFAP.ConstructiveFraction.intCast_mul_direct,
      RFAP.ConstructiveFraction.intCast_mul_direct,
      RFAP.ConstructiveFraction.intCast_mul_direct,
      RFAP.ConstructiveFraction.intCast_mul_direct]
    simpa only [Int.cast_natCast, pow_two] using rationalEquation
  have absoluteEquation := congrArg Int.natAbs integerEquation
  have naturalEquation :
      right.value * (reduced.den * reduced.den) =
        (reduced.num.natAbs * reduced.num.natAbs) * left.value := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using absoluteEquation
  have leftDividesLeftSide :
      left.value ∣ right.value * (reduced.den * reduced.den) := by
    refine ⟨reduced.num.natAbs * reduced.num.natAbs, ?_⟩
    calc
      right.value * (reduced.den * reduced.den) =
          (reduced.num.natAbs * reduced.num.natAbs) * left.value :=
        naturalEquation
      _ = left.value *
          (reduced.num.natAbs * reduced.num.natAbs) := by ring1
  have leftDoesNotDivideRight : ¬ left.value ∣ right.value := by
    intro divides
    have equal := (Nat.prime_dvd_prime_iff_eq
      left.prime right.prime).mp divides
    exact primeValuesDifferent equal
  have leftDividesDenominatorSquare :
      left.value ∣ reduced.den * reduced.den :=
    RFAP.ConstructivePrimeFactor.prime_dvd_right_of_dvd_mul_of_not_dvd
      left.prime leftDoesNotDivideRight leftDividesLeftSide
  have leftDividesDenominator : left.value ∣ reduced.den :=
    RFAP.ConstructivePrimeFactor.prime_dvd_of_dvd_square left.prime
      leftDividesDenominatorSquare
  rcases leftDividesDenominator with ⟨denominatorFactor,
    denominatorEquation⟩
  have canceledEquation :
      right.value * left.value *
          (denominatorFactor * denominatorFactor) =
        reduced.num.natAbs * reduced.num.natAbs := by
    apply Nat.eq_of_mul_eq_mul_left left.prime.pos
    calc
      left.value *
          (right.value * left.value *
            (denominatorFactor * denominatorFactor)) =
        right.value *
          ((left.value * denominatorFactor) *
            (left.value * denominatorFactor)) := by ring1
      _ = right.value * (reduced.den * reduced.den) := by
        rw [← denominatorEquation]
      _ = (reduced.num.natAbs * reduced.num.natAbs) * left.value :=
        naturalEquation
      _ = left.value *
          (reduced.num.natAbs * reduced.num.natAbs) := by ring1
  have leftDividesNumeratorSquare :
      left.value ∣ reduced.num.natAbs * reduced.num.natAbs := by
    refine ⟨right.value *
      (denominatorFactor * denominatorFactor), ?_⟩
    calc
      reduced.num.natAbs * reduced.num.natAbs =
          right.value * left.value *
            (denominatorFactor * denominatorFactor) :=
        canceledEquation.symm
      _ = left.value *
          (right.value *
            (denominatorFactor * denominatorFactor)) := by ring1
  have leftDividesNumerator : left.value ∣ reduced.num.natAbs :=
    RFAP.ConstructivePrimeFactor.prime_dvd_of_dvd_square left.prime
      leftDividesNumeratorSquare
  rcases reduced.reduced with ⟨coprime⟩
  have leftIsOne := coprime.eq_one_of_dvd
    leftDividesNumerator ⟨denominatorFactor, denominatorEquation⟩
  exact left.prime.ne_one leftIsOne

theorem entries_of_distinct_primes_not_equivalent
    (left right : EuclidPrime) (different : left ≠ right) :
    ¬ (positiveSquareClassEntry left).target.representative.Equivalent
      (positiveSquareClassEntry right).target.representative :=
  distinct_primes_not_equivalent left right different

/-- The complete finite response to one requested cardinality. -/
structure DistinctPositiveSquareClassPack (count : Nat) where
  entries : List PositiveSquareClassEntry
  length_eq : entries.length = count
  pairwiseInequivalent : entries.Pairwise fun left right =>
    ¬ left.target.representative.Equivalent right.target.representative

/-- Produce exactly `count` pairwise inequivalent positive square classes,
each with an executable rotation preimage. -/
def distinctPositiveSquareClassPack (count : Nat) :
    DistinctPositiveSquareClassPack count where
  entries := (euclidPrimes count).map positiveSquareClassEntry
  length_eq := by
    rw [List.length_map, euclidPrimes_length]
  pairwiseInequivalent := by
    rw [QuotientFreeList.pairwise_map]
    apply (euclidPrimes_nodup count).imp
    intro left right different
    exact entries_of_distinct_primes_not_equivalent left right different

theorem distinctPositiveSquareClassPack_entry_realizes
    (count : Nat) (entry : PositiveSquareClassEntry)
    (_member : entry ∈ (distinctPositiveSquareClassPack count).entries) :
    entry.preimage.quadranceClass.value =
      entry.target.representative.value :=
  entry.quadranceClass_value

end FiniteSquareClassPacks

end RationalRotations
