import mathlib.Data.ConstructiveList
import mathlib.RFAP.CanonicalGCD
import mathlib.Tactic.QuotientFreeOmega
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.MinimalAxioms
import Init.GrindInstances.Ring.Fin

/-!
# Constructive four-square arithmetic

This file develops the finite residue search and descent needed for
Lagrange's four-square theorem.  It deliberately avoids Mathlib's
`NumberTheory.SumFourSquares` route, whose prime seed is obtained through
classical finite-field cardinality.  Every search here ranges over displayed
lists or bounded natural data.
-/

namespace RFAP.ConstructiveFourSquares

private theorem find?_eq_some_accepts {Alpha : Type*}
    {predicate : Alpha → Bool} {target : Alpha} :
    ∀ {values : List Alpha},
      values.find? predicate = some target → predicate target = true
  | [], impossible => by
      nomatch impossible
  | head :: tail, found => by
      cases accepted : predicate head with
      | false =>
          rw [List.find?_cons, accepted] at found
          exact find?_eq_some_accepts found
      | true =>
          rw [List.find?_cons, accepted] at found
          injection found with equal
          exact equal ▸ accepted

private theorem find?_eq_some_mem {Alpha : Type*}
    {predicate : Alpha → Bool} {target : Alpha} :
    ∀ {values : List Alpha}, values.find? predicate = some target →
      target ∈ values
  | [], impossible => by
      nomatch impossible
  | head :: tail, found => by
      cases accepted : predicate head with
      | false =>
          rw [List.find?_cons, accepted] at found
          exact List.mem_cons_of_mem head (find?_eq_some_mem found)
      | true =>
          rw [List.find?_cons, accepted] at found
          injection found with equal
          exact equal ▸ List.mem_cons_self

private theorem nodup_ofFn_of_injective {Alpha : Type*} {size : Nat}
    {function : Fin size → Alpha} (injective : Function.Injective function) :
    (List.ofFn function).Nodup := by
  induction size with
  | zero =>
      rw [List.ofFn_zero]
      exact List.Pairwise.nil
  | succ size inductionHypothesis =>
      rw [QuotientFreeList.ofFn_succ]
      apply List.pairwise_cons.mpr
      constructor
      · intro value member equal
        rw [List.mem_ofFn] at member
        rcases member with ⟨index, valueEqual⟩
        have impossible : (0 : Fin (size + 1)) = index.succ :=
          injective (equal.trans valueEqual.symm)
        exact Fin.succ_ne_zero index impossible.symm
      · apply inductionHypothesis
        intro left right equal
        have equalSuccessors : left.succ = right.succ := injective equal
        apply Fin.ext
        exact Nat.succ.inj (congrArg Fin.val equalSuccessors)

private theorem fin_zero_add {prime : Nat} [NeZero prime]
    (value : Fin prime) : 0 + value = value := by
  rw [Lean.Grind.Fin.add_comm]
  exact Lean.Grind.Fin.add_zero value

private theorem fin_one_mul {prime : Nat} [NeZero prime]
    (value : Fin prime) : 1 * value = value := by
  rw [Lean.Grind.Fin.mul_comm]
  exact Lean.Grind.Fin.mul_one value

/-- The core modular operations, equipped locally with the ordinary
commutative-ring laws proved directly in Lean's finite residue model. -/
@[reducible] private def finCommRing
    (prime : Nat) [NeZero prime] : CommRing (Fin prime) :=
  CommRing.ofMinimalAxioms
    Lean.Grind.Fin.add_assoc fin_zero_add Lean.Grind.Fin.neg_add_cancel
    Lean.Grind.Fin.mul_assoc Lean.Grind.Fin.mul_comm fin_one_mul
    Lean.Grind.Fin.left_distrib

local instance (prime : Nat) [NeZero prime] : CommRing (Fin prime) :=
  finCommRing prime

/-- A natural number together with four displayed square roots. -/
structure Representation (value : Nat) where
  first : Nat
  second : Nat
  third : Nat
  fourth : Nat
  equation : first ^ 2 + second ^ 2 + third ^ 2 + fourth ^ 2 = value

private theorem halfCount_le_prime {prime : Nat}
    (primePositive : 0 < prime) : (prime + 1) / 2 ≤ prime := by
  omega

private theorem odd_halfCount (prime : Nat) (primeOdd : Odd prime) :
    (prime + 1) / 2 + (prime + 1) / 2 = prime + 1 := by
  rcases primeOdd with ⟨half, equation⟩
  omega

private theorem finPrime_mul_eq_zero
    (prime : Nat) [NeZero prime] (primeIsPrime : Nat.Prime prime)
    (left right : Fin prime) (productZero : left * right = 0) :
    left = 0 ∨ right = 0 := by
  have valueZero := congrArg Fin.val productZero
  change (left.val * right.val) % prime = 0 at valueZero
  have primeDivides : prime ∣ left.val * right.val :=
    Nat.dvd_of_mod_eq_zero valueZero
  by_cases leftDivides : prime ∣ left.val
  · left
    apply Fin.ext
    exact Nat.eq_zero_of_dvd_of_lt leftDivides left.isLt
  · right
    let gcdResult := RFAP.CanonicalGCD.compute prime left.val
    have gcdSpecification := RFAP.CanonicalGCD.compute_spec prime left.val
    have gcdEqualsOne : gcdResult.gcd = 1 := by
      rcases primeIsPrime.eq_one_or_self_of_dvd gcdResult.gcd
          gcdSpecification.2.1 with equalsOne | equalsPrime
      · exact equalsOne
      · have primeDividesLeft : prime ∣ left.val := by
          change (RFAP.CanonicalGCD.compute prime left.val).gcd = prime at equalsPrime
          simpa only [equalsPrime] using gcdSpecification.2.2
        exact False.elim (leftDivides primeDividesLeft)
    let certificate : RFAP.CanonicalGCD.CoprimeCertificate prime left.val :=
      { left := gcdResult.left
        right := gcdResult.right
        identity := by
          rw [← gcdSpecification.1, gcdEqualsOne]
          rfl }
    have reorderedDivides : prime ∣ right.val * left.val := by
      simpa only [Nat.mul_comm] using primeDivides
    have rightDivides : prime ∣ right.val :=
      certificate.dvd_of_dvd_mul_right reorderedDivides
    apply Fin.ext
    exact Nat.eq_zero_of_dvd_of_lt rightDivides right.isLt

private theorem nat_lt_of_mul_lt_mul_right
    {left right factor : Nat} (productLess : left * factor < right * factor) :
    left < right := by
  by_contra notLess
  have rightLeLeft : right ≤ left := by omega
  have productLe := Nat.mul_le_mul_right factor rightLeLeft
  exact (Nat.not_lt_of_ge productLe) productLess

private theorem nat_dvd_of_int_natCast_dvd
    {divisor value : Nat} (divisorPositive : 0 < divisor)
    (integerDivides : (divisor : Int) ∣ (value : Int)) :
    divisor ∣ value := by
  rcases integerDivides with ⟨factor, factorEquation⟩
  have factorNonnegative : 0 ≤ factor := by
    by_contra factorNotNonnegative
    have factorNegative : factor < 0 := by omega
    have productNegative : (divisor : Int) * factor < 0 :=
      Int.mul_neg_of_pos_of_neg (Int.natCast_pos.mpr divisorPositive)
        factorNegative
    rw [← factorEquation] at productNegative
    exact (Int.not_lt_of_ge (Int.natCast_nonneg value)) productNegative
  refine ⟨factor.toNat, ?_⟩
  apply Int.natCast_inj.mp
  calc
    (value : Int) = (divisor : Int) * factor := factorEquation
    _ = (divisor : Int) * (factor.toNat : Int) := by
      rw [Int.toNat_of_nonneg factorNonnegative]
    _ = ((divisor * factor.toNat : Nat) : Int) := by
      rw [Int.ofNat_mul_ofNat]

private def smallRoot (prime : Nat) (primePositive : 0 < prime)
    (index : Fin ((prime + 1) / 2)) : Fin prime :=
  ⟨index.val, index.isLt.trans_le (halfCount_le_prime primePositive)⟩

private theorem smallRoot_value (prime : Nat)
    (primePositive : 0 < prime) (index : Fin ((prime + 1) / 2)) :
    (smallRoot prime primePositive index).val = index.val := rfl

/-- The square map is injective on the displayed representatives
`0, ..., (p-1)/2` for an odd prime. -/
private theorem smallSquare_injective
    (prime : Nat) [NeZero prime] (primeIsPrime : Nat.Prime prime)
    (primeOdd : Odd prime) :
    Function.Injective (fun index : Fin ((prime + 1) / 2) =>
      smallRoot prime primeIsPrime.pos index ^ 2) := by
  intro left right equalSquares
  let leftRoot := smallRoot prime primeIsPrime.pos left
  let rightRoot := smallRoot prime primeIsPrime.pos right
  have equalRootSquares : leftRoot ^ 2 = rightRoot ^ 2 := by
    exact equalSquares
  have productZero :
      (leftRoot + -rightRoot) * (leftRoot + rightRoot) = 0 := by
    calc
      (leftRoot + -rightRoot) * (leftRoot + rightRoot) =
          leftRoot ^ 2 + -(rightRoot ^ 2) := by ring1
      _ = 0 := by
        rw [equalRootSquares, add_neg_cancel]
  rcases finPrime_mul_eq_zero prime primeIsPrime _ _ productZero with
      differenceZero | sumZero
  · have rootsEqual : leftRoot = rightRoot := by
      calc
        leftRoot = leftRoot + 0 := by rw [add_zero]
        _ = leftRoot + (-rightRoot + rightRoot) := by
          rw [neg_add_cancel]
        _ = (leftRoot + -rightRoot) + rightRoot := by
          rw [add_assoc]
        _ = rightRoot := by rw [differenceZero, zero_add]
    apply Fin.ext
    have valuesEqual := congrArg Fin.val rootsEqual
    change left.val = right.val
    simpa only [leftRoot, rightRoot, smallRoot_value prime primeIsPrime.pos]
      using valuesEqual
  · have sumBelow : left.val + right.val < prime := by
      have count := odd_halfCount prime primeOdd
      omega
    have valuesZero := congrArg Fin.val sumZero
    rw [Fin.val_add, smallRoot_value prime primeIsPrime.pos,
      smallRoot_value prime primeIsPrime.pos,
      Nat.mod_eq_of_lt sumBelow] at valuesZero
    have coordinatesZero : left.val = 0 ∧ right.val = 0 :=
      Nat.add_eq_zero_iff.mp valuesZero
    exact Fin.ext (coordinatesZero.1.trans coordinatesZero.2.symm)

/-- The duplicate-free list of small square residues modulo `prime`. -/
private def primeSquareValues (prime : Nat) [NeZero prime]
    (primePositive : 0 < prime) :
    List (Fin prime) :=
  List.ofFn (fun index : Fin ((prime + 1) / 2) =>
    smallRoot prime primePositive index ^ 2)

private theorem primeSquareValues_nodup
    (prime : Nat) [NeZero prime] (primeIsPrime : Nat.Prime prime)
    (primeOdd : Odd prime) :
    (primeSquareValues prime primeIsPrime.pos).Nodup := by
  exact nodup_ofFn_of_injective
    (smallSquare_injective prime primeIsPrime primeOdd)

private def translatedPrimeSquareValues
    (prime : Nat) [NeZero prime] (primePositive : 0 < prime)
    (target : Fin prime) :
    List (Fin prime) :=
  (primeSquareValues prime primePositive).map (fun value => target + -value)

private theorem translate_injective {prime : Nat} [NeZero prime]
    (target : Fin prime) :
    Function.Injective (fun value : Fin prime => target + -value) := by
  intro left right equal
  change target + -left = target + -right at equal
  have negativesEqual : -left = -right := add_left_cancel equal
  calc
    left = - -left := (neg_neg left).symm
    _ = - -right := congrArg Neg.neg negativesEqual
    _ = right := neg_neg right

private theorem translatedPrimeSquareValues_nodup
    (prime : Nat) [NeZero prime] (primeIsPrime : Nat.Prime prime)
    (primeOdd : Odd prime) (target : Fin prime) :
    (translatedPrimeSquareValues prime primeIsPrime.pos target).Nodup := by
  unfold translatedPrimeSquareValues
  exact QuotientFreeList.nodup_map_of_injective
    (translate_injective target)
    (primeSquareValues_nodup prime primeIsPrime primeOdd)

/-- Executable output of the odd-prime square-table collision.  The quotient
is cached alongside its defining equation so no witness is later recovered
from divisibility by choice. -/
structure PrimeSeed (prime : Nat) where
  first : Nat
  second : Nat
  multiplier : Nat
  firstSmall : 2 * first < prime
  secondSmall : 2 * second < prime
  equation : first ^ 2 + second ^ 2 + 1 = multiplier * prime

/-- The constructive square-table collision over the explicit prime residue
carrier.  It produces small natural witnesses whose square sum plus one is
divisible by the odd prime. -/
def primeSeed
    (prime : Nat) (primeIsPrime : Nat.Prime prime) (primeNotTwo : prime ≠ 2) :
    PrimeSeed prime := by
  letI : NeZero prime := ⟨primeIsPrime.ne_zero⟩
  let squareValues := primeSquareValues prime primeIsPrime.pos
  let target : Fin prime := -1
  let translated := translatedPrimeSquareValues prime primeIsPrime.pos target
  let carrier : List (Fin prime) := List.ofFn (fun value => value)
  have primeOdd : Odd prime := primeIsPrime.odd_of_ne_two primeNotTwo
  have squareNodup : squareValues.Nodup :=
    primeSquareValues_nodup prime primeIsPrime primeOdd
  have translatedNodup : translated.Nodup :=
    translatedPrimeSquareValues_nodup prime primeIsPrime primeOdd target
  have carrierNodup : carrier.Nodup :=
    nodup_ofFn_of_injective (fun _ _ equal => equal)
  have carrierComplete : ∀ value : Fin prime, value ∈ carrier := by
    intro value
    exact List.mem_ofFn.mpr ⟨value, rfl⟩
  have oversized : carrier.length < squareValues.length + translated.length := by
    unfold carrier squareValues translated translatedPrimeSquareValues
      primeSquareValues
    rw [QuotientFreeList.length_ofFn, List.length_map,
      QuotientFreeList.length_ofFn, odd_halfCount prime primeOdd]
    exact Nat.lt_succ_self prime
  have intersectionNonempty :
      QuotientFreeList.firstIntersection? squareValues translated ≠ none :=
    QuotientFreeList.firstIntersection?_ne_none_of_length_gt
      squareNodup translatedNodup
      (fun value _ => carrierComplete value)
      (fun value _ => carrierComplete value)
      carrierNodup oversized
  let indices : List (Fin ((prime + 1) / 2)) :=
    List.ofFn (fun index => index)
  let pairs : List
      (Fin ((prime + 1) / 2) × Fin ((prime + 1) / 2)) :=
    indices.flatMap (fun firstIndex =>
      indices.map (fun secondIndex => (firstIndex, secondIndex)))
  let accepted :
      (Fin ((prime + 1) / 2) × Fin ((prime + 1) / 2)) → Bool :=
    fun pair => decide
      (smallRoot prime primeIsPrime.pos pair.1 ^ 2 +
          smallRoot prime primeIsPrime.pos pair.2 ^ 2 + 1 = 0)
  have searchNonempty : pairs.find? accepted ≠ none := by
    intro searchEmpty
    have rejected :=
      (QuotientFreeList.find?_eq_none.mp searchEmpty)
    cases found : QuotientFreeList.firstIntersection? squareValues translated with
    | none => exact intersectionNonempty found
    | some common =>
      have commonMembers :=
        QuotientFreeList.firstIntersection?_eq_some found
      have firstMember := commonMembers.1
      unfold squareValues primeSquareValues at firstMember
      rw [List.mem_ofFn] at firstMember
      rcases firstMember with ⟨firstIndex, firstSquare⟩
      have translatedMember := commonMembers.2
      unfold translated translatedPrimeSquareValues at translatedMember
      rcases QuotientFreeList.mem_map.mp translatedMember with
        ⟨secondSquare, secondSquareMember, translatedSquare⟩
      unfold primeSquareValues at secondSquareMember
      rw [List.mem_ofFn] at secondSquareMember
      rcases secondSquareMember with ⟨secondIndex, secondSquareEqual⟩
      have residueEquation :
            smallRoot prime primeIsPrime.pos firstIndex ^ 2 +
                smallRoot prime primeIsPrime.pos secondIndex ^ 2 + 1 = 0 := by
          calc
            smallRoot prime primeIsPrime.pos firstIndex ^ 2 +
                  smallRoot prime primeIsPrime.pos secondIndex ^ 2 + 1 =
                common + secondSquare + 1 := by
              rw [firstSquare, secondSquareEqual]
            _ = 0 := by
              rw [← translatedSquare]
              unfold target
              ring1
      have pairMember : (firstIndex, secondIndex) ∈ pairs := by
        unfold pairs
        apply QuotientFreeList.mem_flatMap.mpr
        refine ⟨firstIndex, ?_, ?_⟩
        · unfold indices
          exact List.mem_ofFn.mpr ⟨firstIndex, rfl⟩
        · apply QuotientFreeList.mem_map.mpr
          refine ⟨secondIndex, ?_, rfl⟩
          unfold indices
          exact List.mem_ofFn.mpr ⟨secondIndex, rfl⟩
      have rejectedPair := rejected (firstIndex, secondIndex) pairMember
      have acceptedPair : accepted (firstIndex, secondIndex) = true := by
        unfold accepted
        exact decide_eq_true residueEquation
      rw [acceptedPair] at rejectedPair
      exact Bool.noConfusion rejectedPair
  cases pairFound : pairs.find? accepted with
  | none => exact False.elim (searchNonempty pairFound)
  | some pair =>
      have pairAccepted :=
        find?_eq_some_accepts pairFound
      have residueEquation :
          smallRoot prime primeIsPrime.pos pair.1 ^ 2 +
              smallRoot prime primeIsPrime.pos pair.2 ^ 2 + 1 = 0 := by
        unfold accepted at pairAccepted
        exact of_decide_eq_true pairAccepted
      have firstSmall : 2 * pair.1.val < prime := by
        have count := odd_halfCount prime primeOdd
        omega
      have secondSmall : 2 * pair.2.val < prime := by
        have count := odd_halfCount prime primeOdd
        omega
      have finOneValue : (1 : Fin prime).val = 1 := by
        change 1 % prime = 1
        exact Nat.mod_eq_of_lt primeIsPrime.one_lt
      have moduloEquation := congrArg Fin.val residueEquation
      simp only [pow_two, Fin.val_add, Fin.val_mul,
        Fin.val_zero, smallRoot_value prime primeIsPrime.pos] at moduloEquation
      rw [finOneValue] at moduloEquation
      have moduloZero :
          (pair.1.val ^ 2 + pair.2.val ^ 2 + 1) % prime = 0 := by
        calc
          (pair.1.val ^ 2 + pair.2.val ^ 2 + 1) % prime =
              (((pair.1.val ^ 2) % prime +
                  (pair.2.val ^ 2) % prime) % prime +
                1 % prime) % prime := by
            rw [Nat.add_mod
              (pair.1.val ^ 2 + pair.2.val ^ 2) 1 prime]
            rw [Nat.add_mod (pair.1.val ^ 2)
              (pair.2.val ^ 2) prime]
          _ = (((pair.1.val * pair.1.val) % prime +
                  (pair.2.val * pair.2.val) % prime) % prime +
                1) % prime := by
            rw [Nat.mod_eq_of_lt primeIsPrime.one_lt]
            simp only [pow_two]
          _ = 0 := moduloEquation
      have divides := Nat.dvd_of_mod_eq_zero moduloZero
      exact
        { first := pair.1.val
          second := pair.2.val
          multiplier :=
            (pair.1.val ^ 2 + pair.2.val ^ 2 + 1) / prime
          firstSmall := firstSmall
          secondSmall := secondSmall
          equation := (Nat.div_mul_cancel divides).symm }

/-- Propositional corollary of `primeSeed`, useful when only divisibility is
needed.  Executable consumers should retain the richer structure. -/
theorem prime_seed
    (prime : Nat) (primeIsPrime : Nat.Prime prime) (primeNotTwo : prime ≠ 2) :
    ∃ first second : Nat,
      2 * first < prime ∧ 2 * second < prime ∧
        prime ∣ first ^ 2 + second ^ 2 + 1 := by
  let seed := primeSeed prime primeIsPrime primeNotTwo
  refine ⟨seed.first, seed.second, seed.firstSmall, seed.secondSmall, ?_⟩
  exact ⟨seed.multiplier, by simpa only [Nat.mul_comm] using seed.equation⟩

/-- A represented positive multiple whose multiplier is already below the
modulus.  The representation is stored as data, not hidden behind choice. -/
structure BoundedMultiple (modulus : Nat) where
  multiplier : Nat
  positive : 0 < multiplier
  below : multiplier < modulus
  representation : Representation (multiplier * modulus)

/-- The prime seed gives a represented positive multiple `k * prime`, with
the multiplier already strictly smaller than the prime.  This is the finite
starting point for Lagrange descent. -/
def primeInitialMultiple
    (prime : Nat) (primeIsPrime : Nat.Prime prime) :
    BoundedMultiple prime := by
  by_cases primeIsTwo : prime = 2
  · subst prime
    exact
      { multiplier := 1
        positive := by decide
        below := by decide
        representation := ⟨1, 1, 0, 0, by decide⟩ }
  · let seed := primeSeed prime primeIsPrime primeIsTwo
    let first := seed.first
    let second := seed.second
    let multiplier := seed.multiplier
    have firstSmall : 2 * first < prime := seed.firstSmall
    have secondSmall : 2 * second < prime := seed.secondSmall
    have multipleEquation :
        first ^ 2 + second ^ 2 + 1 = multiplier * prime := seed.equation
    have firstBelow : first ≤ prime := by omega
    have secondBelow : second ≤ prime := by omega
    have firstSquareBound : first * first ≤ first * prime :=
      Nat.mul_le_mul_left first firstBelow
    have secondSquareBound : second * second ≤ second * prime :=
      Nat.mul_le_mul_left second secondBelow
    have rootsSumBelow : first + second < prime := by omega
    have sumBound :
        first ^ 2 + second ^ 2 + 1 ≤ (first + second) * prime + 1 := by
      simp only [pow_two, Nat.add_mul]
      omega
    have scaledSuccessorBelow :
        (first + second) * prime + 1 < (first + second + 1) * prime := by
      calc
        (first + second) * prime + 1 <
            (first + second) * prime + prime :=
          Nat.add_lt_add_left primeIsPrime.one_lt _
        _ = (first + second + 1) * prime := by
          simpa only [one_mul] using
            (Nat.add_mul (first + second) 1 prime).symm
    have scaledSuccessorBound :
        (first + second + 1) * prime ≤ prime * prime :=
      Nat.mul_le_mul_right prime (Nat.succ_le_iff.mpr rootsSumBelow)
    have squareSumBelow :
        first ^ 2 + second ^ 2 + 1 < prime * prime :=
      lt_of_le_of_lt sumBound
        (lt_of_lt_of_le scaledSuccessorBelow scaledSuccessorBound)
    have multiplierPositive : 0 < multiplier := by
      apply Nat.pos_of_mul_pos_right
      rw [← multipleEquation]
      omega
    have multiplierBelow : multiplier < prime := by
      apply nat_lt_of_mul_lt_mul_right
      rw [← multipleEquation]
      exact squareSumBelow
    exact
      { multiplier := multiplier
        positive := multiplierPositive
        below := multiplierBelow
        representation :=
          ⟨first, second, 1, 0,
            by simpa using multipleEquation⟩ }

/-- A centered residue with an explicit quotient.  Its decomposition is
computational data, while `small` certifies the strict half-modulus bound
used in descent. -/
structure CenteredResidue (modulus source : Nat) where
  value : Int
  quotient : Int
  decomposition :
    (source : Int) = value + (modulus : Int) * quotient
  small : 2 * value.natAbs < modulus

/-- Compute the centered representative of `source` modulo a positive odd
modulus, caching the corresponding quotient. -/
def centeredResidue (modulus source : Nat) (modulusPositive : 0 < modulus)
    (modulusOdd : Odd modulus) : CenteredResidue modulus source := by
  let remainder := source % modulus
  let quotient := source / modulus
  have remainderBelow : remainder < modulus :=
    Nat.mod_lt source modulusPositive
  have divisionEquation : remainder + modulus * quotient = source := by
    exact Nat.mod_add_div source modulus
  have castDivisionEquation :
      (source : Int) =
        (remainder : Int) + (modulus : Int) * (quotient : Int) := by
    calc
      (source : Int) = ((remainder + modulus * quotient : Nat) : Int) :=
        congrArg (fun value : Nat => (value : Int)) divisionEquation.symm
      _ = (remainder : Int) + ((modulus * quotient : Nat) : Int) :=
        (Int.ofNat_add_ofNat remainder (modulus * quotient)).symm
      _ = (remainder : Int) + (modulus : Int) * (quotient : Int) := by
        rw [Int.ofNat_mul_ofNat]
  by_cases lowerHalf : 2 * remainder < modulus
  · exact
      { value := (remainder : Int)
        quotient := (quotient : Int)
        decomposition := castDivisionEquation
        small := by simpa using lowerHalf }
  · have modulusBelowDouble : modulus < 2 * remainder := by
      have weak : modulus ≤ 2 * remainder := by omega
      have unequal : modulus ≠ 2 * remainder := by
        rintro equality
        rcases modulusOdd with ⟨half, oddEquation⟩
        omega
      omega
    have centeredSmall : 2 * (modulus - remainder) < modulus := by
      omega
    exact
      { value := -((modulus - remainder : Nat) : Int)
        quotient := (quotient : Int) + 1
        decomposition := by
          have remainderLe : remainder ≤ modulus := Nat.le_of_lt remainderBelow
          have castDifference :
              ((modulus - remainder : Nat) : Int) =
                (modulus : Int) - (remainder : Int) := by
            exact Int.ofNat_sub remainderLe
          rw [castDifference]
          calc
            (source : Int) =
                (remainder : Int) + (modulus : Int) * (quotient : Int) :=
              castDivisionEquation
            _ = -((modulus : Int) - (remainder : Int)) +
                (modulus : Int) * ((quotient : Int) + 1) := by ring1
        small := by
          simpa only [Int.natAbs_neg, Int.natAbs_natCast] using
            centeredSmall }

/-- Four half-modulus bounds imply the corresponding four-square sum is
strictly below the modulus square. -/
private theorem small_four_square_sum_lt
    {modulus first second third fourth : Nat}
    (modulusPositive : 0 < modulus)
    (firstSmall : 2 * first < modulus)
    (secondSmall : 2 * second < modulus)
    (thirdSmall : 2 * third < modulus)
    (fourthSmall : 2 * fourth < modulus) :
    first ^ 2 + second ^ 2 + third ^ 2 + fourth ^ 2 <
      modulus * modulus := by
  have firstBound :=
    Nat.mul_le_mul_right first (Nat.le_of_lt firstSmall)
  have secondBound :=
    Nat.mul_le_mul_right second (Nat.le_of_lt secondSmall)
  have thirdBound :=
    Nat.mul_le_mul_right third (Nat.le_of_lt thirdSmall)
  have fourthBound :=
    Nat.mul_le_mul_right fourth (Nat.le_of_lt fourthSmall)
  have firstBound' : 2 * (first * first) ≤ modulus * first := by
    simpa only [Nat.mul_assoc] using firstBound
  have secondBound' : 2 * (second * second) ≤ modulus * second := by
    simpa only [Nat.mul_assoc] using secondBound
  have thirdBound' : 2 * (third * third) ≤ modulus * third := by
    simpa only [Nat.mul_assoc] using thirdBound
  have fourthBound' : 2 * (fourth * fourth) ≤ modulus * fourth := by
    simpa only [Nat.mul_assoc] using fourthBound
  have rootsBelow : first + second + third + fourth < 2 * modulus := by
    omega
  have doubledSquaresBound :
      2 * (first ^ 2 + second ^ 2 + third ^ 2 + fourth ^ 2) ≤
        modulus * (first + second + third + fourth) := by
    simp only [pow_two, Nat.mul_add]
    omega
  have scaledRootsBelow :
      modulus * (first + second + third + fourth) <
        modulus * (2 * modulus) :=
    Nat.mul_lt_mul_of_pos_left rootsBelow modulusPositive
  have doubledSquaresBelow :
      2 * (first ^ 2 + second ^ 2 + third ^ 2 + fourth ^ 2) <
        2 * (modulus * modulus) := by
    apply lt_of_le_of_lt doubledSquaresBound
    calc
      modulus * (first + second + third + fourth) <
          modulus * (2 * modulus) := scaledRootsBelow
      _ = 2 * (modulus * modulus) := by ring1
  omega

private theorem nat_eq_zero_of_square_eq_zero {value : Nat}
    (squareZero : value ^ 2 = 0) : value = 0 := by
  by_contra valueNonzero
  have valuePositive : 0 < value := Nat.zero_lt_of_ne_zero valueNonzero
  have squarePositive : 0 < value * value :=
    Nat.mul_pos valuePositive valuePositive
  rw [pow_two] at squareZero
  omega

/-- One descent step lowers the represented multiplier while retaining a
checked four-square representation of its product with the target. -/
structure DescentStep (previous target : Nat) where
  multiplier : Nat
  positive : 0 < multiplier
  below : multiplier < previous
  representation : Representation (multiplier * target)

/-- The odd-multiplier branch of Lagrange descent.  Centered residues and all
four Euler quotients are computed explicitly. -/
def oddDescentStep (prime multiplier : Nat)
    (primeIsPrime : Nat.Prime prime)
    (multiplierPositive : 0 < multiplier)
    (multiplierBelowPrime : multiplier < prime)
    (multiplierGreaterOne : 1 < multiplier)
    (multiplierOdd : Odd multiplier)
    (input : Representation (multiplier * prime)) :
    DescentStep multiplier prime := by
  let firstCentered := centeredResidue multiplier input.first
    multiplierPositive multiplierOdd
  let secondCentered := centeredResidue multiplier input.second
    multiplierPositive multiplierOdd
  let thirdCentered := centeredResidue multiplier input.third
    multiplierPositive multiplierOdd
  let fourthCentered := centeredResidue multiplier input.fourth
    multiplierPositive multiplierOdd
  let centeredSum :=
    firstCentered.value.natAbs ^ 2 +
      secondCentered.value.natAbs ^ 2 +
      thirdCentered.value.natAbs ^ 2 +
      fourthCentered.value.natAbs ^ 2
  have inputCast :
      (input.first : Int) ^ 2 + (input.second : Int) ^ 2 +
          (input.third : Int) ^ 2 + (input.fourth : Int) ^ 2 =
        (multiplier : Int) * (prime : Int) := by
    have castEquation :=
      congrArg (fun value : Nat => (value : Int)) input.equation
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using castEquation
  have centeredSumCast :
      (centeredSum : Int) =
        firstCentered.value ^ 2 + secondCentered.value ^ 2 +
          thirdCentered.value ^ 2 + fourthCentered.value ^ 2 := by
    unfold centeredSum
    simp only [Nat.cast_add, Nat.cast_pow, Int.natAbs_pow_two]
  let correction : Int :=
    2 * firstCentered.value * firstCentered.quotient +
      (multiplier : Int) * firstCentered.quotient ^ 2 +
      2 * secondCentered.value * secondCentered.quotient +
      (multiplier : Int) * secondCentered.quotient ^ 2 +
      2 * thirdCentered.value * thirdCentered.quotient +
      (multiplier : Int) * thirdCentered.quotient ^ 2 +
      2 * fourthCentered.value * fourthCentered.quotient +
      (multiplier : Int) * fourthCentered.quotient ^ 2
  have expandedCentered :
      (firstCentered.value ^ 2 + secondCentered.value ^ 2 +
          thirdCentered.value ^ 2 + fourthCentered.value ^ 2) +
          (multiplier : Int) * correction =
        (multiplier : Int) * (prime : Int) := by
    calc
      (firstCentered.value ^ 2 + secondCentered.value ^ 2 +
            thirdCentered.value ^ 2 + fourthCentered.value ^ 2) +
            (multiplier : Int) * correction =
          (firstCentered.value +
              (multiplier : Int) * firstCentered.quotient) ^ 2 +
            (secondCentered.value +
              (multiplier : Int) * secondCentered.quotient) ^ 2 +
            (thirdCentered.value +
              (multiplier : Int) * thirdCentered.quotient) ^ 2 +
            (fourthCentered.value +
              (multiplier : Int) * fourthCentered.quotient) ^ 2 := by
        unfold correction
        ring1
      _ = (input.first : Int) ^ 2 + (input.second : Int) ^ 2 +
            (input.third : Int) ^ 2 + (input.fourth : Int) ^ 2 := by
        rw [← firstCentered.decomposition,
          ← secondCentered.decomposition,
          ← thirdCentered.decomposition,
          ← fourthCentered.decomposition]
      _ = (multiplier : Int) * (prime : Int) := inputCast
  have centeredDividesInt :
      (multiplier : Int) ∣
        firstCentered.value ^ 2 + secondCentered.value ^ 2 +
          thirdCentered.value ^ 2 + fourthCentered.value ^ 2 := by
    refine ⟨(prime : Int) - correction, ?_⟩
    calc
      firstCentered.value ^ 2 + secondCentered.value ^ 2 +
            thirdCentered.value ^ 2 + fourthCentered.value ^ 2 =
          (multiplier : Int) * (prime : Int) -
            (multiplier : Int) * correction :=
        by omega
      _ = (multiplier : Int) * ((prime : Int) - correction) := by ring1
  have centeredDivides : multiplier ∣ centeredSum := by
    apply nat_dvd_of_int_natCast_dvd multiplierPositive
    rw [centeredSumCast]
    exact centeredDividesInt
  let nextMultiplier := centeredSum / multiplier
  have nextEquation : centeredSum = nextMultiplier * multiplier :=
    (Nat.div_mul_cancel centeredDivides).symm
  have centeredSumBelow : centeredSum < multiplier * multiplier := by
    unfold centeredSum
    exact small_four_square_sum_lt multiplierPositive
      firstCentered.small secondCentered.small thirdCentered.small
      fourthCentered.small
  have nextBelow : nextMultiplier < multiplier := by
    apply nat_lt_of_mul_lt_mul_right
    rw [← nextEquation]
    exact centeredSumBelow
  have nextPositive : 0 < nextMultiplier := by
    by_contra nextNotPositive
    have nextZero : nextMultiplier = 0 :=
      Nat.eq_zero_of_not_pos nextNotPositive
    have centeredSumZero : centeredSum = 0 := by
      rw [nextEquation, nextZero, Nat.zero_mul]
    have squareZeros :
        ((firstCentered.value.natAbs ^ 2 = 0 ∧
            secondCentered.value.natAbs ^ 2 = 0) ∧
          thirdCentered.value.natAbs ^ 2 = 0) ∧
          fourthCentered.value.natAbs ^ 2 = 0 := by
      unfold centeredSum at centeredSumZero
      simpa only [Nat.add_eq_zero_iff] using centeredSumZero
    have centeredZeros :
        firstCentered.value = 0 ∧ secondCentered.value = 0 ∧
          thirdCentered.value = 0 ∧ fourthCentered.value = 0 :=
      ⟨Int.natAbs_eq_zero.mp
          (nat_eq_zero_of_square_eq_zero squareZeros.1.1.1),
        Int.natAbs_eq_zero.mp
          (nat_eq_zero_of_square_eq_zero squareZeros.1.1.2),
        Int.natAbs_eq_zero.mp
          (nat_eq_zero_of_square_eq_zero squareZeros.1.2),
        Int.natAbs_eq_zero.mp
          (nat_eq_zero_of_square_eq_zero squareZeros.2)⟩
    have firstDivides : multiplier ∣ input.first := by
      apply nat_dvd_of_int_natCast_dvd multiplierPositive
      refine ⟨firstCentered.quotient, ?_⟩
      simpa only [centeredZeros.1, zero_add] using
        firstCentered.decomposition
    have secondDivides : multiplier ∣ input.second := by
      apply nat_dvd_of_int_natCast_dvd multiplierPositive
      refine ⟨secondCentered.quotient, ?_⟩
      simpa only [centeredZeros.2.1, zero_add] using
        secondCentered.decomposition
    have thirdDivides : multiplier ∣ input.third := by
      apply nat_dvd_of_int_natCast_dvd multiplierPositive
      refine ⟨thirdCentered.quotient, ?_⟩
      simpa only [centeredZeros.2.2.1, zero_add] using
        thirdCentered.decomposition
    have fourthDivides : multiplier ∣ input.fourth := by
      apply nat_dvd_of_int_natCast_dvd multiplierPositive
      refine ⟨fourthCentered.quotient, ?_⟩
      simpa only [centeredZeros.2.2.2, zero_add] using
        fourthCentered.decomposition
    have firstSquareDivides :
        multiplier * multiplier ∣ input.first ^ 2 := by
      simpa only [pow_two] using Nat.mul_dvd_mul firstDivides firstDivides
    have secondSquareDivides :
        multiplier * multiplier ∣ input.second ^ 2 := by
      simpa only [pow_two] using Nat.mul_dvd_mul secondDivides secondDivides
    have thirdSquareDivides :
        multiplier * multiplier ∣ input.third ^ 2 := by
      simpa only [pow_two] using Nat.mul_dvd_mul thirdDivides thirdDivides
    have fourthSquareDivides :
        multiplier * multiplier ∣ input.fourth ^ 2 := by
      simpa only [pow_two] using Nat.mul_dvd_mul fourthDivides fourthDivides
    have squareSumDivides :
        multiplier * multiplier ∣
          input.first ^ 2 + input.second ^ 2 +
            input.third ^ 2 + input.fourth ^ 2 :=
      Nat.dvd_add
        (Nat.dvd_add (Nat.dvd_add firstSquareDivides secondSquareDivides)
          thirdSquareDivides) fourthSquareDivides
    have squareMultiplierDividesProduct :
        multiplier * multiplier ∣ multiplier * prime := by
      rw [← input.equation]
      exact squareSumDivides
    have multiplierDividesPrime : multiplier ∣ prime := by
      rcases squareMultiplierDividesProduct with ⟨factor, factorEquation⟩
      refine ⟨factor, ?_⟩
      apply Nat.mul_left_cancel multiplierPositive
      calc
        multiplier * prime = (multiplier * multiplier) * factor :=
          factorEquation
        _ = multiplier * (multiplier * factor) := by ring1
    rcases primeIsPrime.eq_one_or_self_of_dvd multiplier
        multiplierDividesPrime with multiplierOne | multiplierPrime
    · exact (Nat.ne_of_gt multiplierGreaterOne) multiplierOne
    · exact (Nat.ne_of_lt multiplierBelowPrime) multiplierPrime
  have centeredMultiplierCast :
      firstCentered.value ^ 2 + secondCentered.value ^ 2 +
          thirdCentered.value ^ 2 + fourthCentered.value ^ 2 =
        (nextMultiplier : Int) * (multiplier : Int) := by
    have castEquation :=
      congrArg (fun value : Nat => (value : Int)) nextEquation
    rw [centeredSumCast] at castEquation
    simpa only [Nat.cast_mul] using castEquation
  let firstEuler : Int :=
    secondCentered.value * (input.first : Int) -
      firstCentered.value * (input.second : Int) -
      fourthCentered.value * (input.third : Int) -
      (-thirdCentered.value) * (input.fourth : Int)
  let secondEuler : Int :=
    secondCentered.value * (input.second : Int) +
      firstCentered.value * (input.first : Int) +
      fourthCentered.value * (input.fourth : Int) -
      (-thirdCentered.value) * (input.third : Int)
  let thirdEuler : Int :=
    secondCentered.value * (input.third : Int) -
      firstCentered.value * (input.fourth : Int) +
      fourthCentered.value * (input.first : Int) +
      (-thirdCentered.value) * (input.second : Int)
  let fourthEuler : Int :=
    secondCentered.value * (input.fourth : Int) +
      firstCentered.value * (input.third : Int) -
      fourthCentered.value * (input.second : Int) +
      (-thirdCentered.value) * (input.first : Int)
  have firstEulerDivides : (multiplier : Int) ∣ firstEuler := by
    refine ⟨secondCentered.value * firstCentered.quotient -
      firstCentered.value * secondCentered.quotient -
      fourthCentered.value * thirdCentered.quotient +
      thirdCentered.value * fourthCentered.quotient, ?_⟩
    unfold firstEuler
    rw [firstCentered.decomposition, secondCentered.decomposition,
      thirdCentered.decomposition, fourthCentered.decomposition]
    ring1
  have secondEulerDivides : (multiplier : Int) ∣ secondEuler := by
    refine ⟨(nextMultiplier : Int) +
      secondCentered.value * secondCentered.quotient +
      firstCentered.value * firstCentered.quotient +
      fourthCentered.value * fourthCentered.quotient +
      thirdCentered.value * thirdCentered.quotient, ?_⟩
    unfold secondEuler
    rw [firstCentered.decomposition, secondCentered.decomposition,
      thirdCentered.decomposition, fourthCentered.decomposition]
    calc
      secondCentered.value *
              (secondCentered.value +
                (multiplier : Int) * secondCentered.quotient) +
            firstCentered.value *
              (firstCentered.value +
                (multiplier : Int) * firstCentered.quotient) +
            fourthCentered.value *
              (fourthCentered.value +
                (multiplier : Int) * fourthCentered.quotient) -
            -thirdCentered.value *
              (thirdCentered.value +
                (multiplier : Int) * thirdCentered.quotient) =
          (firstCentered.value ^ 2 + secondCentered.value ^ 2 +
              thirdCentered.value ^ 2 + fourthCentered.value ^ 2) +
            (multiplier : Int) *
              (secondCentered.value * secondCentered.quotient +
                firstCentered.value * firstCentered.quotient +
                fourthCentered.value * fourthCentered.quotient +
                thirdCentered.value * thirdCentered.quotient) := by ring1
      _ = (multiplier : Int) *
          ((nextMultiplier : Int) +
            secondCentered.value * secondCentered.quotient +
            firstCentered.value * firstCentered.quotient +
            fourthCentered.value * fourthCentered.quotient +
            thirdCentered.value * thirdCentered.quotient) := by
        rw [centeredMultiplierCast]
        ring1
  have thirdEulerDivides : (multiplier : Int) ∣ thirdEuler := by
    refine ⟨secondCentered.value * thirdCentered.quotient -
      firstCentered.value * fourthCentered.quotient +
      fourthCentered.value * firstCentered.quotient -
      thirdCentered.value * secondCentered.quotient, ?_⟩
    unfold thirdEuler
    rw [firstCentered.decomposition, secondCentered.decomposition,
      thirdCentered.decomposition, fourthCentered.decomposition]
    ring1
  have fourthEulerDivides : (multiplier : Int) ∣ fourthEuler := by
    refine ⟨secondCentered.value * fourthCentered.quotient +
      firstCentered.value * thirdCentered.quotient -
      fourthCentered.value * secondCentered.quotient -
      thirdCentered.value * firstCentered.quotient, ?_⟩
    unfold fourthEuler
    rw [firstCentered.decomposition, secondCentered.decomposition,
      thirdCentered.decomposition, fourthCentered.decomposition]
    ring1
  let firstQuotient := firstEuler / (multiplier : Int)
  let secondQuotient := secondEuler / (multiplier : Int)
  let thirdQuotient := thirdEuler / (multiplier : Int)
  let fourthQuotient := fourthEuler / (multiplier : Int)
  have firstScaled :
      (multiplier : Int) * firstQuotient = firstEuler := by
    exact Int.mul_ediv_cancel' firstEulerDivides
  have secondScaled :
      (multiplier : Int) * secondQuotient = secondEuler := by
    exact Int.mul_ediv_cancel' secondEulerDivides
  have thirdScaled :
      (multiplier : Int) * thirdQuotient = thirdEuler := by
    exact Int.mul_ediv_cancel' thirdEulerDivides
  have fourthScaled :
      (multiplier : Int) * fourthQuotient = fourthEuler := by
    exact Int.mul_ediv_cancel' fourthEulerDivides
  have eulerProduct :
      firstEuler ^ 2 + secondEuler ^ 2 + thirdEuler ^ 2 +
          fourthEuler ^ 2 =
        (firstCentered.value ^ 2 + secondCentered.value ^ 2 +
          thirdCentered.value ^ 2 + fourthCentered.value ^ 2) *
        ((input.first : Int) ^ 2 + (input.second : Int) ^ 2 +
          (input.third : Int) ^ 2 + (input.fourth : Int) ^ 2) := by
    unfold firstEuler secondEuler thirdEuler fourthEuler
    ring1
  have scaledQuotientNorm :
      (multiplier : Int) ^ 2 *
          (firstQuotient ^ 2 + secondQuotient ^ 2 +
            thirdQuotient ^ 2 + fourthQuotient ^ 2) =
        (multiplier : Int) ^ 2 *
          ((nextMultiplier : Int) * (prime : Int)) := by
    calc
      (multiplier : Int) ^ 2 *
            (firstQuotient ^ 2 + secondQuotient ^ 2 +
              thirdQuotient ^ 2 + fourthQuotient ^ 2) =
          firstEuler ^ 2 + secondEuler ^ 2 + thirdEuler ^ 2 +
            fourthEuler ^ 2 := by
        rw [← firstScaled, ← secondScaled, ← thirdScaled,
          ← fourthScaled]
        ring1
      _ = (firstCentered.value ^ 2 + secondCentered.value ^ 2 +
            thirdCentered.value ^ 2 + fourthCentered.value ^ 2) *
          ((input.first : Int) ^ 2 + (input.second : Int) ^ 2 +
            (input.third : Int) ^ 2 + (input.fourth : Int) ^ 2) :=
        eulerProduct
      _ = (multiplier : Int) ^ 2 *
          ((nextMultiplier : Int) * (prime : Int)) := by
        rw [centeredMultiplierCast, inputCast]
        ring1
  have quotientNorm :
      firstQuotient ^ 2 + secondQuotient ^ 2 +
          thirdQuotient ^ 2 + fourthQuotient ^ 2 =
        (nextMultiplier : Int) * (prime : Int) :=
    Int.eq_of_mul_eq_mul_left (by
      intro squareZero
      have castSquare :
          ((multiplier * multiplier : Nat) : Int) =
            (multiplier : Int) ^ 2 := by
        simp only [Nat.cast_mul, pow_two]
      rw [← castSquare] at squareZero
      have naturalSquareZero := Int.ofNat.inj squareZero
      omega) scaledQuotientNorm
  have naturalQuotientNorm :
      firstQuotient.natAbs ^ 2 + secondQuotient.natAbs ^ 2 +
          thirdQuotient.natAbs ^ 2 + fourthQuotient.natAbs ^ 2 =
        nextMultiplier * prime := by
    apply Int.natCast_inj.mp
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Int.natAbs_pow_two] using quotientNorm
  exact
    { multiplier := nextMultiplier
      positive := nextPositive
      below := nextBelow
      representation :=
        ⟨firstQuotient.natAbs, secondQuotient.natAbs,
          thirdQuotient.natAbs, fourthQuotient.natAbs,
          naturalQuotientNorm⟩ }

private theorem natCast_two_int : ((2 : Nat) : Int) = 2 := by decide

private theorem two_dvd_int_sub_of_same_parity
    {left right : Nat} (sameParity : left % 2 = right % 2) :
    (2 : Int) ∣ (left : Int) - (right : Int) := by
  have leftDivision : left % 2 + 2 * (left / 2) = left :=
    Nat.mod_add_div left 2
  have rightDivision : right % 2 + 2 * (right / 2) = right :=
    Nat.mod_add_div right 2
  have leftCast :
      (left : Int) = ((left % 2 : Nat) : Int) +
        2 * ((left / 2 : Nat) : Int) := by
    have castEquation :=
      congrArg (fun value : Nat => (value : Int)) leftDivision
    simpa only [Nat.cast_add, Nat.cast_mul, natCast_two_int] using
      castEquation.symm
  have rightCast :
      (right : Int) = ((right % 2 : Nat) : Int) +
        2 * ((right / 2 : Nat) : Int) := by
    have castEquation :=
      congrArg (fun value : Nat => (value : Int)) rightDivision
    simpa only [Nat.cast_add, Nat.cast_mul, natCast_two_int] using
      castEquation.symm
  refine ⟨((left / 2 : Nat) : Int) - ((right / 2 : Nat) : Int), ?_⟩
  have sameParityCast :
      ((left % 2 : Nat) : Int) = ((right % 2 : Nat) : Int) :=
    congrArg (fun value : Nat => (value : Int)) sameParity
  rw [leftCast, rightCast, sameParityCast]
  ring1

private theorem two_dvd_int_add_of_same_parity
    {left right : Nat} (sameParity : left % 2 = right % 2) :
    (2 : Int) ∣ (left : Int) + (right : Int) := by
  have leftDivision : left % 2 + 2 * (left / 2) = left :=
    Nat.mod_add_div left 2
  have rightDivision : right % 2 + 2 * (right / 2) = right :=
    Nat.mod_add_div right 2
  have leftCast :
      (left : Int) = ((left % 2 : Nat) : Int) +
        2 * ((left / 2 : Nat) : Int) := by
    have castEquation :=
      congrArg (fun value : Nat => (value : Int)) leftDivision
    simpa only [Nat.cast_add, Nat.cast_mul, natCast_two_int] using
      castEquation.symm
  have rightCast :
      (right : Int) = ((right % 2 : Nat) : Int) +
        2 * ((right / 2 : Nat) : Int) := by
    have castEquation :=
      congrArg (fun value : Nat => (value : Int)) rightDivision
    simpa only [Nat.cast_add, Nat.cast_mul, natCast_two_int] using
      castEquation.symm
  refine ⟨((left / 2 : Nat) : Int) + ((right / 2 : Nat) : Int) +
    ((left % 2 : Nat) : Int), ?_⟩
  have sameParityCast :
      ((left % 2 : Nat) : Int) = ((right % 2 : Nat) : Int) :=
    congrArg (fun value : Nat => (value : Int)) sameParity
  rw [leftCast, rightCast, sameParityCast]
  ring1

/-- An even four-square sum admits one of the three displayed pairings into
equal parities.  The proof checks the sixteen possible residue tuples. -/
private theorem four_parity_pairing
    {first second third fourth : Nat}
    (sumEven :
      2 ∣ first ^ 2 + second ^ 2 + third ^ 2 + fourth ^ 2) :
    (first % 2 = second % 2 ∧ third % 2 = fourth % 2) ∨
      (first % 2 = third % 2 ∧ second % 2 = fourth % 2) ∨
      (first % 2 = fourth % 2 ∧ second % 2 = third % 2) := by
  have totalMod := Nat.mod_eq_zero_of_dvd sumEven
  rcases Nat.mod_two_eq_zero_or_one first with firstParity | firstParity <;>
    rcases Nat.mod_two_eq_zero_or_one second with secondParity | secondParity <;>
    rcases Nat.mod_two_eq_zero_or_one third with thirdParity | thirdParity <;>
    rcases Nat.mod_two_eq_zero_or_one fourth with fourthParity | fourthParity <;>
    simp [firstParity, secondParity, thirdParity, fourthParity, pow_two,
      Nat.add_mod, Nat.mul_mod] at totalMod ⊢

private theorem two_dvd_of_even {value : Nat} (valueEven : Even value) :
    2 ∣ value := by
  rcases valueEven with ⟨half, equation⟩
  exact ⟨half, by omega⟩

/-- Exact halving identity for two same-parity pairs. -/
private def halvePairedFourSquares
    (target first second third fourth : Nat)
    (equation :
      first ^ 2 + second ^ 2 + third ^ 2 + fourth ^ 2 = 2 * target)
    (firstPair : first % 2 = second % 2)
    (secondPair : third % 2 = fourth % 2) :
    Representation target := by
  let firstHalf : Int := ((first : Int) - (second : Int)) / 2
  let secondHalf : Int := ((first : Int) + (second : Int)) / 2
  let thirdHalf : Int := ((third : Int) - (fourth : Int)) / 2
  let fourthHalf : Int := ((third : Int) + (fourth : Int)) / 2
  have firstDifferenceDivides :
      (2 : Int) ∣ (first : Int) - (second : Int) :=
    two_dvd_int_sub_of_same_parity firstPair
  have firstSumDivides :
      (2 : Int) ∣ (first : Int) + (second : Int) :=
    two_dvd_int_add_of_same_parity firstPair
  have secondDifferenceDivides :
      (2 : Int) ∣ (third : Int) - (fourth : Int) :=
    two_dvd_int_sub_of_same_parity secondPair
  have secondSumDivides :
      (2 : Int) ∣ (third : Int) + (fourth : Int) :=
    two_dvd_int_add_of_same_parity secondPair
  have firstScaled : 2 * firstHalf = (first : Int) - (second : Int) :=
    Int.mul_ediv_cancel' firstDifferenceDivides
  have secondScaled : 2 * secondHalf = (first : Int) + (second : Int) :=
    Int.mul_ediv_cancel' firstSumDivides
  have thirdScaled : 2 * thirdHalf = (third : Int) - (fourth : Int) :=
    Int.mul_ediv_cancel' secondDifferenceDivides
  have fourthScaled : 2 * fourthHalf = (third : Int) + (fourth : Int) :=
    Int.mul_ediv_cancel' secondSumDivides
  have equationCast :
      (first : Int) ^ 2 + (second : Int) ^ 2 +
          (third : Int) ^ 2 + (fourth : Int) ^ 2 =
        2 * (target : Int) := by
    have castEquation :=
      congrArg (fun value : Nat => (value : Int)) equation
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      natCast_two_int] using castEquation
  have scaledNorm :
      (4 : Int) *
          (firstHalf ^ 2 + secondHalf ^ 2 +
            thirdHalf ^ 2 + fourthHalf ^ 2) =
        (4 : Int) * (target : Int) := by
    calc
      (4 : Int) *
            (firstHalf ^ 2 + secondHalf ^ 2 +
              thirdHalf ^ 2 + fourthHalf ^ 2) =
          (2 * firstHalf) ^ 2 + (2 * secondHalf) ^ 2 +
            (2 * thirdHalf) ^ 2 + (2 * fourthHalf) ^ 2 := by ring1
      _ = ((first : Int) - (second : Int)) ^ 2 +
            ((first : Int) + (second : Int)) ^ 2 +
            ((third : Int) - (fourth : Int)) ^ 2 +
            ((third : Int) + (fourth : Int)) ^ 2 := by
        rw [firstScaled, secondScaled, thirdScaled, fourthScaled]
      _ =
          2 * ((first : Int) ^ 2 + (second : Int) ^ 2 +
            (third : Int) ^ 2 + (fourth : Int) ^ 2) := by
        ring1
      _ = (4 : Int) * (target : Int) := by
        rw [equationCast]
        ring1
  have halfNorm :
      firstHalf ^ 2 + secondHalf ^ 2 +
          thirdHalf ^ 2 + fourthHalf ^ 2 = (target : Int) :=
    Int.eq_of_mul_eq_mul_left (by decide : (4 : Int) ≠ 0) scaledNorm
  have naturalHalfNorm :
      firstHalf.natAbs ^ 2 + secondHalf.natAbs ^ 2 +
          thirdHalf.natAbs ^ 2 + fourthHalf.natAbs ^ 2 = target := by
    apply Int.natCast_inj.mp
    simpa only [Nat.cast_add, Nat.cast_pow, Int.natAbs_pow_two] using halfNorm
  exact
    ⟨firstHalf.natAbs, secondHalf.natAbs, thirdHalf.natAbs,
      fourthHalf.natAbs, naturalHalfNorm⟩

/-- The even-multiplier branch halves the multiplier after explicitly
selecting one of the three parity pairings. -/
def evenDescentStep (prime multiplier : Nat)
    (multiplierPositive : 0 < multiplier)
    (multiplierEven : Even multiplier)
    (input : Representation (multiplier * prime)) :
    DescentStep multiplier prime := by
  let halfMultiplier := multiplier / 2
  have twoDivides : 2 ∣ multiplier := two_dvd_of_even multiplierEven
  have halfEquation : halfMultiplier * 2 = multiplier :=
    Nat.div_mul_cancel twoDivides
  have halfPositive : 0 < halfMultiplier := by
    by_contra halfNotPositive
    have halfZero := Nat.eq_zero_of_not_pos halfNotPositive
    rw [halfZero, Nat.zero_mul] at halfEquation
    omega
  have halfBelow : halfMultiplier < multiplier := by omega
  have pairedTargetEquation :
      input.first ^ 2 + input.second ^ 2 +
          input.third ^ 2 + input.fourth ^ 2 =
        2 * (halfMultiplier * prime) := by
    calc
      input.first ^ 2 + input.second ^ 2 +
            input.third ^ 2 + input.fourth ^ 2 =
          multiplier * prime := input.equation
      _ = 2 * (halfMultiplier * prime) := by
        rw [← halfEquation]
        ring1
  have sumEven :
      2 ∣ input.first ^ 2 + input.second ^ 2 +
        input.third ^ 2 + input.fourth ^ 2 :=
    ⟨halfMultiplier * prime, pairedTargetEquation⟩
  have pairing := four_parity_pairing sumEven
  by_cases firstSecond : input.first % 2 = input.second % 2
  · have thirdFourth : input.third % 2 = input.fourth % 2 := by
      rcases pairing with direct | cross | cross
      · exact direct.2
      · exact cross.1.symm.trans (firstSecond.trans cross.2)
      · exact cross.2.symm.trans (firstSecond.symm.trans cross.1)
    exact
      { multiplier := halfMultiplier
        positive := halfPositive
        below := halfBelow
        representation := halvePairedFourSquares
          (halfMultiplier * prime) input.first input.second input.third
          input.fourth pairedTargetEquation firstSecond thirdFourth }
  · by_cases firstThird : input.first % 2 = input.third % 2
    · have secondFourth : input.second % 2 = input.fourth % 2 := by
        rcases pairing with direct | cross | cross
        · exact False.elim (firstSecond direct.1)
        · exact cross.2
        · exact False.elim (firstSecond (firstThird.trans cross.2.symm))
      have reorderedEquation :
          input.first ^ 2 + input.third ^ 2 +
              input.second ^ 2 + input.fourth ^ 2 =
            2 * (halfMultiplier * prime) := by
        rw [← pairedTargetEquation]
        ring1
      exact
        { multiplier := halfMultiplier
          positive := halfPositive
          below := halfBelow
          representation := halvePairedFourSquares
            (halfMultiplier * prime) input.first input.third input.second
            input.fourth reorderedEquation firstThird secondFourth }
    · have firstFourth : input.first % 2 = input.fourth % 2 := by
        rcases pairing with direct | cross | cross
        · exact False.elim (firstSecond direct.1)
        · exact False.elim (firstThird cross.1)
        · exact cross.1
      have secondThird : input.second % 2 = input.third % 2 := by
        rcases pairing with direct | cross | cross
        · exact False.elim (firstSecond direct.1)
        · exact False.elim (firstThird cross.1)
        · exact cross.2
      have reorderedEquation :
          input.first ^ 2 + input.fourth ^ 2 +
              input.second ^ 2 + input.third ^ 2 =
            2 * (halfMultiplier * prime) := by
        rw [← pairedTargetEquation]
        ring1
      exact
        { multiplier := halfMultiplier
          positive := halfPositive
          below := halfBelow
          representation := halvePairedFourSquares
            (halfMultiplier * prime) input.first input.fourth input.second
            input.third reorderedEquation firstFourth secondThird }

/-- Well-founded Lagrange descent on the positive multiplier. -/
def descendPrime (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (multiplier : Nat) (multiplierPositive : 0 < multiplier)
    (multiplierBelowPrime : multiplier < prime)
    (input : Representation (multiplier * prime)) :
    Representation prime := by
  by_cases multiplierOne : multiplier = 1
  · subst multiplier
    simpa using input
  · have multiplierGreaterOne : 1 < multiplier := by omega
    by_cases remainderZero : multiplier % 2 = 0
    · have multiplierEven : Even multiplier := by
        refine ⟨multiplier / 2, ?_⟩
        have divisionEquation := Nat.mod_add_div multiplier 2
        rw [remainderZero] at divisionEquation
        omega
      let next := evenDescentStep prime multiplier multiplierPositive
        multiplierEven input
      exact descendPrime prime primeIsPrime next.multiplier next.positive
        (next.below.trans multiplierBelowPrime) next.representation
    · have multiplierOdd : Odd multiplier :=
        ⟨multiplier / 2, by
          have remainderOne :=
            (Nat.mod_two_eq_zero_or_one multiplier).resolve_left remainderZero
          have divisionEquation := Nat.mod_add_div multiplier 2
          rw [remainderOne] at divisionEquation
          omega⟩
      let next := oddDescentStep prime multiplier primeIsPrime
        multiplierPositive multiplierBelowPrime multiplierGreaterOne
        multiplierOdd input
      exact descendPrime prime primeIsPrime next.multiplier next.positive
        (next.below.trans multiplierBelowPrime) next.representation
termination_by multiplier
decreasing_by
  · exact next.below
  · exact next.below

/-- Constructive four-square representation of a prime. -/
def primeRepresentation (prime : Nat) (primeIsPrime : Nat.Prime prime) :
    Representation prime := by
  let initial := primeInitialMultiple prime primeIsPrime
  exact descendPrime prime primeIsPrime initial.multiplier initial.positive
    initial.below initial.representation

/-- Euler multiplication of two checked representations. -/
def Representation.multiply {leftValue rightValue : Nat}
    (left : Representation leftValue) (right : Representation rightValue) :
    Representation (leftValue * rightValue) := by
  let firstProduct : Int :=
    (left.first : Int) * right.first -
      (left.second : Int) * right.second -
      (left.third : Int) * right.third -
      (left.fourth : Int) * right.fourth
  let secondProduct : Int :=
    (left.first : Int) * right.second +
      (left.second : Int) * right.first +
      (left.third : Int) * right.fourth -
      (left.fourth : Int) * right.third
  let thirdProduct : Int :=
    (left.first : Int) * right.third -
      (left.second : Int) * right.fourth +
      (left.third : Int) * right.first +
      (left.fourth : Int) * right.second
  let fourthProduct : Int :=
    (left.first : Int) * right.fourth +
      (left.second : Int) * right.third -
      (left.third : Int) * right.second +
      (left.fourth : Int) * right.first
  have leftCast :
      (left.first : Int) ^ 2 + (left.second : Int) ^ 2 +
          (left.third : Int) ^ 2 + (left.fourth : Int) ^ 2 =
        (leftValue : Int) := by
    have castEquation :=
      congrArg (fun value : Nat => (value : Int)) left.equation
    simpa only [Nat.cast_add, Nat.cast_pow] using castEquation
  have rightCast :
      (right.first : Int) ^ 2 + (right.second : Int) ^ 2 +
          (right.third : Int) ^ 2 + (right.fourth : Int) ^ 2 =
        (rightValue : Int) := by
    have castEquation :=
      congrArg (fun value : Nat => (value : Int)) right.equation
    simpa only [Nat.cast_add, Nat.cast_pow] using castEquation
  have productNorm :
      firstProduct ^ 2 + secondProduct ^ 2 +
          thirdProduct ^ 2 + fourthProduct ^ 2 =
        (leftValue : Int) * (rightValue : Int) := by
    calc
      firstProduct ^ 2 + secondProduct ^ 2 +
            thirdProduct ^ 2 + fourthProduct ^ 2 =
          ((left.first : Int) ^ 2 + (left.second : Int) ^ 2 +
            (left.third : Int) ^ 2 + (left.fourth : Int) ^ 2) *
          ((right.first : Int) ^ 2 + (right.second : Int) ^ 2 +
            (right.third : Int) ^ 2 + (right.fourth : Int) ^ 2) := by
        unfold firstProduct secondProduct thirdProduct fourthProduct
        ring1
      _ = (leftValue : Int) * (rightValue : Int) := by
        rw [leftCast, rightCast]
  have naturalProductNorm :
      firstProduct.natAbs ^ 2 + secondProduct.natAbs ^ 2 +
          thirdProduct.natAbs ^ 2 + fourthProduct.natAbs ^ 2 =
        leftValue * rightValue := by
    apply Int.natCast_inj.mp
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Int.natAbs_pow_two] using productNorm
  exact
    ⟨firstProduct.natAbs, secondProduct.natAbs, thirdProduct.natAbs,
      fourthProduct.natAbs, naturalProductNorm⟩

/-- Fully executable constructive Lagrange algorithm.  Composite inputs are
split by a displayed bounded proper-factor search, and prime inputs use the finite
residue search followed by descent above. -/
def naturalRepresentation : (value : Nat) → Representation value :=
  Nat.strongRec (motive := fun value => Representation value) fun value recurse => by
    by_cases valueZero : value = 0
    · subst value
      exact ⟨0, 0, 0, 0, rfl⟩
    · by_cases valueOne : value = 1
      · subst value
        exact ⟨1, 0, 0, 0, by decide⟩
      · have valueAtLeastTwo : 2 ≤ value := by omega
        let acceptedFactor : Nat → Bool := fun factor =>
          decide (2 ≤ factor) && decide (value % factor = 0)
        cases factorFound : (List.range value).find? acceptedFactor with
        | none =>
            have rejected :=
              QuotientFreeList.find?_eq_none.mp factorFound
            have valuePrime : Nat.Prime value := by
              apply Nat.prime_def.mpr
              refine ⟨valueAtLeastTwo, ?_⟩
              intro divisor divisorDivides
              by_cases divisorOne : divisor = 1
              · exact Or.inl divisorOne
              · by_cases divisorValue : divisor = value
                · exact Or.inr divisorValue
                · have divisorPositive : 0 < divisor := by
                    by_contra divisorNotPositive
                    have divisorZero : divisor = 0 := by omega
                    subst divisor
                    exact valueZero
                      (Nat.eq_zero_of_zero_dvd divisorDivides)
                  have divisorAtLeastTwo : 2 ≤ divisor := by omega
                  have divisorAtMostValue : divisor ≤ value :=
                    Nat.le_of_dvd (Nat.zero_lt_of_ne_zero valueZero)
                      divisorDivides
                  have divisorBelow : divisor < value := by omega
                  have divisorMember : divisor ∈ List.range value :=
                    QuotientFreeList.mem_range.mpr divisorBelow
                  have divisorRejected := rejected divisor divisorMember
                  have divisorModulo : value % divisor = 0 :=
                    Nat.mod_eq_zero_of_dvd divisorDivides
                  have divisorAccepted : acceptedFactor divisor = true := by
                    simp only [acceptedFactor, Bool.and_eq_true,
                      decide_eq_true_eq]
                    exact ⟨divisorAtLeastTwo, divisorModulo⟩
                  rw [divisorAccepted] at divisorRejected
                  exact False.elim (Bool.noConfusion divisorRejected)
            exact primeRepresentation value valuePrime
        | some factor =>
            have factorAccepted := find?_eq_some_accepts factorFound
            have factorMember := find?_eq_some_mem factorFound
            have factorConditions : 2 ≤ factor ∧ value % factor = 0 := by
              simpa only [acceptedFactor, Bool.and_eq_true,
                decide_eq_true_eq] using factorAccepted
            have factorBelow : factor < value :=
              QuotientFreeList.mem_range.mp factorMember
            have factorDivides : factor ∣ value :=
              Nat.dvd_of_mod_eq_zero factorConditions.2
            let cofactor := value / factor
            have factorGreaterOne : 1 < factor := by omega
            have cofactorBelow : cofactor < value :=
              Nat.div_lt_self (Nat.zero_lt_of_ne_zero valueZero)
                factorGreaterOne
            have productEquation : factor * cofactor = value :=
              Nat.mul_div_cancel' factorDivides
            let factorRepresentation := recurse factor factorBelow
            let cofactorRepresentation := recurse cofactor cofactorBelow
            exact productEquation ▸
              factorRepresentation.multiply cofactorRepresentation

end RFAP.ConstructiveFourSquares
