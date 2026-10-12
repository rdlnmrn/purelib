module

public import Purelib.NumberTheory.FourSquares.Basic
public import Purelib.NumberTheory.Prime.Basic
public import Purelib.Algebra.Modular.Fin
public import Purelib.Data.List.OfFn.Basic
public import Purelib.Data.List.OfFn.Nodup
public import Purelib.Data.List.Flatten
public import Purelib.Data.List.Intersection
public import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
public import Purelib.Data.List.Search
import Purelib.Data.Nat.Coprime.Basic
public import Purelib.Data.Nat.Divisibility
import Purelib.Data.Nat.Divisibility.IntCast
public import Purelib.Data.Nat.Division
import Purelib.Data.Nat.GCD.Extended
import Purelib.Data.Nat.Multiplication
public import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Parity
public import Purelib.Data.Nat.Remainder.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained odd-prime residue tables and checked square seeds

The original bounded residue tables keep their index order and natural values.
The same pair scan selects its first accepted residue equation and retains the
original quotient cache and certified represented multiple of the prime.
-/

open Purelib
open Purelib.NumberTheory
open Purelib.Data.Nat
open Purelib.Data.List

-- Preserve the original nominal PrimeSeed.PrimeSeed owner path.

namespace Purelib.NumberTheory.FourSquares

/-- Use the explicit modular commutative-ring structure on the finite residue carrier. -/
local instance (prime : Nat) [NeZero prime] : CommRing (Fin prime) :=
  Algebra.Modular.Fin.finCommRing prime

namespace PrimeSeed

/-- The half-table length is at most the positive modulus.

The original quotient by two of the successor is strictly below that
successor. The retained positivity identifies its predecessor upper bound
without adding generic division preprocessing to the scalar proof. -/
public theorem halfCount_le_prime {prime : Nat}
    (primePositive : 0 < prime) : (prime + 1) / 2 ≤ prime := by
  exact Nat.le_of_lt_succ (Division.div_lt_self
    (Nat.lt_trans primePositive (Nat.lt_succ_self prime)) (by decide))

end PrimeSeed

namespace PrimeSeed

/-- For an odd modulus, twice the half-table length is the modulus plus one.

The retained oddness witness identifies the original successor as twice
the displayed half successor. Direct cancellation of that original multiple
recovers both occurrences of the unchanged half-table quotient. -/
public theorem odd_halfCount (prime : Nat) (primeOdd : Parity.Odd prime) :
    (prime + 1) / 2 + (prime + 1) / 2 = prime + 1 := by
  rcases primeOdd with ⟨half, equation⟩
  have doubledSuccessor : prime + 1 = 2 * (half + 1) := by
    rw [equation, Nat.mul_succ, Nat.add_assoc]
  have retainedHalf : (prime + 1) / 2 = half + 1 :=
    (congrArg (fun value : Nat => value / 2) doubledSuccessor).trans
      (Division.mul_div_cancel_left (half + 1) (by decide))
  exact (congrArg (fun count : Nat => count + count) retainedHalf).trans
    ((Nat.two_mul (half + 1)).symm.trans doubledSuccessor.symm)

end PrimeSeed

namespace PrimeSeed

/-- A zero product modulo a prime has a zero factor.

The explicit Euclidean gcd certificate proves the directed cancellation step. -/
private theorem finPrime_mul_eq_zero
    (prime : Nat) [NeZero prime] (primeIsPrime : NumberTheory.Prime prime)
    (left right : Fin prime) (productZero : left * right = 0) :
    left = 0 ∨ right = 0 := by
  have valueZero := congrArg Fin.val productZero
  change (left.val * right.val) % prime = 0 at valueZero
  have primeDivides : prime ∣ left.val * right.val :=
    Divisibility.of_mod_eq_zero valueZero
  by_cases leftModuloZero : left.val % prime = 0
  · left
    apply Fin.ext
    change left.val = 0 % prime
    exact (Remainder.mod_eq_of_lt left.isLt).symm.trans leftModuloZero
  · have leftDivides : ¬ prime ∣ left.val := fun divides =>
      leftModuloZero (Divisibility.mod_eq_zero_of_dvd divides)
    right
    let gcdResult := GCD.Extended.compute prime left.val
    have gcdSpecification := GCD.Extended.compute_spec prime left.val
    have gcdEqualsOne : gcdResult.gcd = 1 := by
      rcases primeIsPrime.eq_one_or_self_of_dvd gcdResult.gcd
          gcdSpecification.2.1 with equalsOne | equalsPrime
      · exact equalsOne
      · have primeDividesLeft : prime ∣ left.val := by
          change (GCD.Extended.compute prime left.val).gcd = prime at equalsPrime
          have retained := gcdSpecification.2.2
          rw [equalsPrime] at retained
          exact retained
        exact False.elim (leftDivides primeDividesLeft)
    let certificate : Coprime.Basic.CoprimeCertificate prime left.val :=
      { left := gcdResult.left
        right := gcdResult.right
        identity := by
          rw [← gcdSpecification.1, gcdEqualsOne]
          rfl }
    have reorderedDivides : prime ∣ right.val * left.val := by
      rw [Nat.mul_comm]
      exact primeDivides
    have rightDivides : prime ∣ right.val :=
      certificate.dvd_of_dvd_mul_right reorderedDivides
    apply Fin.ext
    change right.val = 0 % prime
    exact (Remainder.mod_eq_of_lt right.isLt).symm.trans
      (Divisibility.mod_eq_zero_of_dvd rightDivides)

end PrimeSeed

namespace PrimeSeed

/-- Embed a retained half-table index into the original positive residue modulus.

The original index value is embedded unchanged. Its retained finite bound
composes with the direct upper bound for the same original half-table quotient. -/
@[expose] public def boundedSmallRoot (prime : Nat) (primePositive : 0 < prime)
    (index : Fin ((prime + 1) / 2)) : Fin prime :=
  ⟨index.val, Nat.lt_of_lt_of_le index.isLt (halfCount_le_prime primePositive)⟩

end PrimeSeed

namespace PrimeSeed

/-- Read the bounded representative of a retained half-table index. -/
private def smallRoot (prime : Nat) (primePositive : 0 < prime)
    (index : Fin ((prime + 1) / 2)) : Fin prime :=
  boundedSmallRoot prime primePositive index

end PrimeSeed

namespace PrimeSeed

/-- The residue embedding preserves the original half-table index value.

The retained residue constructor stores exactly the supplied original
natural index. Its additional modulus bound changes no executable value. -/
public theorem boundedSmallRoot_value (prime : Nat) (primePositive : 0 < prime)
    (index : Fin ((prime + 1) / 2)) :
    (boundedSmallRoot prime primePositive index).val = index.val := rfl

end PrimeSeed

namespace PrimeSeed

/-- The small-root helper preserves the original half-table index value. -/
private theorem smallRoot_value (prime : Nat)
    (primePositive : 0 < prime) (index : Fin ((prime + 1) / 2)) :
    (smallRoot prime primePositive index).val = index.val := rfl

end PrimeSeed

namespace PrimeSeed

/-- The square map is injective on the displayed representatives
`0, ..., (p-1)/2` for an odd prime.

The original finite ring factors the difference of the two squares.
Primality forces a zero factor, and the retained half-table bounds distinguish
the sum case while preserving both original bounded indices. -/
private theorem smallSquare_injective
    (prime : Nat) [NeZero prime] (primeIsPrime : NumberTheory.Prime prime)
    (primeOdd : Parity.Odd prime) :
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
      have leftBound := left.isLt
      have rightBound := right.isLt
      have retained : left.val + right.val + 1 + 1 ≤ prime + 1 := by
        calc
          left.val + right.val + 1 + 1 = (left.val + 1) + (right.val + 1) := by
            exact ((congrArg (· + 1) (Nat.add_assoc left.val right.val 1)).trans
              (congrArg (fun value => left.val + value + 1) (Nat.add_comm right.val 1))).trans
                ((congrArg (· + 1) (Nat.add_assoc left.val 1 right.val).symm).trans
                  (Nat.add_assoc (left.val + 1) right.val 1))
          _ ≤ (prime + 1) / 2 + (prime + 1) / 2 :=
            Nat.add_le_add leftBound rightBound
          _ = prime + 1 := count
      exact Nat.lt_of_succ_le (Nat.le_of_succ_le_succ retained)
    have valuesZero := congrArg Fin.val sumZero
    rw [Fin.val_add, smallRoot_value prime primeIsPrime.pos,
      smallRoot_value prime primeIsPrime.pos,
      Remainder.mod_eq_of_lt sumBelow] at valuesZero
    have coordinatesZero : left.val = 0 ∧ right.val = 0 :=
      Nat.add_eq_zero_iff.mp valuesZero
    exact Fin.ext (coordinatesZero.1.trans coordinatesZero.2.symm)

end PrimeSeed

namespace PrimeSeed

/-- Materialize the bounded square residues in half-table index order.

The indices below `(prime + 1) / 2` occur once in ascending order. Each
entry squares the corresponding bounded residue in `Fin prime`, with
the supplied positivity certificate establishing its embedding. -/
private def primeSquareValues (prime : Nat) [NeZero prime]
    (primePositive : 0 < prime) :
    List (Fin prime) :=
  List.ofFn (fun index : Fin ((prime + 1) / 2) =>
    smallRoot prime primePositive index ^ 2)

end PrimeSeed

namespace PrimeSeed

/-- The small-square residue table has no repeated entry for an odd prime.

The original table materializes its bounded square family in index order.
The injectivity certificate for the same odd prime rules out repeated entries
without changing the family or replacing its retained finite indices. -/
public theorem primeSquareValues_nodup
    (prime : Nat) [NeZero prime] (primeIsPrime : NumberTheory.Prime prime)
    (primeOdd : Parity.Odd prime) :
    (List.ofFn (fun index : Fin ((prime + 1) / 2) =>
      boundedSmallRoot prime primeIsPrime.pos index ^ 2)).Nodup := by
  change (primeSquareValues prime primeIsPrime.pos).Nodup
  exact OfFn.Nodup.nodup_ofFn_of_injective
    (smallSquare_injective prime primeIsPrime primeOdd)

end PrimeSeed

namespace PrimeSeed

/-- Subtract each small-square residue from the supplied target.

Each entry is the target plus the negation of the corresponding square-table
entry. Mapping preserves the enumeration order, modulus and supplied target. -/
private def translatedPrimeSquareValues
    (prime : Nat) [NeZero prime] (primePositive : 0 < prime)
    (target : Fin prime) :
    List (Fin prime) :=
  (primeSquareValues prime primePositive).map (fun value => target + -value)

end PrimeSeed

namespace PrimeSeed

/-- Subtracting residues from one fixed target is injective.

The retained finite addition cancels the unchanged target. Negating both
resulting scalar values twice recovers the same original residue owners. -/
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

end PrimeSeed

namespace PrimeSeed

/-- Translating the small-square residue table preserves distinctness for an odd prime.

The original map retains the same target-minus-entry computation.
Injectivity transports the checked distinctness of the original odd-prime
square table without changing either list or its enumeration order. -/
public theorem translatedPrimeSquareValues_nodup
    (prime : Nat) [NeZero prime] (primeIsPrime : NumberTheory.Prime prime)
    (primeOdd : Parity.Odd prime) (target : Fin prime) :
    ((List.ofFn (fun index : Fin ((prime + 1) / 2) =>
      boundedSmallRoot prime primeIsPrime.pos index ^ 2)).map
        (fun value => target + -value)).Nodup := by
  change (translatedPrimeSquareValues prime primeIsPrime.pos target).Nodup
  unfold translatedPrimeSquareValues
  exact Data.List.Nodup.nodup_map_of_injective
    (translate_injective target)
    (primeSquareValues_nodup prime primeIsPrime primeOdd)

end PrimeSeed

@[expose] public section

set_option genInjectivity false in
/-- Retain two bounded roots and a certified cached square-sum quotient.

Both selected roots come from the original ordered bounded pair scan.
The original quotient is retained as the multiplier, with its equation and
the original strict bounds on the same two selected natural values. -/
structure PrimeSeed (prime : Nat) where
  /-- The first retained natural square root. -/ first : Nat
  /-- The second retained natural square root. -/ second : Nat
  /-- The cached quotient of the square sum plus one by the prime. -/ multiplier : Nat
  /-- Twice the first retained root is strictly below the prime. -/ firstSmall : 2 * first < prime
  /-- Twice the second retained root is strictly below the prime. -/ secondSmall : 2 * second < prime
  /-- The two retained squares plus one equal the cached multiplier times the prime. -/ equation : first ^ 2 + second ^
    2 + 1 = multiplier * prime

constructive_injectivity PrimeSeed

end

namespace PrimeSeed.mk

end PrimeSeed.mk

namespace PrimeSeed.mk

end PrimeSeed.mk

namespace PrimeSeed

/-- Select the first accepted original bounded pair for an odd natural prime.

The original duplicate-free tables certify that the displayed pair scan
accepts an entry. Its first accepted pair supplies the retained indices and
roots, and the original natural quotient is cached without another search. -/
@[expose] public def primeSeed
    (prime : Nat) (primeIsPrime : NumberTheory.Prime prime) (primeNotTwo : prime ≠ 2) :
    PrimeSeed prime := by
  letI : NeZero prime := ⟨primeIsPrime.ne_zero⟩
  let squareValues : List (Fin prime) :=
    List.ofFn (fun index : Fin ((prime + 1) / 2) =>
      boundedSmallRoot prime primeIsPrime.pos index ^ 2)
  let target : Fin prime := -1
  let translated := squareValues.map (fun value => target + -value)
  let carrier : List (Fin prime) := List.ofFn (fun value => value)
  have primeOdd : Parity.Odd prime := primeIsPrime.odd_of_ne_two primeNotTwo
  have squareNodup : squareValues.Nodup :=
    primeSquareValues_nodup prime primeIsPrime primeOdd
  have translatedNodup : translated.Nodup :=
    translatedPrimeSquareValues_nodup prime primeIsPrime primeOdd target
  have carrierNodup : carrier.Nodup :=
    OfFn.Nodup.nodup_ofFn_of_injective (fun _ _ equal => equal)
  have carrierComplete : ∀ value : Fin prime, value ∈ carrier := by
    intro value
    exact OfFn.Basic.mem_ofFn.mpr ⟨value, rfl⟩
  have oversized : carrier.length < squareValues.length + translated.length := by
    unfold carrier squareValues translated
    rw [OfFn.Basic.length_ofFn, Map.length_map,
      OfFn.Basic.length_ofFn, odd_halfCount prime primeOdd]
    exact Nat.lt_succ_self prime
  have intersectionNonempty :
      Intersection.firstIntersection? squareValues translated ≠ none :=
    Intersection.firstIntersection?_ne_none_of_length_gt
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
      (boundedSmallRoot prime primeIsPrime.pos pair.1 ^ 2 +
          boundedSmallRoot prime primeIsPrime.pos pair.2 ^ 2 + 1 = 0)
  have searchNonempty : pairs.find? accepted ≠ none := by
    intro searchEmpty
    have rejected :=
      (Search.find?_eq_none.mp searchEmpty)
    cases found : Intersection.firstIntersection? squareValues translated with
    | none => exact intersectionNonempty found
    | some common =>
      have commonMembers :=
        Intersection.firstIntersection?_eq_some found
      have firstMember := commonMembers.1
      unfold squareValues at firstMember
      rcases OfFn.Basic.mem_ofFn.mp firstMember with ⟨firstIndex, firstSquare⟩
      have translatedMember := commonMembers.2
      unfold translated at translatedMember
      rcases Map.mem_map.mp translatedMember with
        ⟨secondSquare, secondSquareMember, translatedSquare⟩
      unfold squareValues at secondSquareMember
      rcases OfFn.Basic.mem_ofFn.mp secondSquareMember with ⟨secondIndex, secondSquareEqual⟩
      have residueEquation :
            boundedSmallRoot prime primeIsPrime.pos firstIndex ^ 2 +
                boundedSmallRoot prime primeIsPrime.pos secondIndex ^ 2 + 1 = 0 := by
          calc
            boundedSmallRoot prime primeIsPrime.pos firstIndex ^ 2 +
                  boundedSmallRoot prime primeIsPrime.pos secondIndex ^ 2 + 1 =
                common + secondSquare + 1 := by
              rw [firstSquare, secondSquareEqual]
            _ = 0 := by
              rw [← translatedSquare]
              unfold target
              ring1
      have pairMember : (firstIndex, secondIndex) ∈ pairs := by
        unfold pairs
        apply Flatten.mem_flatMap.mpr
        refine ⟨firstIndex, ?_, ?_⟩
        · unfold indices
          exact OfFn.Basic.mem_ofFn.mpr ⟨firstIndex, rfl⟩
        · apply Map.mem_map.mpr
          refine ⟨secondIndex, ?_, rfl⟩
          unfold indices
          exact OfFn.Basic.mem_ofFn.mpr ⟨secondIndex, rfl⟩
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
        Search.find?_eq_some_accepts_certificate pairFound
      have residueEquation :
          boundedSmallRoot prime primeIsPrime.pos pair.1 ^ 2 +
              boundedSmallRoot prime primeIsPrime.pos pair.2 ^ 2 + 1 = 0 := by
        unfold accepted at pairAccepted
        exact of_decide_eq_true pairAccepted
      have firstSmall : 2 * pair.1.val < prime := by
        exact Order.two_mul_lt_of_lt_half
          (odd_halfCount prime primeOdd) pair.1.isLt
      have secondSmall : 2 * pair.2.val < prime := by
        exact Order.two_mul_lt_of_lt_half
          (odd_halfCount prime primeOdd) pair.2.isLt
      have finOneValue : (1 : Fin prime).val = 1 := by
        change 1 % prime = 1
        exact Remainder.mod_eq_of_lt primeIsPrime.one_lt
      have moduloEquation := congrArg Fin.val residueEquation
      rewrite [Algebra.Modular.Fin.fin_pow_two,
        Algebra.Modular.Fin.fin_pow_two] at moduloEquation
      simp only [Fin.val_add, Fin.val_mul, Fin.val_zero,
        boundedSmallRoot_value prime primeIsPrime.pos] at moduloEquation
      rw [finOneValue] at moduloEquation
      have moduloZero :
          (pair.1.val ^ 2 + pair.2.val ^ 2 + 1) % prime = 0 := by
        calc
          (pair.1.val ^ 2 + pair.2.val ^ 2 + 1) % prime =
              (((pair.1.val ^ 2) % prime +
                  (pair.2.val ^ 2) % prime) % prime +
                1 % prime) % prime := by
            have sumReduction :
                ((pair.1.val ^ 2) % prime + (pair.2.val ^ 2) % prime) % prime =
                  (pair.1.val ^ 2 + pair.2.val ^ 2) % prime :=
              (Remainder.Arithmetic.add_mod_left _ _ _).trans
                (Remainder.Arithmetic.add_mod_right _ _ _)
            have outerReduction :
                ((pair.1.val ^ 2 + pair.2.val ^ 2) % prime + 1 % prime) % prime =
                  (pair.1.val ^ 2 + pair.2.val ^ 2 + 1) % prime :=
              (Remainder.Arithmetic.add_mod_left _ _ _).trans
                (Remainder.Arithmetic.add_mod_right _ _ _)
            exact ((congrArg (fun value : Nat => (value + 1 % prime) % prime)
              sumReduction).trans outerReduction).symm
          _ = (((pair.1.val * pair.1.val) % prime +
                  (pair.2.val * pair.2.val) % prime) % prime +
                1) % prime := by
            rw [Remainder.mod_eq_of_lt primeIsPrime.one_lt]
            rw [Multiplication.pow_two, Multiplication.pow_two]
          _ = 0 := moduloEquation
      have divides := Divisibility.of_mod_eq_zero moduloZero
      exact
        { first := pair.1.val
          second := pair.2.val
          multiplier :=
            (pair.1.val ^ 2 + pair.2.val ^ 2 + 1) / prime
          firstSmall := firstSmall
          secondSmall := secondSmall
          equation := (Division.div_mul_cancel divides).symm }

end PrimeSeed

namespace PrimeSeed

/-- The retained square seed supplies bounded roots and an original divisibility witness.

The displayed roots are read directly from the retained executable seed.
Its original cached multiplier supplies the divisibility witness; no new search
or witness selection is performed. -/
public theorem prime_seed
    (prime : Nat) (primeIsPrime : NumberTheory.Prime prime) (primeNotTwo : prime ≠ 2) :
    ∃ first second : Nat,
      2 * first < prime ∧ 2 * second < prime ∧
        prime ∣ first ^ 2 + second ^ 2 + 1 := by
  let seed := primeSeed prime primeIsPrime primeNotTwo
  refine ⟨seed.first, seed.second, seed.firstSmall, seed.secondSmall, ?_⟩
  exact ⟨seed.multiplier, seed.equation.trans (Nat.mul_comm _ _)⟩

end PrimeSeed

@[expose] public section

namespace PrimeSeed

set_option genInjectivity false in
/-- Retain a positive bounded multiplier and its indexed four-square representation.

The multiplier and its original indexed representation are retained
together. Its strict positivity and upper bound concern that same multiplier
and the supplied original modulus, rather than another represented value. -/
structure BoundedMultiple (modulus : Nat) where
  /-- The retained multiplier of the original modulus. -/ multiplier : Nat
  /-- The retained multiplier is positive. -/ positive : 0 < multiplier
  /-- The retained multiplier is strictly below the modulus. -/ below : multiplier < modulus
  /-- The retained four-square representation of this exact multiplier times the original modulus. -/ representation :
    Basic.Representation (multiplier * modulus)

constructive_injectivity BoundedMultiple

end PrimeSeed

end

namespace PrimeSeed.BoundedMultiple.mk

end PrimeSeed.BoundedMultiple.mk

namespace PrimeSeed.BoundedMultiple.mk

end PrimeSeed.BoundedMultiple.mk

namespace PrimeSeed

/-- An original prime has a represented positive multiple with multiplier below it.

The exceptional prime two uses the original fixed roots. Every other
prime retains the selected square seed and its same quotient cache, together
with explicit bounds certifying the original represented prime multiple. -/
@[expose] public def primeInitialMultiple
    (prime : Nat) (primeIsPrime : NumberTheory.Prime prime) :
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
    have firstBelow : first ≤ prime := by omega0
    have secondBelow : second ≤ prime := by omega0
    have firstSquareBound : first * first ≤ first * prime :=
      Nat.mul_le_mul_left first firstBelow
    have secondSquareBound : second * second ≤ second * prime :=
      Nat.mul_le_mul_left second secondBelow
    have rootsSumBelow : first + second < prime := by omega0
    have sumBound :
        first ^ 2 + second ^ 2 + 1 ≤ (first + second) * prime + 1 := by
      rw [Multiplication.pow_two, Multiplication.pow_two, Multiplication.right_distrib]
      omega0
    have scaledSuccessorBelow :
        (first + second) * prime + 1 < (first + second + 1) * prime := by
      calc
        (first + second) * prime + 1 <
            (first + second) * prime + prime :=
          Nat.add_lt_add_left primeIsPrime.one_lt _
        _ = (first + second + 1) * prime := by
          exact (congrArg (fun value => (first + second) * prime + value)
            (Nat.one_mul prime).symm).trans
              (Multiplication.right_distrib (first + second) 1 prime).symm
    have scaledSuccessorBound :
        (first + second + 1) * prime ≤ prime * prime :=
      Nat.mul_le_mul_right prime (Nat.succ_le_iff.mpr rootsSumBelow)
    have squareSumBelow :
        first ^ 2 + second ^ 2 + 1 < prime * prime :=
      Nat.lt_of_le_of_lt sumBound
        (Nat.lt_of_lt_of_le scaledSuccessorBelow scaledSuccessorBound)
    have multiplierPositive : 0 < multiplier := by
      apply Nat.zero_lt_of_ne_zero
      intro vanishes
      rw [vanishes, Nat.zero_mul] at multipleEquation
      exact Nat.noConfusion multipleEquation
    have multiplierBelow : multiplier < prime := by
      apply Order.lt_of_mul_lt_mul_left (factor := prime)
      rewrite [Nat.mul_comm prime multiplier, ← multipleEquation]
      exact squareSumBelow
    exact
      { multiplier := multiplier
        positive := multiplierPositive
        below := multiplierBelow
        representation :=
          ⟨first, second, 1, 0,
            by
              change first ^ 2 + second ^ 2 + 1 + 0 = multiplier * prime
              exact (Nat.add_zero _).trans multipleEquation⟩ }

end PrimeSeed

end Purelib.NumberTheory.FourSquares
