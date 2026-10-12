module

import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Quaternion.Projective.Basic
public import Purelib.Algebra.Quaternion.Projective.Rational.Surjectivity
import Purelib.Data.List.Pairwise
import Purelib.NumberTheory.FourSquares.Rational
import Purelib.NumberTheory.Prime.FinitePacks
import Purelib.NumberTheory.SquareClass.Rational.Basic
public import Purelib.NumberTheory.SquareClass.Rational.Separation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Quaternion.Projective

open Purelib.Algebra.Quaternion.Projective.Rational

open Purelib.Data.Rat

open Purelib.NumberTheory.FourSquares

open Purelib.NumberTheory.Prime.FinitePacks.SquareClassPacks

open Purelib.NumberTheory.Prime
open Purelib.Data.List

open Purelib.NumberTheory.SquareClass.Rational.Basic.TheoremSixtyTwo

open Purelib.NumberTheory.SquareClass.Rational

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

namespace Purelib.Algebra.Quaternion.Projective.Rational.Packs

namespace SquareClassPacks

set_option genInjectivity false in
/-- A positive prime square class with its retained rational quaternion preimage.

The entry stores the prime, its exact positive target, the four-square preimage, and equalities linking all retained
data to that construction. -/
structure PositiveSquareClassEntry where
  /-- The retained explicit Euclid prime. -/ prime : EuclidPrime
  /-- The retained positive rational square-class target. -/ target : PositiveSquareClassRepresentative
  /-- The target is exactly the positive square class constructed from the retained prime. -/ target_eq : target =
    Separation.SquareClassPacks.positivePrimeClass prime
  /-- The retained non-null rational quaternion preimage. -/ preimage : Basic.NonNullProportion Fraction.Rational
  /-- The preimage is exactly the output of the finite Lagrange four-square construction for this target. -/ preimage_eq
    : preimage = Surjectivity.TheoremSixtyTwo.preimage
    Rational.TheoremSixtyTwo.lagrangeAlgorithm target
  /-- The preimage quadrance-class value equals the retained target value. -/ quadranceClass_value :
    (SquareClass.NonNullProportion.quadranceClass preimage).value =
    target.representative.value

constructive_injectivity PositiveSquareClassEntry

section
open Purelib.Algebra.Quaternion.Projective.Rational.Packs.SquareClassPacks
/-- Construct and retain the quaternion preimage of a displayed Euclid-prime class.

The finite four-square algorithm supplies a preimage whose quadrance-class value equals the positive prime target. -/
@[expose] def positiveSquareClassEntry
  (prime : EuclidPrime) :
    PositiveSquareClassEntry where
  prime := prime
  target := Separation.SquareClassPacks.positivePrimeClass prime
  target_eq := rfl
  preimage := Surjectivity.TheoremSixtyTwo.preimage
    Rational.TheoremSixtyTwo.lagrangeAlgorithm (Separation.SquareClassPacks.positivePrimeClass prime)
  preimage_eq := rfl
  quadranceClass_value :=
    Surjectivity.TheoremSixtyTwo.preimage_quadranceClass
      Rational.TheoremSixtyTwo.lagrangeAlgorithm (Separation.SquareClassPacks.positivePrimeClass prime)

/-- The retained positive target value equals the rational cast of its stored prime. -/
theorem
  PositiveSquareClassEntry.target_value
    (entry : PositiveSquareClassEntry) :
    entry.target.representative.value = (entry.prime.value : Fraction.Rational) := by
  rw [entry.target_eq]
  rfl

end

/-- Distinct displayed Euclid primes give inequivalent positive square-class entries.

The inequivalence concerns their retained target representatives. -/
theorem
  entries_of_distinct_primes_not_equivalent
    (left right : EuclidPrime) (different : left ≠ right) :
    ¬ (positiveSquareClassEntry left).target.representative.Equivalent
      (positiveSquareClassEntry right).target.representative :=
  Separation.SquareClassPacks.distinct_primes_not_equivalent left right different

open Purelib.Algebra.Quaternion.Projective.Rational.Packs.SquareClassPacks in
set_option genInjectivity false in
/-- A finite requested number of pairwise inequivalent positive square-class entries.

The list retains each prime target and its quaternion preimage, together with exact length and pairwise inequivalence
certificates. -/
structure DistinctPositiveSquareClassPack
  (count : Nat) where
  /-- The retained finite list of prime targets and their quaternion preimages. -/ entries : List
    PositiveSquareClassEntry
  /-- The entry count equals the requested natural cardinality. -/ length_eq : entries.length = count
  /-- Distinct list positions retain inequivalent target square classes. -/ pairwiseInequivalent : entries.Pairwise fun
    left right =>
    ¬ left.target.representative.Equivalent right.target.representative

constructive_injectivity DistinctPositiveSquareClassPack

open Purelib.Algebra.Quaternion.Projective.Rational.Packs.SquareClassPacks
/-- Construct exactly the requested number of inequivalent positive square-class entries.

A finite Euclid-prime list is mapped to retained four-square preimages, preserving its certified length and distinct
square classes. -/
@[expose] def
  distinctPositiveSquareClassPack (count :
  Nat) :
    DistinctPositiveSquareClassPack count where
  entries := (FinitePacks.SquareClassPacks.euclidPrimes count).map positiveSquareClassEntry
  length_eq := by
    rewrite [Map.length_map]
    exact FinitePacks.SquareClassPacks.euclidPrimes_length count
  pairwiseInequivalent := by
    apply Pairwise.pairwise_map.mpr
    apply (FinitePacks.SquareClassPacks.euclidPrimes_nodup count).imp
    intro left right different
    exact entries_of_distinct_primes_not_equivalent left right different

/-- Each retained pack entry realizes its target square-class value through its stored preimage.

The equality is the entry's own retained certificate, independent of how membership in the pack was established. -/
theorem
  distinctPositiveSquareClassPack_entry_realizes
    (count : Nat) (entry : PositiveSquareClassEntry)
    (_member : entry ∈ (distinctPositiveSquareClassPack count).entries) :
    (SquareClass.NonNullProportion.quadranceClass entry.preimage).value =
      entry.target.representative.value :=
  entry.quadranceClass_value

end SquareClassPacks

end Purelib.Algebra.Quaternion.Projective.Rational.Packs

end
