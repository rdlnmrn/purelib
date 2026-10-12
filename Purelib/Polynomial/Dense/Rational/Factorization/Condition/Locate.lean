module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.BoundaryFactorization (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Rational.Factorization (ConditionProfile)
open Purelib.Polynomial.Dense.Rational.Squarefree (Factor)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite squarefree decomposition of coordinate polynomials

A boundary-curve gcd can have repeated parameter factors even when the
original Gaussian polynomial is squarefree.  This module removes that
special-case obligation: finite extended Euclid recursively decomposes any
nonzero positive-degree constructive-rational polynomial into displayed
squarefree occurrences.  The product identity and root coverage are proved
from finite coefficient candidates, never from evaluation over a carrier.
-/

namespace Purelib.Polynomial.Dense.Rational.Factorization

/-! ## Executable lookup in the final condition profiles -/

/-- Find the first final condition profile whose factor vanishes at the
displayed rational parameter. -/
def findRootProfileIndex
    {source : Factor} {conditions : List
      CoefficientPolynomial}
    (point : Fraction.Rational) :
    (profiles : List (ConditionProfile source conditions)) →
      Option (Fin profiles.length)
  | [] => none
  | profile :: remaining =>
      if profile.factor.polynomial.eval point = 0 then some 0
      else
        match findRootProfileIndex point remaining with
        | none => none
        | some index => some index.succ

/-- A successful finite scan returns an index whose original profile factor vanishes at the supplied point. -/
theorem findRootProfileIndex_sound
    {source : Factor} {conditions : List
      CoefficientPolynomial}
    (point : Fraction.Rational) :
    ∀ (profiles : List (ConditionProfile source conditions))
      (index : Fin profiles.length),
      findRootProfileIndex point profiles = some index →
        (profiles.get index).factor.polynomial.eval point = 0
  | [], index, _ => Fin.elim0 index
  | profile :: remaining, index, found => by
      by_cases headZero : profile.factor.polynomial.eval point = 0
      · rw [findRootProfileIndex, if_pos headZero] at found
        have indexZero : index = 0 := Option.some.inj found.symm
        subst index
        exact headZero
      · rw [findRootProfileIndex, if_neg headZero] at found
        cases recursive : findRootProfileIndex point remaining with
        | none => rw [recursive] at found; contradiction
        | some tailIndex =>
            rw [recursive] at found
            have indexSucc : index = tailIndex.succ :=
              Option.some.inj found.symm
            subst index
            exact findRootProfileIndex_sound point remaining tailIndex
              recursive

/-- A displayed vanishing factor in the profile list forces the finite index scan to succeed. -/
theorem findRootProfileIndex_ne_none_of_exists
    {source : Factor} {conditions : List
      CoefficientPolynomial}
    (point : Fraction.Rational) :
    ∀ (profiles : List (ConditionProfile source conditions)),
      (∃ profile ∈ profiles,
        profile.factor.polynomial.eval point = 0) →
        findRootProfileIndex point profiles ≠ none := by
  intro profiles witness
  induction profiles with
  | nil =>
      rcases witness with ⟨profile, member, _⟩
      exact (List.not_mem_nil member).elim
  | cons profile remaining inductionHypothesis =>
      by_cases headZero : profile.factor.polynomial.eval point = 0
      · intro impossible
        rewrite [findRootProfileIndex, if_pos headZero] at impossible
        cases impossible
      · have tailExists : ∃ tailProfile ∈ remaining,
            tailProfile.factor.polynomial.eval point = 0 := by
          rcases witness with ⟨found, member, zero⟩
          rcases Data.List.Membership.mem_cons.mp member with rfl | tailMember
          · exact (headZero zero).elim
          · exact ⟨found, tailMember, zero⟩
        have recursive := inductionHypothesis tailExists
        rw [findRootProfileIndex, if_neg headZero]
        cases found : findRootProfileIndex point remaining with
        | none => exact (recursive found).elim
        | some index =>
            intro impossible
            cases impossible

set_option genInjectivity false in
/-- Proof-bearing output of the executable condition-profile scan. -/
structure LocatedConditionProfile
    {source : Factor} {conditions : List
      CoefficientPolynomial}
    (profiles : Dense.Rational.Factorization.ConditionProfiles source conditions)
    (point : Fraction.Rational) where
  /-- The first retained condition profile found by the finite scan. -/ profile :
    ConditionProfile source conditions
  /-- The selected profile belongs to the exact original profile list. -/ member : profile ∈ profiles.profiles
  /-- The selected factor vanishes at the original displayed rational point. -/ zero : profile.factor.polynomial.eval
    point = 0

constructive_injectivity LocatedConditionProfile

namespace ConditionProfiles

/-- Assign a displayed rational source-factor root to the first final
condition profile containing it. -/
def locateRoot
    {source : Factor} {conditions : List
      CoefficientPolynomial}
    (profiles : Dense.Rational.Factorization.ConditionProfiles source conditions)
    (point : Fraction.Rational) (sourceZero : source.polynomial.eval point = 0) :
    LocatedConditionProfile profiles point := by
  have existsProfile := (profiles.rootCoverage point).mp sourceZero
  have foundNonempty := findRootProfileIndex_ne_none_of_exists point
    profiles.profiles existsProfile
  cases found : findRootProfileIndex point profiles.profiles with
  | none => exact (foundNonempty found).elim
  | some index =>
      exact
        { profile := profiles.profiles.get index
          member := List.get_mem profiles.profiles index
          zero := findRootProfileIndex_sound point profiles.profiles index
            found }

end ConditionProfiles
end Purelib.Polynomial.Dense.Rational.Factorization

end
