module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
public import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.BoundaryFactorization (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Rational.Factorization (ConditionProfile)

open Purelib

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Data.List

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

set_option genInjectivity false in
/-- Complete finite refinements of one existing condition profile by an
additional displayed list.  Every output keeps the old relations, descended
through the new gcd pieces, and prepends the new relations. -/
structure ConditionProfileExtensions
    {source : Dense.Rational.Squarefree.Factor} {existing : List
      CoefficientPolynomial}
    (profile : ConditionProfile source existing)
    (conditions : List CoefficientPolynomial) where
  /-- The resulting profiles, indexed by the original source and the additional conditions prepended to the existing
    list. -/ profiles : List
    (ConditionProfile source (Data.List.prependConditions conditions existing))
  /-- At least one refined profile is retained. -/ nonempty : profiles ≠ []
  /-- At every displayed rational point, the original profile factor vanishes exactly when one retained refined factor
    vanishes. -/ rootCoverage : ∀ point : Fraction.Rational,
    profile.factor.polynomial.eval point = 0 ↔
      ∃ next ∈ profiles, next.factor.polynomial.eval point = 0

constructive_injectivity ConditionProfileExtensions

/-- Repeatedly split one existing profile against further conditions.  This
is the finite composition operation used to add cleared CCL-formula atoms
after denominator and box-edge profiling. -/
def extendProfileConditions
    {source : Dense.Rational.Squarefree.Factor} {existing : List
      CoefficientPolynomial}
    (profile : ConditionProfile source existing) :
    (conditions : List CoefficientPolynomial) →
      ConditionProfileExtensions profile conditions
  | [] =>
      { profiles := [profile]
        nonempty := List.cons_ne_nil _ _
        rootCoverage := by
          intro point
          constructor
          · intro zero
            exact ⟨profile, List.mem_cons_self, zero⟩
          · rintro ⟨next, member, zero⟩
            have equal : next = profile := Membership.mem_singleton.mp member
            subst next
            exact zero }
  | condition :: remaining => by
      let prior := extendProfileConditions profile remaining
      let profiles := prior.profiles.flatMap fun priorProfile =>
        priorProfile.extend condition
      have profilesNonempty : profiles ≠ [] := by
        cases priorProfilesEq : prior.profiles with
        | nil => exact (prior.nonempty priorProfilesEq).elim
        | cons priorProfile otherProfiles =>
            cases extensionEq : priorProfile.extend condition with
            | nil =>
                exact (priorProfile.extend_nonempty condition extensionEq).elim
            | cons next otherExtensions =>
                intro empty
                have priorMember : priorProfile ∈ prior.profiles := by
                  rw [priorProfilesEq]
                  exact List.mem_cons_self
                have nextMember : next ∈ priorProfile.extend condition := by
                  rw [extensionEq]
                  exact List.mem_cons_self
                have flattenedMember : next ∈ profiles :=
                  Data.List.Flatten.mem_flatMap.mpr
                    ⟨priorProfile, priorMember, nextMember⟩
                rw [empty] at flattenedMember
                exact List.not_mem_nil flattenedMember
      exact
        { profiles := profiles
          nonempty := profilesNonempty
          rootCoverage := by
            intro point
            constructor
            · intro profileZero
              rcases (prior.rootCoverage point).mp profileZero with
                ⟨priorProfile, priorMember, priorZero⟩
              rcases (priorProfile.extend_rootCoverage condition point).mp
                  priorZero with ⟨next, nextMember, nextZero⟩
              exact ⟨next,
                Data.List.Flatten.mem_flatMap.mpr
                  ⟨priorProfile, priorMember, nextMember⟩,
                nextZero⟩
            · rintro ⟨next, nextMember, nextZero⟩
              change ConditionProfile source
                (condition :: Data.List.prependConditions remaining existing) at next
              simp only [Data.List.prependConditions, -eq_self, -iff_self] at nextMember
              have flattenedMember : next ∈ profiles := nextMember
              rcases Flatten.mem_flatMap.mp flattenedMember with
                ⟨priorProfile, priorMember, nextMember⟩
              have priorZero :=
                (priorProfile.extend_rootCoverage condition point).mpr
                  ⟨next, nextMember, nextZero⟩
              exact (prior.rootCoverage point).mpr
                ⟨priorProfile, priorMember, priorZero⟩ }
end Purelib.Polynomial.Dense.Rational.Factorization

end
