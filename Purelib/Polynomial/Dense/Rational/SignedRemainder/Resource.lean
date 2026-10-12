module
import Purelib.Data.List.Membership
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.Nat.Order

import Purelib.Algebra.Field.Resource.Magnitude
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Resource.Model
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Resource.Magnitude
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
import Purelib.Polynomial.Dense.Resource
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Rational (NormalizedPolynomial)

open Purelib

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Normalized finite Sturm calculations

This module runs the finite Sturm recursion on canonical reduced coefficient
records.  The finite chain and index calculations use the original Sturm programs
on the same canonical rational carrier.  The resource readbacks retain their
established theorem names without executing identity coefficient maps.  The accompanying recurrence bounds every
coefficient in every chain
member from the two displayed source polynomials.
-/

namespace Purelib.RootIsolation.Sturm.Normalized
open Purelib.Algebra.Polynomial.DensePolynomial

/-! ## Normalized endpoint execution and winding cost -/

end Purelib.RootIsolation.Sturm.Normalized

section
open Purelib.Algebra.Polynomial.DensePolynomial

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource

open _root_.Purelib.RootIsolation.Sturm.Normalized
/-- Every member of the well-founded signed chain fits the larger input coefficient count. -/
private theorem
  signedRemainderChainWF_slots_le :
    ∀ (p q candidate : NormalizedPolynomial),
      candidate ∈ Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF p q →
      candidate.coeffs.length ≤ max p.coeffs.length q.coeffs.length := by
  intro p q
  generalize degreeEquation : q.degreeCount = degree
  induction degree using Nat.strong_induction_on generalizing p q with
  | h degree inductionHypothesis =>
      intro candidate member
      rw [Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF_eq] at member
      split at member
      · have equal := Purelib.Data.List.Membership.mem_singleton.mp member
        rw [equal]
        exact Purelib.Data.Nat.Order.le_max_left _ _
      · rename_i qNonzeroProof
        dsimp only at member
        split at member
        · have member := Purelib.Data.List.Membership.mem_cons.mp member
          rcases member with head | tail
          · rw [head]
            exact Purelib.Data.Nat.Order.le_max_left _ _
          · rcases Purelib.Data.List.Membership.mem_cons.mp tail with second | impossible
            · rw [second]
              exact Purelib.Data.Nat.Order.le_max_right _ _
            · cases impossible
        · have member := Purelib.Data.List.Membership.mem_cons.mp member
          rcases member with head | tail
          · rw [head]
            exact Purelib.Data.Nat.Order.le_max_left _ _
          · let next := -((DensePolynomial.divMod p q).remainder)
            have qNonzero : q.isZero = false := by
              cases value : q.isZero
              · rfl
              · exact False.elim (qNonzeroProof value)
            have nextDegree : next.degreeCount < degree := by
              dsimp only [next]
              rw [DensePolynomial.degreeCount_neg, ← degreeEquation]
              exact DensePolynomial.divMod_remainder_degreeCount_lt p q qNonzero
            have recursive := inductionHypothesis next.degreeCount nextDegree
              (p := q) (q := next) rfl candidate
              (by simpa only [next] using tail)
            have nextNormalized : next.normalize = next := by
              dsimp only [next]
              exact DensePolynomial.normalize_neg _
            have nextSlots : next.coeffs.length ≤ q.coeffs.length := by
              have degreeDrop : next.degreeCount < q.degreeCount := by
                simpa only [next, DensePolynomial.degreeCount_neg] using
                  DensePolynomial.divMod_remainder_degreeCount_lt p q qNonzero
              have degreeToSlots : q.degreeCount ≤ q.coeffs.length := by
                unfold DensePolynomial.degreeCount
                exact Purelib.Data.List.DropWhile.length_le
                  (fun coefficient : Fraction.Basic.ReducedFraction =>
                    decide (coefficient = 0)) q.coeffs
              have nextLength : next.coeffs.length = next.degreeCount := by
                unfold DensePolynomial.degreeCount
                rw [nextNormalized]
              rw [nextLength]
              exact (Nat.le_of_lt degreeDrop).trans degreeToSlots
            exact recursive.trans
              (Purelib.Data.Nat.Order.max_le (Purelib.Data.Nat.Order.le_max_right _ _) (nextSlots.trans
                (Purelib.Data.Nat.Order.le_max_right _ _)))
end Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource
end

namespace Purelib.RootIsolation.Sturm.Normalized

open Purelib.Algebra.Polynomial.DensePolynomial

end Purelib.RootIsolation.Sturm.Normalized

end

section
@[expose] public section

/-!
# Normalized finite Sturm calculations

This module runs the finite Sturm recursion on canonical reduced coefficient
records.  The finite chain and index calculations use the original Sturm programs
on the same canonical rational carrier.  The resource readbacks retain their
established theorem names without executing identity coefficient maps.  The accompanying recurrence bounds every
coefficient in every chain
member from the two displayed source polynomials.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource
open Purelib.Algebra.Polynomial.DensePolynomial

/-- The magnitude-growth step allowance for one division-and-negation round.

A degree limit contributes four steps per possible division coefficient and one final negation step. -/
def chainRoundSteps (degreeLimit : Nat) : Nat :=
  4 * (degreeLimit + 1) + 1
end Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource

end

section
@[expose] public section

/-!
# Normalized finite Sturm calculations

This module runs the finite Sturm recursion on canonical reduced coefficient
records.  The finite chain and index calculations use the original Sturm programs
on the same canonical rational carrier.  The resource readbacks retain their
established theorem names without executing identity coefficient maps.  The accompanying recurrence bounds every
coefficient in every chain
member from the two displayed source polynomials.
-/

namespace Purelib.RootIsolation.Sturm.Normalized
open Purelib.Algebra.Polynomial.DensePolynomial

end Purelib.RootIsolation.Sturm.Normalized

section
open Purelib.Algebra.Polynomial.DensePolynomial

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource

open _root_.Purelib.RootIsolation.Sturm.Normalized
/-- Bound every signed-chain coefficient by finite magnitude growth from the supplied common bound.

Both input degree counts fit the retained degree limit; the number of rounds is controlled by the second polynomial's
degree count. -/
private theorem
  signedRemainderChainWF_within
    {p q : NormalizedPolynomial} {bound degreeLimit : Nat}
    (zeroBound : Fraction.Resource.Model.rationalModel.magnitude 0 ≤ bound)
    (pWithin : Dense.Resource.PolynomialWithin Fraction.Resource.Model.rationalModel p bound)
    (qWithin : Dense.Resource.PolynomialWithin Fraction.Resource.Model.rationalModel q bound)
    (pDegree : p.degreeCount ≤ degreeLimit)
    (qDegree : q.degreeCount ≤ degreeLimit) :
    ∀ {candidate : NormalizedPolynomial},
      candidate ∈ Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF p q →
      Dense.Resource.PolynomialWithin Fraction.Resource.Model.rationalModel candidate
        (Algebra.Field.Resource.Magnitude.grow Fraction.Resource.Model.rationalModel bound
          (chainRoundSteps degreeLimit * (q.degreeCount + 1))) := by
  generalize degreeEquation : q.degreeCount = degree
  induction degree using Nat.strong_induction_on generalizing p q bound with
  | h degree inductionHypothesis =>
      intro candidate member
      rw [Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF_eq] at member
      split at member
      · have member := Purelib.Data.List.Membership.mem_singleton.mp member
        rw [member]
        exact Dense.Resource.polynomialWithin_mono Fraction.Resource.Model.rationalModel pWithin
          (Algebra.Field.Resource.Magnitude.bound_le_grow Fraction.Resource.Model.rationalModel bound _)
      · rename_i qNonzeroProof
        dsimp only at member
        split at member
        · have member := Purelib.Data.List.Membership.mem_cons.mp member
          rcases member with head | tail
          · rw [head]
            exact Dense.Resource.polynomialWithin_mono Fraction.Resource.Model.rationalModel pWithin
              (Algebra.Field.Resource.Magnitude.bound_le_grow Fraction.Resource.Model.rationalModel bound _)
          · rcases Purelib.Data.List.Membership.mem_cons.mp tail with second | impossible
            · rw [second]
              exact Dense.Resource.polynomialWithin_mono Fraction.Resource.Model.rationalModel qWithin
                (Algebra.Field.Resource.Magnitude.bound_le_grow Fraction.Resource.Model.rationalModel bound _)
            · cases impossible
        · have member := Purelib.Data.List.Membership.mem_cons.mp member
          rcases member with head | tail
          · rw [head]
            exact Dense.Resource.polynomialWithin_mono Fraction.Resource.Model.rationalModel pWithin
              (Algebra.Field.Resource.Magnitude.bound_le_grow Fraction.Resource.Model.rationalModel bound _)
          · have qNonzero : q.isZero = false := by
              cases value : q.isZero
              · rfl
              · exact False.elim (qNonzeroProof value)
            have division := Dense.Resource.divMod_within Fraction.Resource.Model.rationalModel zeroBound pWithin
              qWithin
            let divisionBound := Algebra.Field.Resource.Magnitude.grow Fraction.Resource.Model.rationalModel bound (4 *
              (degreeLimit + 1))
            let roundBound := Algebra.Field.Resource.Magnitude.grow Fraction.Resource.Model.rationalModel bound
              (chainRoundSteps degreeLimit)
            have divisionSteps : 4 * (p.degreeCount + 1) ≤
                4 * (degreeLimit + 1) :=
              Nat.mul_le_mul_left 4 (Nat.add_le_add_right pDegree 1)
            have remainderWithin : Dense.Resource.PolynomialWithin Fraction.Resource.Model.rationalModel
                (DensePolynomial.divMod p q).remainder
                divisionBound :=
              Dense.Resource.polynomialWithin_mono Fraction.Resource.Model.rationalModel division.2
                (Algebra.Field.Resource.Magnitude.grow_mono_steps Fraction.Resource.Model.rationalModel bound
                  divisionSteps)
            have negated := Dense.Resource.neg_within Fraction.Resource.Model.rationalModel remainderWithin
            rw [Algebra.Field.Resource.Magnitude.grow_add] at negated
            have nextWithin : Dense.Resource.PolynomialWithin Fraction.Resource.Model.rationalModel
                (-((DensePolynomial.divMod p q).remainder)) roundBound := by
              simpa only [divisionBound, roundBound, chainRoundSteps] using
                negated
            have qNext := Dense.Resource.polynomialWithin_mono Fraction.Resource.Model.rationalModel qWithin
              (Algebra.Field.Resource.Magnitude.bound_le_grow Fraction.Resource.Model.rationalModel bound
                (chainRoundSteps degreeLimit))
            have smallerActual :
                (-((DensePolynomial.divMod p q).remainder)).degreeCount < q.degreeCount := by
              rw [DensePolynomial.degreeCount_neg]
              exact DensePolynomial.divMod_remainder_degreeCount_lt p q qNonzero
            have smaller :
                (-((DensePolynomial.divMod p q).remainder)).degreeCount < degree := by
              rwa [degreeEquation] at smallerActual
            have nextDegree :
                (-((DensePolynomial.divMod p q).remainder)).degreeCount ≤ degreeLimit :=
              (Nat.le_of_lt smallerActual).trans qDegree
            have recursive := inductionHypothesis _ smaller
              (p := q) (q := -((DensePolynomial.divMod p q).remainder))
              (bound := roundBound)
              (zeroBound.trans (Algebra.Field.Resource.Magnitude.bound_le_grow Fraction.Resource.Model.rationalModel
                bound _))
              qNext nextWithin qDegree nextDegree rfl tail
            rw [Algebra.Field.Resource.Magnitude.grow_add] at recursive
            apply Dense.Resource.polynomialWithin_mono Fraction.Resource.Model.rationalModel recursive
            apply Algebra.Field.Resource.Magnitude.grow_mono_steps Fraction.Resource.Model.rationalModel bound
            have degreeDrop :
                (-((DensePolynomial.divMod p q).remainder)).degreeCount + 1 ≤
                  q.degreeCount := smallerActual
            calc
              chainRoundSteps degreeLimit +
                    chainRoundSteps degreeLimit *
                      ((-((DensePolynomial.divMod p q).remainder)).degreeCount + 1) =
                  chainRoundSteps degreeLimit *
                    ((-((DensePolynomial.divMod p q).remainder)).degreeCount + 2) := by
                symm
                calc
                  chainRoundSteps degreeLimit *
                        ((-((DensePolynomial.divMod p q).remainder)).degreeCount + 2) =
                      chainRoundSteps degreeLimit *
                        (1 + ((-((DensePolynomial.divMod p q).remainder)).degreeCount + 1)) := by
                    congr 1
                    let count := (-((DensePolynomial.divMod p q).remainder)).degreeCount
                    change count + 2 = 1 + (count + 1)
                    calc
                      count + 2 = (count + 1) + 1 :=
                        (Nat.add_assoc count 1 1).symm
                      _ = (1 + count) + 1 := by
                        rw [Nat.add_comm count 1]
                      _ = 1 + (count + 1) := Nat.add_assoc 1 count 1
                  _ = chainRoundSteps degreeLimit * 1 +
                        chainRoundSteps degreeLimit *
                          ((-((DensePolynomial.divMod p q).remainder)).degreeCount + 1) :=
                    Nat.mul_add _ _ _
                  _ = chainRoundSteps degreeLimit +
                        chainRoundSteps degreeLimit *
                          ((-((DensePolynomial.divMod p q).remainder)).degreeCount + 1) := by
                    rw [Nat.mul_one]
              _ ≤ chainRoundSteps degreeLimit * (q.degreeCount + 1) :=
                Nat.mul_le_mul_left _ (Nat.add_le_add_right degreeDrop 1)
              _ = chainRoundSteps degreeLimit * (degree + 1) := by
                rw [degreeEquation]
end Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource
end

namespace Purelib.RootIsolation.Sturm.Normalized

open Purelib.Algebra.Polynomial.DensePolynomial

end Purelib.RootIsolation.Sturm.Normalized

end

section
@[expose] public section

/-!
# Normalized finite Sturm calculations

This module runs the finite Sturm recursion on canonical reduced coefficient
records.  The finite chain and index calculations use the original Sturm programs
on the same canonical rational carrier.  The resource readbacks retain their
established theorem names without executing identity coefficient maps.  The accompanying recurrence bounds every
coefficient in every chain
member from the two displayed source polynomials.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource
open Purelib.Algebra.Polynomial.DensePolynomial

/-- The signed chain beginning with q then p has length at most p's degree count plus one. -/
theorem normalizedChain_length_le (p q :
  Dense.Rational.Basic.CoordinatePolynomial) :
    (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain (id q)
        (id p)).length ≤ p.degreeCount + 1 := by
  exact Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF_length_le q p

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource

end

section
@[expose] public section

/-!
# Normalized finite Sturm calculations

This module runs the finite Sturm recursion on canonical reduced coefficient
records.  The finite chain and index calculations use the original Sturm programs
on the same canonical rational carrier.  The resource readbacks retain their
established theorem names without executing identity coefficient maps.  The accompanying recurrence bounds every
coefficient in every chain
member from the two displayed source polynomials.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource
open Purelib.Algebra.Polynomial.DensePolynomial

/-- Every signed-chain member fits the larger stored input coefficient count. -/
theorem signedRemainderChain_slots_le (p q candidate :
  NormalizedPolynomial)
    (member : candidate ∈ Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain p q) :
    candidate.coeffs.length ≤ max p.coeffs.length q.coeffs.length :=
  signedRemainderChainWF_slots_le p q candidate member
end Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource

end

section
@[expose] public section

/-!
# Normalized finite Sturm calculations

This module runs the finite Sturm recursion on canonical reduced coefficient
records.  The finite chain and index calculations use the original Sturm programs
on the same canonical rational carrier.  The resource readbacks retain their
established theorem names without executing identity coefficient maps.  The accompanying recurrence bounds every
coefficient in every chain
member from the two displayed source polynomials.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource
open Purelib.Algebra.Polynomial.DensePolynomial

/-- The larger coefficient magnitude of the two original signed-chain inputs. -/
def sourceMagnitude (p q :
  NormalizedPolynomial) : Nat :=
  max (Dense.Rational.Resource.Magnitude.coefficientMagnitude p) (Dense.Rational.Resource.Magnitude.coefficientMagnitude
    q)
end Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource

end

section
@[expose] public section

/-!
# Normalized finite Sturm calculations

This module runs the finite Sturm recursion on canonical reduced coefficient
records.  The finite chain and index calculations use the original Sturm programs
on the same canonical rational carrier.  The resource readbacks retain their
established theorem names without executing identity coefficient maps.  The accompanying recurrence bounds every
coefficient in every chain
member from the two displayed source polynomials.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource
open Purelib.Algebra.Polynomial.DensePolynomial

/-- A coefficient-magnitude envelope computed from both source polynomials.

Finite growth uses their maximum degree count for each round and the second input's degree count for the number of
rounds. -/
def chainMagnitudeEnvelope (p q :
  NormalizedPolynomial) : Nat :=
  Algebra.Field.Resource.Magnitude.grow Fraction.Resource.Model.rationalModel
    (sourceMagnitude p q)
    (chainRoundSteps (max p.degreeCount q.degreeCount) *
      (q.degreeCount + 1))
end Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource

end

section
@[expose] public section

/-!
# Normalized finite Sturm calculations

This module runs the finite Sturm recursion on canonical reduced coefficient
records.  The finite chain and index calculations use the original Sturm programs
on the same canonical rational carrier.  The resource readbacks retain their
established theorem names without executing identity coefficient maps.  The accompanying recurrence bounds every
coefficient in every chain
member from the two displayed source polynomials.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource
open Purelib.Algebra.Polynomial.DensePolynomial

/-- Coefficient and storage bounds for one member of the original signed chain.

The bounds use the exact two source polynomials and retain separate magnitude and coefficient-slot claims. -/
structure ChainMemberResource (p q candidate :
  NormalizedPolynomial) : Prop where
  /-- Each candidate coefficient lies within the source-derived magnitude envelope. -/ coefficients :
    Dense.Resource.PolynomialWithin Fraction.Resource.Model.rationalModel candidate
    (chainMagnitudeEnvelope p q)
  /-- The stored candidate coefficient count fits the larger source count. -/ slots : candidate.coeffs.length ≤ max
    p.coeffs.length q.coeffs.length
end Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource

end

section
@[expose] public section

/-!
# Normalized finite Sturm calculations

This module runs the finite Sturm recursion on canonical reduced coefficient
records.  The finite chain and index calculations use the original Sturm programs
on the same canonical rational carrier.  The resource readbacks retain their
established theorem names without executing identity coefficient maps.  The accompanying recurrence bounds every
coefficient in every chain
member from the two displayed source polynomials.
-/

namespace Purelib.RootIsolation.Sturm.Normalized
open Purelib.Algebra.Polynomial.DensePolynomial

end Purelib.RootIsolation.Sturm.Normalized

end

section
@[expose] public section

/-!
# Normalized finite Sturm calculations

This module runs the finite Sturm recursion on canonical reduced coefficient
records.  The finite chain and index calculations use the original Sturm programs
on the same canonical rational carrier.  The resource readbacks retain their
established theorem names without executing identity coefficient maps.  The accompanying recurrence bounds every
coefficient in every chain
member from the two displayed source polynomials.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource
open Purelib.Algebra.Polynomial.DensePolynomial

/-- Every reduced numerator and denominator in the normalized Sturm chain is
bounded by an explicit recurrence in the two displayed source polynomials and
their finite degree counts. -/
theorem signedRemainderChain_coefficient_le
    (p q candidate : NormalizedPolynomial)
    (member : candidate ∈ Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain p q) :
    Dense.Resource.PolynomialWithin Fraction.Resource.Model.rationalModel candidate
      (chainMagnitudeEnvelope p q) := by
  let bound := sourceMagnitude p q
  have zeroBound : Fraction.Resource.Model.rationalModel.magnitude 0 ≤ bound :=
    (Dense.Rational.Resource.Magnitude.zero_le_coefficientMagnitude p).trans
      ((Purelib.Data.Nat.Order.le_max_left _ _))
  have pWithin : Dense.Resource.PolynomialWithin Fraction.Resource.Model.rationalModel p bound :=
    Dense.Resource.polynomialWithin_mono Fraction.Resource.Model.rationalModel
      (Dense.Rational.Resource.Magnitude.polynomial_within_coefficientMagnitude p) (Purelib.Data.Nat.Order.le_max_left _
        _)
  have qWithin : Dense.Resource.PolynomialWithin Fraction.Resource.Model.rationalModel q bound :=
    Dense.Resource.polynomialWithin_mono Fraction.Resource.Model.rationalModel
      (Dense.Rational.Resource.Magnitude.polynomial_within_coefficientMagnitude q) (Purelib.Data.Nat.Order.le_max_right
        _ _)
  exact signedRemainderChainWF_within zeroBound pWithin
    qWithin
    (Purelib.Data.Nat.Order.le_max_left _ _) (Purelib.Data.Nat.Order.le_max_right _ _) member
end Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource

end

section
@[expose] public section

/-!
# Normalized finite Sturm calculations

This module runs the finite Sturm recursion on canonical reduced coefficient
records.  The finite chain and index calculations use the original Sturm programs
on the same canonical rational carrier.  The resource readbacks retain their
established theorem names without executing identity coefficient maps.  The accompanying recurrence bounds every
coefficient in every chain
member from the two displayed source polynomials.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource
open Purelib.Algebra.Polynomial.DensePolynomial

/-- Bound endpoint Horner intermediates using the chain envelope and the displayed argument magnitude. -/
def workingEndpointMagnitudeEnvelope (p q :
  NormalizedPolynomial)
    (point : Fraction.Basic.ReducedFraction) : Nat :=
  Algebra.Field.Resource.Magnitude.grow Fraction.Resource.Model.rationalModel
    (max (chainMagnitudeEnvelope p q)
      (Fraction.Resource.Model.rationalModel.magnitude point))
    (2 * max p.coeffs.length q.coeffs.length)
/-- Combine coefficient-magnitude and slot bounds for a displayed chain member. -/
theorem chainMember_resource (p q candidate :
  NormalizedPolynomial)
    (member : candidate ∈ Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain p q) :
    ChainMemberResource p q candidate :=
  ⟨signedRemainderChain_coefficient_le p q candidate member,
    signedRemainderChain_slots_le p q candidate member⟩

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource

end
