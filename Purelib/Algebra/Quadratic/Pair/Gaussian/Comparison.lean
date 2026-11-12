module

public import Purelib.Algebra.Quadratic.Pair.Gaussian.Preparation
import Purelib.Approximation.Gaussian.Division.Obstruction.Zero
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Arithmetic.Neg

/-!
# Unique original quadratic coordinates at an admitted generator

An injective exact coefficient map and nonsquare negative parameter make every
nonzero original pair preparable. Operational zero is incompatible with that
preparation, so operational agreement at the same retained generator identifies
both original coordinates.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Gaussian

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Approximation.Gaussian.Division

variable {K : Type} {parameter : K}

/-- Interpreted pair subtraction agrees with the original numerical sum followed by negation. -/
@[noinline, nospecialize] def denote_sub [CommRing K] (coefficient : K → Canonical)
    (zero_eq : coefficient 0 = 0)
    (add_eq : ∀ first second, coefficient (first + second) = coefficient first + coefficient second)
    (generator : CoherentNamed) (left right : Pair K parameter) :
    NamedEquivalent (CoherentNamed.add (denote coefficient generator left)
      (CoherentNamed.neg (denote coefficient generator right))).name
      (denote coefficient generator (left - right)).name := by
  let first := denote coefficient generator left
  let second := denote coefficient generator right
  let negative := denote coefficient generator (-right)
  have sum := denote_add coefficient add_eq generator left (-right)
  rewrite [← _root_.sub_eq_add_neg] at sum
  exact NamedEquivalent.trans
    (Congruence.coherentAdd_respects first first (CoherentNamed.neg second) negative
      (NamedEquivalent.refl _) (denote_neg coefficient zero_eq add_eq generator right)) sum

/-- An operational zero at an admitted generator forces the entire original pair to be zero. -/
theorem zero_injective [ExplicitField K] [DecidableEq K] (coefficient : K → Canonical)
    (zero_eq : coefficient 0 = 0) (injective : Function.Injective coefficient)
    (add_eq : ∀ first second, coefficient (first + second) = coefficient first + coefficient second)
    (mul_eq : ∀ first second, coefficient (first * second) = coefficient first * coefficient second)
    (sub_eq : ∀ first second, coefficient (first - second) = coefficient first - coefficient second)
    (generator : CoherentNamed) (identity : PowerIdentity generator 2 (-coefficient parameter))
    (nonsquare : ∀ candidate : K, candidate * candidate ≠ -parameter)
    (value : Pair K parameter)
    (zero : NamedEquivalent (denote coefficient generator value).name (Coherence.exact 0).name) : value = 0 := by
  by_cases valueZero : value = 0
  · exact valueZero
  · have normNonzero : value.norm ≠ 0 := value.norm_ne_zero nonsquare valueZero
    have mappedNonzero : coefficient value.norm ≠ 0 := by
      intro vanishes
      exact normNonzero (injective (vanishes.trans zero_eq.symm))
    let observation := observe_norm coefficient zero_eq add_eq mul_eq sub_eq generator identity value mappedNonzero
    exact False.elim (Obstruction.Zero.ZeroIdentity.incompatible_prepared zero observation.prepare)

/-- Operational agreement at the same admitted generator identifies the entire original pair of coordinates. -/
theorem denote_injective [ExplicitField K] [DecidableEq K] (coefficient : K → Canonical)
    (zero_eq : coefficient 0 = 0) (injective : Function.Injective coefficient)
    (add_eq : ∀ first second, coefficient (first + second) = coefficient first + coefficient second)
    (mul_eq : ∀ first second, coefficient (first * second) = coefficient first * coefficient second)
    (sub_eq : ∀ first second, coefficient (first - second) = coefficient first - coefficient second)
    (generator : CoherentNamed) (identity : PowerIdentity generator 2 (-coefficient parameter))
    (nonsquare : ∀ candidate : K, candidate * candidate ≠ -parameter)
    (left right : Pair K parameter)
    (equivalent : NamedEquivalent (denote coefficient generator left).name
      (denote coefficient generator right).name) : left = right := by
  let first := denote coefficient generator left
  let second := denote coefficient generator right
  have differenceZero : NamedEquivalent
      (CoherentNamed.add first (CoherentNamed.neg second)).name (Coherence.exact 0).name :=
    NamedEquivalent.trans
      (Congruence.coherentAdd_respects first second (CoherentNamed.neg second) (CoherentNamed.neg second)
        equivalent (NamedEquivalent.refl _)) (Neg.coherentAdd_neg_right second)
  have zero : NamedEquivalent (denote coefficient generator (left - right)).name (Coherence.exact 0).name :=
    NamedEquivalent.trans (NamedEquivalent.symm (denote_sub coefficient zero_eq add_eq generator left right))
      differenceZero
  have difference :=
    zero_injective coefficient zero_eq injective add_eq mul_eq sub_eq generator identity nonsquare (left - right) zero
  have translated := congrArg (fun value : Pair K parameter => value + right) difference
  change (left + -right) + right = 0 + right at translated
  rewrite [add_assoc, neg_add_cancel, add_zero, zero_add] at translated
  exact translated

end Purelib.Algebra.Quadratic.Pair.Gaussian

end
