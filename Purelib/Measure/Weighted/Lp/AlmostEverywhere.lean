module
import Purelib.Data.List.Membership
public import Purelib.Measure.Weighted.AlmostEverywhere
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
public section

/-!
# Powered Lp quantities modulo finite almost-everywhere equality

Natural-powered finite magnitudes and distances depend only on displayed
nonzero-weight rows.  At every explicitly positive natural exponent they
vanish exactly when the relevant observables are equal in the finite
almost-everywhere sense.  The proof is a direct induction over the weighted
atom list and uses no quotient function space.
-/

namespace Purelib.Measure

open Purelib Purelib.Data.Rat Purelib.Data.List

/-- A zero weighted integral of a positive natural power of distance implies agreement away from zero-weight
occurrences.

The power is the supplied exponent plus one. Nonnegativity separates every retained summand, and a nonzero weight forces
that occurrence's exact rational distance to vanish. -/
theorem equalOffZeroWeight_of_poweredDistance_eq_zero
    {α : Type} (left right : α → Fraction.Rational) (exponent : Nat) :
    ∀ atoms : List (Weighted α),
      Distribution.expectationWeight atoms (fun item =>
        Distance.rationalSeparation (left item) (right item) ^ (exponent + 1)) = 0 →
      EqualOffZeroWeightOn atoms left right
  | [], zero => by
      intro atom member
      cases member
  | head :: remaining, zero => by
      let poweredDistance : α → Fraction.Rational := fun item =>
        Distance.rationalSeparation (left item) (right item) ^ (exponent + 1)
      have totalEquation :
          head.weight * poweredDistance head.item +
              Distribution.expectationWeight remaining poweredDistance = 0 := by
        simpa only [Distribution.expectationWeight] using zero
      have headNonnegative :
          0 ≤ head.weight * poweredDistance head.item :=
        Fraction.Order.Arithmetic.mul_nonneg_direct head.nonnegative
          (Fraction.Order.Arithmetic.pow_nonneg_direct
            (Distance.rationalSeparation_nonneg _ _) (exponent + 1))
      have tailNonnegative :
          0 ≤ Distribution.expectationWeight remaining poweredDistance :=
        Distribution.expectationWeight_nonneg remaining poweredDistance
          (fun atom member =>
            Fraction.Order.Arithmetic.pow_nonneg_direct
              (Distance.rationalSeparation_nonneg _ _) (exponent + 1))
      have headZero : head.weight * poweredDistance head.item = 0 :=
        Fraction.Order.Basic.Compatibility.le_antisymm _ _
          (calc
            head.weight * poweredDistance head.item ≤
                head.weight * poweredDistance head.item +
                  Distribution.expectationWeight remaining poweredDistance :=
              le_add_of_nonneg_right tailNonnegative
            _ = 0 := totalEquation)
          headNonnegative
      have tailZero :
          Distribution.expectationWeight remaining poweredDistance = 0 :=
        Fraction.Order.Basic.Compatibility.le_antisymm _ _
          (calc
            Distribution.expectationWeight remaining poweredDistance ≤
                head.weight * poweredDistance head.item +
                  Distribution.expectationWeight remaining poweredDistance :=
              le_add_of_nonneg_left headNonnegative
            _ = 0 := totalEquation)
          tailNonnegative
      intro atom member
      rcases Membership.mem_cons.mp member with same | tail
      · subst atom
        by_cases weightZero : head.weight = 0
        · exact Or.inl weightZero
        · apply Or.inr
          apply (Distance.rationalSeparation_eq_zero_iff
            (left head.item) (right head.item)).mp
          by_cases separationZero :
              Distance.rationalSeparation (left head.item) (right head.item) = 0
          · exact separationZero
          · have weightPositive : 0 < head.weight :=
              lt_of_le_of_ne head.nonnegative (Ne.symm weightZero)
            have separationPositive :
                0 < Distance.rationalSeparation (left head.item) (right head.item) :=
              lt_of_le_of_ne (Distance.rationalSeparation_nonneg _ _)
                (Ne.symm separationZero)
            have poweredPositive :
                0 < poweredDistance head.item :=
              Fraction.Order.Arithmetic.pow_pos_direct
                separationPositive (exponent + 1)
            have productPositive := Fraction.Order.Arithmetic.mul_pos_direct
              weightPositive poweredPositive
            exact (productPositive.ne' headZero).elim
      · exact equalOffZeroWeight_of_poweredDistance_eq_zero
          left right exponent remaining tailZero atom tail

end Purelib.Measure

end
