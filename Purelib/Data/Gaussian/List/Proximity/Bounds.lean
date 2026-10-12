module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.List.NormBounds
public import Purelib.Data.Gaussian.List.Proximity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Lattice

open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-!
# Uniform norm bounds for nearby Gaussian coefficient lists

The retained reference maximum and common coefficientwise tolerance determine
the original admitted bound. Paired-list proximity preserves the same ordered
reference and reading tails under that finite uniform quadrance estimate.
-/

namespace Purelib.Data.Gaussian.List.Proximity.Bounds

/-- Compute twice the reference coefficient norm maximum plus eight times the target tolerance.

The reference maximum retains every original coefficient quadrance.
The supplied scalar tolerance is multiplied by eight before adding it
to that same maximum and doubling the result. -/
@[expose] public def admittedCoefficientBound (reference : List Basic.Canonical)
    (target : Fraction.Rational) : Fraction.Rational :=
  2 * (List.NormBounds.coefficientNormMaximum reference + 8 * target)

/-- A positive target tolerance makes the admitted coefficient bound positive.

The reference maximum is strictly positive and the supplied tolerance
is strictly positive. The original positive scalar factors preserve
positivity of their sum and its outer doubled value. -/
public theorem admittedCoefficientBound_pos (reference : List Basic.Canonical)
    {target : Fraction.Rational} (positive : 0 < target) :
    0 < List.Proximity.Bounds.admittedCoefficientBound reference target :=
  Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
      (List.NormBounds.coefficientNormMaximum_pos reference).le
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide) positive))

set_option backward.match.sparseCases false in
/-- Entrywise squared distance at most eight times a nonnegative target bounds every reading norm by the admitted
reference bound.

The two lists retain corresponding positions through the supplied closeness relation. The Gaussian squared-norm addition
bound combines reference norms and displacement bounds, while monotonicity extends the tail bound to the full reference
maximum. -/
public theorem coefficientsNormLe_of_close : ∀
    {reference reading : List Basic.Canonical} {target : Fraction.Rational},
    List.Proximity.CoefficientsClose reference reading (8 * target) →
    0 ≤ target →
    List.NormBounds.CoefficientsNormLe reading (List.Proximity.Bounds.admittedCoefficientBound reference target)
  | [], [], target, _close, _targetNonnegative => trivial
  | [], _ :: _, target, close, _targetNonnegative => by
      exact close.elim
  | _ :: _, [], target, close, _targetNonnegative => by
      exact close.elim
  | reference :: referenceTail, reading :: readingTail, target,
      close, targetNonnegative => by
      rcases close with ⟨headClose, tailClose⟩
      constructor
      · have referenceBound : Norm.Basic.normSq reference ≤
            List.NormBounds.coefficientNormMaximum (reference :: referenceTail) :=
          Fraction.Order.Basic.le_max_left _ _
        have identity : reading = (reading - reference) + reference := by
          apply Basic.ext <;>
            simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im] <;> ring1
        rw [identity]
        calc
          Norm.Basic.normSq ((reading - reference) + reference) ≤
              2 * (Norm.Basic.normSq (reading - reference) + Norm.Basic.normSq reference) :=
            Norm.Bounds.normSq_add_le_two _ _
          _ = 2 * (Norm.Basic.normSq (reference - reading) + Norm.Basic.normSq reference) := by
            have reverse : reading - reference = -(reference - reading) := by
              apply Basic.ext <;>
                simp only [Basic.sub_re, Basic.sub_im, Basic.neg_re, Basic.neg_im] <;> ring1
            rw [reverse, Norm.Basic.normSq_neg]
          _ ≤ 2 * (8 * target +
                List.NormBounds.coefficientNormMaximum (reference :: referenceTail)) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (add_le_add headClose referenceBound) (by decide)
          _ = List.Proximity.Bounds.admittedCoefficientBound (reference :: referenceTail) target := by
            unfold List.Proximity.Bounds.admittedCoefficientBound
            ring1
      · have tailBound := Purelib.Data.Gaussian.List.Proximity.Bounds.coefficientsNormLe_of_close tailClose
          targetNonnegative
        apply tailBound.mono
        unfold List.Proximity.Bounds.admittedCoefficientBound
        apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _
          (by decide)
        change List.NormBounds.coefficientNormMaximum referenceTail + 8 * target ≤
          max (Norm.Basic.normSq reference) (List.NormBounds.coefficientNormMaximum referenceTail) +
            8 * target
        exact add_le_add
          (show List.NormBounds.coefficientNormMaximum referenceTail ≤
              max (Norm.Basic.normSq reference) (List.NormBounds.coefficientNormMaximum referenceTail)
            from Fraction.Order.Basic.le_max_right _ _)
          (Fraction.Order.Basic.le_refl _)

end Purelib.Data.Gaussian.List.Proximity.Bounds
