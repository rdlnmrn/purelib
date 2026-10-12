module
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
public import Purelib.Approximation.Gaussian.Division.Prepared.Bounded
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Division.Prepared

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Denominator preparation survives fractional composition

A preparation provider for all invertible integral matrices can be carried
through a prepared fractional action. An outer denominator is represented as
the quotient of the combined and inner denominators. Both are already apart;
one retained base state supplies a uniform upper bound for the divisor.
-/

namespace Purelib.Approximation.Gaussian.Division.Prepared.Ratio

/-- Form the coherent quotient of two prepared channels, restricting the divisor to its retained initial future.

The quotient consumes the original numerator preparation and the bounded denominator preparation with its exact
apartness certificate. -/
def quotient {numerator denominator :
  Coherent.CoherentNamed}
    (top : Prepared.DenominatorPreparation numerator) (bottom : Prepared.DenominatorPreparation denominator) :
    Coherent.CoherentNamed :=
  CoherentNamed.div top.prepared
    (Bounded.basedPreparation bottom).prepared (Bounded.basedPreparation bottom).apart

/-- Apartness of the quotient needs only the numerator lower bound and the retained denominator upper bound; no new
search is performed. -/
def quotientApart {numerator denominator :
  Coherent.CoherentNamed}
    (top : Prepared.DenominatorPreparation numerator) (bottom : Prepared.DenominatorPreparation denominator) :
    Possible.PossibleApart (quotient top bottom).name.process where
  lowerSq := top.apart.certificate.lowerSq / Bounded.divisorUpper bottom
  positive := Fraction.Order.Field.div_pos_direct top.apart.certificate.positive
    (Bounded.divisorUpper_positive bottom)
  lower := by
    intro state value possible
    rcases possible with ⟨x, y, hx, hy, rfl⟩
    have xLower := top.apart.certificate.lower _
      (top.prepared.name.process.possible_inside hx)
    have yPositive := (Bounded.basedPreparation bottom).apart.certificate.positive.trans_le
      ((Bounded.basedPreparation bottom).apart.certificate.lower _
        ((Bounded.basedPreparation bottom).prepared.name.process.possible_inside hy))
    have yNonzero : y ≠ 0 := by
      intro zero
      rw [zero, Data.Gaussian.Norm.Basic.normSq_zero] at yPositive
      exact lt_irrefl _ yPositive
    rw [Data.Gaussian.Field.normSq_div _ _ yNonzero]
    apply (Fraction.Order.Field.le_div_iff_pos yPositive).2
    calc
      (top.apart.certificate.lowerSq / Bounded.divisorUpper bottom) *
          Data.Gaussian.Norm.Basic.normSq y ≤
        (top.apart.certificate.lowerSq / Bounded.divisorUpper bottom) * Bounded.divisorUpper bottom :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Bounded.divisor_bounded bottom _ hy)
            (Fraction.Order.Field.div_nonneg_direct top.apart.certificate.positive.le
              (Bounded.divisorUpper_positive bottom).le)
      _ = top.apart.certificate.lowerSq :=
        Fraction.Field.div_mul_cancel_of_ne _ _
          (Bounded.divisorUpper_positive bottom).ne'
      _ ≤ Data.Gaussian.Norm.Basic.normSq x := xLower
end Purelib.Approximation.Gaussian.Division.Prepared.Ratio

end
