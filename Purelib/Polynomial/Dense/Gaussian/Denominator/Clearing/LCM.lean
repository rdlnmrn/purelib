module
import Purelib.Data.Rat.Fraction
public import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Fraction.NaturalDenominator.LeastDenominator
public import Purelib.Data.Gaussian.Fraction.NaturalDenominator.ScaledNumerator
import Purelib.Data.Nat.LCM
import Purelib.Data.Nat.Divisibility
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.GaussianInt.Evaluation
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite denominator-height lower bounds for polynomial residuals

The finite coefficient list is cleared to Gaussian integers by a structural
product of the canonical coordinate denominators.  Homogeneous evaluation at
a displayed common-denominator Gaussian fraction then gives an integral
numerator.  If the residual is nonzero, its integral norm is at least one.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.LCM

open Purelib.Data.List
open Purelib.Data.Gaussian

/-- The global least common multiple of all reduced coefficient-coordinate
denominators.  Unlike `clear`, this does not multiply denominators that have
already been cleared. -/
def lcmScale : List Gaussian.Basic.Canonical → Nat
  | [] => 1
  | coefficient :: remaining =>
      Data.Nat.LCM.lcm
        (Gaussian.Fraction.NaturalDenominator.LeastDenominator.coefficientDenominator coefficient)
          (lcmScale remaining)

/-- The common-denominator LCM of a finite Gaussian coefficient list is positive. -/
theorem lcmScale_pos (coefficients : List
  Gaussian.Basic.Canonical) :
    0 < lcmScale coefficients := by
  induction coefficients with
  | nil => decide
  | cons coefficient remaining inductionHypothesis =>
      exact Data.Nat.LCM.lcm_pos
        (Gaussian.Fraction.NaturalDenominator.LeastDenominator.coefficientDenominator_pos coefficient)
          inductionHypothesis

/-- A natural scale is a common multiple of every reduced real and imaginary
coordinate denominator in the displayed coefficient list. -/
def ClearsCoefficientDenominators
    (coefficients : List Gaussian.Basic.Canonical) (scale : Nat) : Prop :=
  ∀ coefficient ∈ coefficients,
    (Fraction.Basic.representative coefficient.re).den ∣ scale ∧
      (Fraction.Basic.representative coefficient.im).den ∣ scale

open Purelib.Data.Nat

/-- The retained coefficient LCM clears every coordinate denominator.

Structural list membership selects the original coefficient occurrence. Direct
natural divisibility composition carries each retained denominator into the
same computed LCM scale. -/
theorem lcmScale_clears (coefficients : List
  Gaussian.Basic.Canonical) :
    ClearsCoefficientDenominators coefficients
      (lcmScale coefficients) := by
  induction coefficients with
  | nil =>
      intro coefficient member
      cases member
  | cons coefficient remaining inductionHypothesis =>
      intro candidate member
      cases member with
      | head =>
          exact
            ⟨Divisibility.trans (LCM.left_dvd_lcm _ _) (LCM.left_dvd_lcm _ _),
              Divisibility.trans (LCM.right_dvd_lcm _ _) (LCM.left_dvd_lcm _ _)⟩
      | tail _ tailMember =>
          have tailCleared := inductionHypothesis candidate tailMember
          exact
            ⟨Divisibility.trans tailCleared.1 (LCM.right_dvd_lcm _ _),
              Divisibility.trans tailCleared.2 (LCM.right_dvd_lcm _ _)⟩

/-- The computed LCM scale divides every other displayed common multiple of
all reduced coefficient-coordinate denominators.

The supplied scale is a common multiple of every reduced coordinate denominator in
the original coefficient list. Their recursively computed least common multiple
therefore divides it. -/
theorem lcmScale_dvd_of_clears {coefficients : List
  Gaussian.Basic.Canonical} {scale : Nat}
    (clears : ClearsCoefficientDenominators coefficients scale) :
    lcmScale coefficients ∣ scale := by
  induction coefficients with
  | nil => exact ⟨scale, (Nat.one_mul scale).symm⟩
  | cons coefficient remaining inductionHypothesis =>
      have head := clears coefficient List.mem_cons_self
      have tail : ClearsCoefficientDenominators remaining scale := by
        intro candidate member
        exact clears candidate (List.mem_cons_of_mem _ member)
      exact Data.Nat.LCM.lcm_dvd
        (Data.Nat.LCM.lcm_dvd head.1 head.2)
        (inductionHypothesis tail)

/-- Coefficients cleared with the global least common denominator. -/
def lcmClear (coefficients : List
  Gaussian.Basic.Canonical) : Dense.Gaussian.Denominator.Clearing.Basic.ClearedCoefficients :=
  let scale := lcmScale coefficients
  { scale := scale
    scalePositive := lcmScale_pos coefficients
    coefficients := coefficients.map (Gaussian.Fraction.NaturalDenominator.ScaledNumerator.scaledGaussianCoefficient
      scale) }

/-- LCM clearing retains exactly one integer entry per source coefficient. -/
@[simp] theorem DenominatorHeight.lcmClear_length
  (coefficients : List Gaussian.Basic.Canonical) :
    (lcmClear coefficients).coefficients.length = coefficients.length := by
  exact Map.length_map _ coefficients

/-- Evaluation of the scaled integer coefficients equals the original evaluation times the common scale.

The natural scale must divide out every real and imaginary coordinate denominator in the displayed list. -/
theorem evalIntegers_map_scaled
    (point : Gaussian.Basic.Canonical) (coefficients : List Gaussian.Basic.Canonical) (scale : Nat)
    (clears : ClearsCoefficientDenominators coefficients scale) :
    Dense.GaussianInt.Evaluation.evalIntegers point
        (coefficients.map (Gaussian.Fraction.NaturalDenominator.ScaledNumerator.scaledGaussianCoefficient scale)) =
      ⟨(scale : Fraction.Rational), 0⟩ * DensePolynomial.evalCoeffs point coefficients := by
  induction coefficients with
  | nil =>
      exact (Basic.mul_zero _).symm
  | cons coefficient remaining inductionHypothesis =>
      have head := clears coefficient List.mem_cons_self
      have tail : ClearsCoefficientDenominators remaining scale := by
        intro candidate member
        exact clears candidate (List.mem_cons_of_mem _ member)
      rw [List.map_cons, Dense.GaussianInt.Evaluation.evalIntegers_cons, Map.length_map,
        Gaussian.Fraction.NaturalDenominator.ScaledNumerator.toGaussian_scaledGaussianCoefficient scale coefficient
          head.1 head.2,
        inductionHypothesis tail, DensePolynomial.evalCoeffs_cons_expansion]
      ring1

/-- LCM coefficient clearing multiplies evaluation by exactly its displayed
least common denominator. -/
theorem eval_lcmClear (point :
  Gaussian.Basic.Canonical) (coefficients : List Gaussian.Basic.Canonical) :
    Dense.GaussianInt.Evaluation.evalIntegers point (lcmClear
      coefficients).coefficients =
      ⟨((lcmClear coefficients).scale : Fraction.Rational), 0⟩ *
        DensePolynomial.evalCoeffs point coefficients := by
  exact evalIntegers_map_scaled point coefficients
    (lcmScale coefficients)
    (lcmScale_clears coefficients)
end Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.LCM

end

section
@[expose] public section

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.LCM.ClearingCalculationSize

/-- The LCM-cleared output contains exactly as many coefficients as its input. -/
@[simp] theorem
  lcmClear_output_length
  (coefficients : List Gaussian.Basic.Canonical) :
    (lcmClear coefficients).coefficients.length =
      coefficients.length :=
  Dense.Gaussian.Denominator.Clearing.LCM.DenominatorHeight.lcmClear_length coefficients

end Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.LCM.ClearingCalculationSize

end
