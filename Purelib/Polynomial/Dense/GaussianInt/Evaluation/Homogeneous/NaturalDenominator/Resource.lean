module
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order

import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Norm.Bounds
import Purelib.Data.GaussianInt.Power
public import Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
import Mathlib.Algebra.Group.Nat.Defs

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- A direct multiplication count for the displayed implementation: each
clause computes one power and then performs its two outer products. -/
def
  homogeneousMultiplicationBudget
  : List GaussianInt → Nat
  | [] => 0
  | _ :: remaining =>
      remaining.length + 2 +
        homogeneousMultiplicationBudget
        remaining
end Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- The multiplication budget adds the current power length and two outer products to the remaining coefficient budget.
-/
@[simp] theorem
  homogeneousMultiplicationBudget_eq
    (coefficient : GaussianInt) (remaining : List GaussianInt) :
    Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousMultiplicationBudget (coefficient ::
      remaining) =
      remaining.length + 2 +
        Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousMultiplicationBudget remaining
        := rfl
end Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- Structural norm envelope matching the homogeneous evaluation recursion. -/
def
  homogeneousNormEnvelope
  (numerator denominator : GaussianInt) :
    List GaussianInt → Nat
  | [] => 0
  | coefficient :: remaining =>
      2 *
        (normNat coefficient * normNat numerator ^ remaining.length +
          normNat denominator *

              homogeneousNormEnvelope
              numerator denominator remaining)
end Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- Gaussian-integer homogeneous evaluation is bounded by its structural natural norm envelope. -/
theorem
  homogeneousEval_norm_le_envelope
    (numerator denominator : GaussianInt) (coefficients : List GaussianInt) :
    normNat
        (Dense.GaussianInt.Evaluation.Homogeneous.homogeneousEval numerator denominator
          coefficients) ≤
      Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousNormEnvelope numerator denominator
        coefficients := by
  induction coefficients with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      rw [Dense.GaussianInt.Evaluation.Homogeneous.homogeneousEval,
        Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousNormEnvelope]
      refine (GaussianInt.Norm.Bounds.normNat_add_le_two _ _).trans ?_
      rw [normNat_mul, normNat_mul, GaussianInt.Power.normNat_pow]
      exact Nat.mul_le_mul_left 2
        (Nat.add_le_add_left
          (Nat.mul_le_mul_left (normNat denominator) inductionHypothesis) _)
end Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- The number of coefficient clauses in the finite homogeneous evaluation. -/
def homogeneousStepBudget
  (coefficients : List GaussianInt) : Nat :=
  coefficients.length
end Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- One list entry for the base case and each recursive suffix value. -/
def homogeneousTrace
  (numerator denominator : GaussianInt) :
    List GaussianInt → List GaussianInt
  | [] => [0]
  | coefficients@(_ :: remaining) =>
      Dense.GaussianInt.Evaluation.Homogeneous.homogeneousEval numerator denominator
          coefficients ::
        Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousTrace
          numerator denominator remaining
end Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- The homogeneous evaluation trace contains one entry per coefficient and its final zero base value. -/
@[simp] theorem
  homogeneousTrace_length
    (numerator denominator : GaussianInt) (coefficients : List GaussianInt) :
    (Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousTrace numerator denominator
      coefficients).length =
      coefficients.length + 1 := by
  induction coefficients with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self,
        Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousTrace, List.length_cons,
        inductionHypothesis]
      rfl
end Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- Maximum of the structural envelopes for all recursive suffixes. -/
def
  homogeneousWorkingEnvelope
  (numerator denominator : GaussianInt) :
    List GaussianInt → Nat
  | [] => 0
  | coefficients@(_ :: remaining) =>
      max (Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousNormEnvelope numerator
        denominator coefficients)

          (homogeneousWorkingEnvelope
          numerator denominator remaining)
end Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- Every retained suffix evaluation in the homogeneous trace fits the maximum structural norm envelope. -/
theorem
  homogeneousTrace_norm_le_workingEnvelope
    (numerator denominator : GaussianInt) (coefficients : List GaussianInt)
    {value : GaussianInt}
    (member : value ∈ Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousTrace numerator
      denominator coefficients) :
    normNat value ≤
      Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousWorkingEnvelope numerator
        denominator coefficients := by
  induction coefficients with
  | nil =>
      simp only [-eq_self, -iff_self,
        Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousTrace] at member
      have member := Purelib.Data.List.Membership.mem_singleton.mp member
      rw [member]
      rfl
  | cons coefficient remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self,
        Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousTrace] at member
      have member := Purelib.Data.List.Membership.mem_cons.mp member
      rw [Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousWorkingEnvelope]
      rcases member with head | tail
      · rw [head]
        exact (Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousEval_norm_le_envelope
          numerator denominator _).trans
          (Purelib.Data.Nat.Order.le_max_left _ _)
      · exact (inductionHypothesis tail).trans (Purelib.Data.Nat.Order.le_max_right _ _)
end Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource

end
