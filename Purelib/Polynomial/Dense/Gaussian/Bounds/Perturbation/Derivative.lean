module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.List.Proximity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Polynomial.Bounds.Horner
public import Purelib.Polynomial.Dense.Derivative
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Paired automatic-Horner perturbation bounds

Paired automatic-Horner scans retain their original ordered coefficient
lists and initial running values. The same finite rational recurrence
bounds value and derivative differences at their supplied input.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Perturbation.Derivative

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial

open Purelib.Data.Gaussian

/-- One automatic-Horner perturbation step.  `value` bounds the difference
of the two running values and `slope` bounds the difference of the two
running derivatives.

The supplied bounds retain the two running automatic-Horner differences.
The original doubled rational formulas update value and derivative bounds
at the same coefficient and input quadrance. -/
@[expose] public def perturbationBoundsStep (inputNormSq coefficientBound : Fraction.Rational)
    (bounds : Bounds.Horner) : Bounds.Horner where
  value := 2 * (bounds.value * inputNormSq + coefficientBound)
  slope := 2 * (bounds.slope * inputNormSq + bounds.value)

/-- Repeat the same coefficientwise perturbation bound through a finite
automatic-Horner scan.

The recurrence iterates the same original step exactly the supplied finite
count. Its retained initial bounds are passed through each original tail
without replacing the automatic-Horner scan. -/
@[expose] public def perturbationBoundsFrom : Nat → Fraction.Rational → Fraction.Rational →
    Bounds.Horner → Bounds.Horner
  | 0, _, _, bounds => bounds
  | count + 1, coefficientBound, inputNormSq, bounds =>
      Purelib.Polynomial.Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsFrom count coefficientBound
        inputNormSq
        (Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsStep inputNormSq coefficientBound bounds)

/-- Compute simultaneous value and derivative perturbation bounds by a fixed-length automatic-Horner recurrence starting
at zero.

Both original running bounds start at zero and follow the same finite
coefficient-count recurrence. The displayed coefficient and input bounds
are retained at every step. -/
@[expose] public def coefficientPerturbationBounds (count : Nat)
    (coefficientBound inputNormSq : Fraction.Rational) : Bounds.Horner :=
  Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsFrom count coefficientBound inputNormSq ⟨0, 0⟩

/-- The perturbation recurrence preserves nonnegative value and derivative bounds when coefficient and input bounds are
nonnegative.

The initial running bounds, coefficient bound and input quadrance are
nonnegative. Each original recurrence step preserves both value and
derivative inequalities along the supplied finite count. -/
private theorem perturbationBoundsFrom_nonneg : ∀ count
    {coefficientBound inputNormSq : Fraction.Rational}
    (bounds : Bounds.Horner),
    0 ≤ coefficientBound → 0 ≤ inputNormSq →
      0 ≤ bounds.value → 0 ≤ bounds.slope →
      0 ≤ (Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsFrom count coefficientBound
        inputNormSq bounds).value ∧
      0 ≤ (Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsFrom count coefficientBound
        inputNormSq bounds).slope
  | 0, _coefficientBound, _inputNormSq, bounds,
      _coefficientNonnegative, _inputNonnegative,
      valueNonnegative, slopeNonnegative =>
      ⟨valueNonnegative, slopeNonnegative⟩
  | count + 1, coefficientBound, inputNormSq, bounds,
      coefficientNonnegative, inputNonnegative,
      valueNonnegative, slopeNonnegative => by
      apply Purelib.Polynomial.Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsFrom_nonneg count
        (Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsStep inputNormSq coefficientBound bounds)
        coefficientNonnegative inputNonnegative
      · exact Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg
            (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
              valueNonnegative inputNonnegative)
            coefficientNonnegative)
      · exact Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg
            (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
              slopeNonnegative inputNonnegative)
            valueNonnegative)

/-- Both perturbation bounds computed from zero are nonnegative for nonnegative coefficient and input bounds.

The original recurrence begins at two zero bounds and uses nonnegative
coefficient and input bounds throughout its finite scan. Both displayed
outputs are therefore nonnegative. -/
public theorem coefficientPerturbationBounds_nonneg
    (count : Nat) {coefficientBound inputNormSq : Fraction.Rational}
    (coefficientNonnegative : 0 ≤ coefficientBound)
    (inputNonnegative : 0 ≤ inputNormSq) :
    0 ≤ (Dense.Gaussian.Bounds.Perturbation.Derivative.coefficientPerturbationBounds count coefficientBound
      inputNormSq).value ∧
    0 ≤ (Dense.Gaussian.Bounds.Perturbation.Derivative.coefficientPerturbationBounds count coefficientBound
      inputNormSq).slope :=
  Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsFrom_nonneg count ⟨0, 0⟩ coefficientNonnegative
    inputNonnegative le_rfl le_rfl

set_option backward.match.sparseCases false in
/-- Paired automatic-Horner folds preserve the computed value and derivative perturbation bounds.

The coefficient lists satisfy the retained pointwise squared-distance bound, the input quadrance is bounded, and the
initial value and derivative differences satisfy their supplied invariants. -/
private theorem evalDerivativeCoeffs_sub_bounds :
    ∀ (left right : List Gaussian.Basic.Canonical) (input : Gaussian.Basic.Canonical)
      (coefficientBound inputNormSq : Fraction.Rational)
      (leftValue leftDerivative rightValue rightDerivative : Gaussian.Basic.Canonical)
      (bounds : Bounds.Horner),
      Gaussian.List.Proximity.CoefficientsClose left right coefficientBound →
      Data.Gaussian.Norm.Basic.normSq input ≤ inputNormSq →
      0 ≤ coefficientBound → 0 ≤ inputNormSq →
      0 ≤ bounds.value → 0 ≤ bounds.slope →
      Data.Gaussian.Norm.Basic.normSq (leftValue - rightValue) ≤ bounds.value →
      Data.Gaussian.Norm.Basic.normSq (leftDerivative - rightDerivative) ≤ bounds.slope →
      let leftResult := left.foldl
        (Dense.Derivative.evalDerivativeStep input)
        (leftValue, leftDerivative)
      let rightResult := right.foldl
        (Dense.Derivative.evalDerivativeStep input)
        (rightValue, rightDerivative)
      let finalBounds := Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsFrom left.length
        coefficientBound inputNormSq bounds
      Data.Gaussian.Norm.Basic.normSq (leftResult.1 - rightResult.1) ≤ finalBounds.value ∧
        Data.Gaussian.Norm.Basic.normSq (leftResult.2 - rightResult.2) ≤ finalBounds.slope
  | [], [], input, coefficientBound, inputNormSq,
      leftValue, leftDerivative, rightValue, rightDerivative, bounds,
      _close, _inputBound, _coefficientNonnegative, _inputNonnegative,
      _valueNonnegative, _slopeNonnegative, valueBound, derivativeBound =>
      ⟨valueBound, derivativeBound⟩
  | [], _ :: _, input, coefficientBound, inputNormSq,
      leftValue, leftDerivative, rightValue, rightDerivative, bounds,
      close, _inputBound, _coefficientNonnegative, _inputNonnegative,
      _valueNonnegative, _slopeNonnegative, _valueBound, _derivativeBound => by
      exact close.elim
  | _ :: _, [], input, coefficientBound, inputNormSq,
      leftValue, leftDerivative, rightValue, rightDerivative, bounds,
      close, _inputBound, _coefficientNonnegative, _inputNonnegative,
      _valueNonnegative, _slopeNonnegative, _valueBound, _derivativeBound => by
      exact close.elim
  | left :: leftTail, right :: rightTail, input, coefficientBound,
      inputNormSq, leftValue, leftDerivative, rightValue, rightDerivative,
      bounds, close, inputBound, coefficientNonnegative, inputNonnegative,
      valueNonnegative, slopeNonnegative, valueBound, derivativeBound => by
      rcases close with ⟨headClose, tailClose⟩
      let nextLeftValue := leftValue * input + left
      let nextRightValue := rightValue * input + right
      let nextLeftDerivative := leftDerivative * input + leftValue
      let nextRightDerivative := rightDerivative * input + rightValue
      let nextBounds := Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsStep inputNormSq
        coefficientBound bounds
      have nextValueIdentity : nextLeftValue - nextRightValue =
          (leftValue - rightValue) * input + (left - right) := by
        apply Gaussian.Basic.ext <;>
          simp only [nextLeftValue, nextRightValue, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re,
            Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1
      have nextDerivativeIdentity :
          nextLeftDerivative - nextRightDerivative =
            (leftDerivative - rightDerivative) * input +
              (leftValue - rightValue) := by
        apply Gaussian.Basic.ext <;>
          simp only [nextLeftDerivative, nextRightDerivative, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
            Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1
      have valueProduct :
          Data.Gaussian.Norm.Basic.normSq (leftValue - rightValue) * Data.Gaussian.Norm.Basic.normSq input ≤
            bounds.value * inputNormSq :=
        Fraction.Order.Arithmetic.mul_le_mul_direct valueBound inputBound
          (Gaussian.Norm.Basic.normSq_nonneg input) valueNonnegative
      have derivativeProduct :
          Data.Gaussian.Norm.Basic.normSq (leftDerivative - rightDerivative) * Data.Gaussian.Norm.Basic.normSq
            input ≤
            bounds.slope * inputNormSq :=
        Fraction.Order.Arithmetic.mul_le_mul_direct derivativeBound inputBound
          (Gaussian.Norm.Basic.normSq_nonneg input) slopeNonnegative
      have nextValueBound :
          Data.Gaussian.Norm.Basic.normSq (nextLeftValue - nextRightValue) ≤ nextBounds.value := by
        rw [nextValueIdentity]
        calc
          Data.Gaussian.Norm.Basic.normSq ((leftValue - rightValue) * input + (left - right)) ≤
              2 * (Data.Gaussian.Norm.Basic.normSq ((leftValue - rightValue) * input) +
                Data.Gaussian.Norm.Basic.normSq (left - right)) := Gaussian.Norm.Bounds.normSq_add_le_two _ _
          _ = 2 * (Data.Gaussian.Norm.Basic.normSq (leftValue - rightValue) * Data.Gaussian.Norm.Basic.normSq
            input +
                Data.Gaussian.Norm.Basic.normSq (left - right)) := by rw [Gaussian.Norm.Basic.normSq_mul]
          _ ≤ 2 * (bounds.value * inputNormSq + coefficientBound) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (add_le_add valueProduct headClose) (by decide)
          _ = nextBounds.value := rfl
      have nextDerivativeBound :
          Data.Gaussian.Norm.Basic.normSq (nextLeftDerivative - nextRightDerivative) ≤
            nextBounds.slope := by
        rw [nextDerivativeIdentity]
        calc
          Data.Gaussian.Norm.Basic.normSq ((leftDerivative - rightDerivative) * input +
              (leftValue - rightValue)) ≤
              2 * (Data.Gaussian.Norm.Basic.normSq ((leftDerivative - rightDerivative) * input) +
                Data.Gaussian.Norm.Basic.normSq (leftValue - rightValue)) := Gaussian.Norm.Bounds.normSq_add_le_two
                  _ _
          _ = 2 * (Data.Gaussian.Norm.Basic.normSq (leftDerivative - rightDerivative) *
            Data.Gaussian.Norm.Basic.normSq input +
                Data.Gaussian.Norm.Basic.normSq (leftValue - rightValue)) := by rw [Gaussian.Norm.Basic.normSq_mul]
          _ ≤ 2 * (bounds.slope * inputNormSq + bounds.value) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (add_le_add derivativeProduct valueBound) (by decide)
          _ = nextBounds.slope := rfl
      have nextNonnegative := Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsFrom_nonneg 1 bounds
        coefficientNonnegative inputNonnegative valueNonnegative
        slopeNonnegative
      simpa only [List.foldl_cons, List.length_cons,
        Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsFrom, Dense.Derivative.evalDerivativeStep,
        nextLeftValue, nextRightValue, nextLeftDerivative,
        nextRightDerivative, nextBounds] using
        Purelib.Polynomial.Dense.Gaussian.Bounds.Perturbation.Derivative.evalDerivativeCoeffs_sub_bounds leftTail
          rightTail input
          coefficientBound inputNormSq nextLeftValue nextLeftDerivative
          nextRightValue nextRightDerivative nextBounds tailClose inputBound
          coefficientNonnegative inputNonnegative nextNonnegative.1
          nextNonnegative.2 nextValueBound nextDerivativeBound

/-- One finite coefficientwise bound simultaneously controls evaluation and
automatic-derivative evaluation at the same displayed input.

The ordered coefficient lists satisfy their retained entrywise quadrance
bound, and the same input has bounded quadrance. The original paired
automatic-Horner scans begin at zero and share the computed finite budgets. -/
public theorem normSq_evalDerivative_sub_le
    (left right : List Gaussian.Basic.Canonical) (input : Gaussian.Basic.Canonical)
    (coefficientBound inputNormSq : Fraction.Rational)
    (close : Gaussian.List.Proximity.CoefficientsClose left right coefficientBound)
    (inputBound : Data.Gaussian.Norm.Basic.normSq input ≤ inputNormSq)
    (coefficientNonnegative : 0 ≤ coefficientBound)
    (inputNonnegative : 0 ≤ inputNormSq) :
    let leftResult := Dense.Derivative.evalDerivativeCoeffs input left
    let rightResult := Dense.Derivative.evalDerivativeCoeffs input right
    let bounds := Dense.Gaussian.Bounds.Perturbation.Derivative.coefficientPerturbationBounds left.length
      coefficientBound
      inputNormSq
    Data.Gaussian.Norm.Basic.normSq (leftResult.1 - rightResult.1) ≤ bounds.value ∧
      Data.Gaussian.Norm.Basic.normSq (leftResult.2 - rightResult.2) ≤ bounds.slope := by
  simpa only [Dense.Derivative.evalDerivativeCoeffs,
    Dense.Gaussian.Bounds.Perturbation.Derivative.coefficientPerturbationBounds] using
    Dense.Gaussian.Bounds.Perturbation.Derivative.evalDerivativeCoeffs_sub_bounds left right input coefficientBound
      inputNormSq 0 0 0 0 ⟨0, 0⟩ close inputBound coefficientNonnegative
      inputNonnegative le_rfl le_rfl (by rw [sub_self, Gaussian.Norm.Basic.normSq_zero])
      (by rw [sub_self, Gaussian.Norm.Basic.normSq_zero])

/-- Scaling the coefficient bound and both initial components scales both outputs of the finite perturbation recurrence.

The same rational factor scales the coefficient bound and both original
initial components. Scalar identities preserve that factor through every
step of the original finite recurrence. -/
private theorem perturbationBoundsFrom_scale : ∀ count
    (factor coefficientBound inputNormSq : Fraction.Rational)
    (bounds : Bounds.Horner),
    Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsFrom count (factor * coefficientBound) inputNormSq
        ⟨factor * bounds.value, factor * bounds.slope⟩ =
      let output := Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsFrom count coefficientBound
        inputNormSq bounds
      ⟨factor * output.value, factor * output.slope⟩
  | 0, factor, coefficientBound, inputNormSq, bounds => rfl
  | count + 1, factor, coefficientBound, inputNormSq, bounds => by
      change Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsFrom count (factor * coefficientBound)
          inputNormSq
          (Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsStep inputNormSq (factor * coefficientBound)
            ⟨factor * bounds.value, factor * bounds.slope⟩) = _
      have stepIdentity :
          Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsStep inputNormSq (factor * coefficientBound)
              ⟨factor * bounds.value, factor * bounds.slope⟩ =
            let next := Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsStep inputNormSq
              coefficientBound
              bounds
            ⟨factor * next.value, factor * next.slope⟩ := by
        rcases bounds with ⟨value, slope⟩
        simp only [Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsStep]
        congr 1 <;> ring1
      rw [stepIdentity]
      exact Purelib.Polynomial.Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsFrom_scale count factor
        coefficientBound
        inputNormSq (Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsStep inputNormSq coefficientBound
          bounds)

/-- Scaling the common coefficient perturbation bound scales both computed value and derivative bounds.

The zero initial bounds retain the supplied rational scale factor. The
original recurrence therefore scales both displayed output bounds without
changing the coefficient count or input quadrance. -/
public theorem coefficientPerturbationBounds_scale
    (count : Nat) (factor coefficientBound inputNormSq : Fraction.Rational) :
    Dense.Gaussian.Bounds.Perturbation.Derivative.coefficientPerturbationBounds count (factor * coefficientBound)
        inputNormSq =
      let output := Dense.Gaussian.Bounds.Perturbation.Derivative.coefficientPerturbationBounds count coefficientBound
        inputNormSq
      ⟨factor * output.value, factor * output.slope⟩ := by
  simpa only [Dense.Gaussian.Bounds.Perturbation.Derivative.coefficientPerturbationBounds,
    Fraction.Field.mul_zero_direct] using
      Dense.Gaussian.Bounds.Perturbation.Derivative.perturbationBoundsFrom_scale count factor coefficientBound
        inputNormSq ⟨0, 0⟩

end Purelib.Polynomial.Dense.Gaussian.Bounds.Perturbation.Derivative
