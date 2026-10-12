module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.List.NormBounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Bounds.Horner
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Horner
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

open Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor (HornerTaylorNormBounds)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor.Uniform
open Purelib.Data.Gaussian

/-- The value and slope components of the Taylor fold agree with the ordinary Horner bounds when their initial
components agree. -/
private theorem denseHornerNormTaylor_fields : ∀
    (coefficients : List Gaussian.Basic.Canonical) (inputNormSq : Fraction.Rational)
    (normBounds : Polynomial.Bounds.Horner)
    (taylorBounds : HornerTaylorNormBounds),
    normBounds.value = taylorBounds.value →
    normBounds.slope = taylorBounds.slope →
    let normFinal := coefficients.foldl
      (Dense.Gaussian.Bounds.Horner.step inputNormSq) normBounds
    let taylorFinal := coefficients.foldl
      (HornerTaylorNormBounds.step inputNormSq)
        taylorBounds
    normFinal.value = taylorFinal.value ∧
      normFinal.slope = taylorFinal.slope
  | [], inputNormSq, normBounds, taylorBounds, valueEqual, slopeEqual =>
      ⟨valueEqual, slopeEqual⟩
  | coefficient :: remaining, inputNormSq, normBounds, taylorBounds,
      valueEqual, slopeEqual => by
      simp only [List.foldl_cons]
      apply denseHornerNormTaylor_fields remaining inputNormSq
      · simp only [Dense.Gaussian.Bounds.Horner.step,
          HornerTaylorNormBounds.step]
        rw [valueEqual]
      · simp only [Dense.Gaussian.Bounds.Horner.step,
          HornerTaylorNormBounds.step]
        rw [valueEqual, slopeEqual]

end Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor.Uniform

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor.Uniform
open Purelib.Data.Gaussian

/-- Advance value, slope and Taylor-remainder bounds using one common coefficient quadrance ceiling. -/
def uniformTaylorStep (inputNormSq coefficientBound :
  Fraction.Rational)
    (bounds : HornerTaylorNormBounds) : HornerTaylorNormBounds
      where
  value := 2 * (bounds.value * inputNormSq + coefficientBound)
  slope := 2 * (bounds.slope * inputNormSq + bounds.value)
  remainder := 2 * (bounds.slope + inputNormSq * bounds.remainder)
end Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor.Uniform

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor.Uniform
open Purelib.Data.Gaussian

/-- Iterate the uniform Taylor-bound step for a displayed coefficient count from the supplied initial bounds. -/
def uniformTaylorBoundsFrom : Nat → Fraction.Rational →
  Fraction.Rational →
    HornerTaylorNormBounds → HornerTaylorNormBounds
  | 0, _, _, bounds => bounds
  | count + 1, coefficientBound, inputNormSq, bounds =>
      uniformTaylorBoundsFrom count coefficientBound inputNormSq
        (uniformTaylorStep inputNormSq coefficientBound bounds)
end Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor.Uniform

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor.Uniform
open Purelib.Data.Gaussian

/-- The uniform coefficient ceiling bounds all three components of the actual Taylor fold.

The input radius and coefficient ceiling are nonnegative, and the actual initial components are nonnegative and bounded
by their uniform counterparts. -/
private theorem denseTaylorFold_le_uniform : ∀
    (coefficients : List Gaussian.Basic.Canonical) {coefficientBound inputNormSq : Fraction.Rational}
    (actual uniform : HornerTaylorNormBounds),
    Purelib.Data.Gaussian.List.NormBounds.CoefficientsNormLe coefficients coefficientBound →
    0 ≤ coefficientBound → 0 ≤ inputNormSq →
    0 ≤ actual.value → 0 ≤ actual.slope →
    0 ≤ actual.remainder →
    actual.value ≤ uniform.value →
    actual.slope ≤ uniform.slope →
    actual.remainder ≤ uniform.remainder →
    let actualFinal := coefficients.foldl
      (HornerTaylorNormBounds.step inputNormSq) actual
    let uniformFinal := uniformTaylorBoundsFrom coefficients.length
      coefficientBound inputNormSq uniform
    actualFinal.value ≤ uniformFinal.value ∧
      actualFinal.slope ≤ uniformFinal.slope ∧
      actualFinal.remainder ≤ uniformFinal.remainder
  | [], coefficientBound, inputNormSq, actual, uniform,
      _bounded, _coefficientNonnegative, _inputNonnegative,
      _actualValueNonnegative, _actualSlopeNonnegative,
      _actualRemainderNonnegative, valueOrder, slopeOrder, remainderOrder =>
      ⟨valueOrder, slopeOrder, remainderOrder⟩
  | coefficient :: remaining, coefficientBound, inputNormSq, actual, uniform,
      bounded, coefficientNonnegative, inputNonnegative,
      actualValueNonnegative, actualSlopeNonnegative,
      actualRemainderNonnegative, valueOrder, slopeOrder, remainderOrder => by
      let actualNext := HornerTaylorNormBounds.step
        inputNormSq actual coefficient
      let uniformNext := uniformTaylorStep inputNormSq coefficientBound uniform
      have actualNextNonnegative :
          0 ≤ actualNext.value ∧ 0 ≤ actualNext.slope ∧
            0 ≤ actualNext.remainder := by
        constructor
        · exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (add_nonneg
              (Fraction.Order.Arithmetic.mul_nonneg_direct
                actualValueNonnegative inputNonnegative)
              (Gaussian.Norm.Basic.normSq_nonneg coefficient))
        constructor
        · exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (add_nonneg
              (Fraction.Order.Arithmetic.mul_nonneg_direct
                actualSlopeNonnegative inputNonnegative)
              actualValueNonnegative)
        · exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (add_nonneg actualSlopeNonnegative
              (Fraction.Order.Arithmetic.mul_nonneg_direct
                inputNonnegative actualRemainderNonnegative))
      have valueNext : actualNext.value ≤ uniformNext.value := by
        apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _
          (by decide)
        exact add_le_add
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            valueOrder inputNonnegative) bounded.1
      have slopeNext : actualNext.slope ≤ uniformNext.slope := by
        apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _
          (by decide)
        exact add_le_add
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            slopeOrder inputNonnegative) valueOrder
      have remainderNext : actualNext.remainder ≤ uniformNext.remainder := by
        apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _
          (by decide)
        exact add_le_add slopeOrder
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            remainderOrder inputNonnegative)
      simpa only [List.foldl_cons, List.length_cons,
        uniformTaylorBoundsFrom, actualNext, uniformNext] using
        denseTaylorFold_le_uniform remaining actualNext
          uniformNext bounded.2
          coefficientNonnegative inputNonnegative actualNextNonnegative.1
          actualNextNonnegative.2.1 actualNextNonnegative.2.2 valueNext
          slopeNext remainderNext
end Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor.Uniform

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor.Uniform
open Purelib.Data.Gaussian

/-- Compute uniform value, slope and Taylor-remainder bounds from zero for the supplied coefficient count. -/
def uniformTaylorBounds (count : Nat)
    (coefficientBound inputNormSq : Fraction.Rational) : HornerTaylorNormBounds :=
  uniformTaylorBoundsFrom count coefficientBound inputNormSq ⟨0, 0, 0⟩
end Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor.Uniform

end
