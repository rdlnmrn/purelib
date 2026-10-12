module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Nat.Order
import Purelib.Algebra.Group.Negation
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Quadratic Taylor bounds propagated by a finite Horner fold

Each original coefficient updates value, displacement and quadratic-remainder
bounds together. The same coefficient list and paired derivative fold retain
all three accumulator estimates without replacing their executable data.
-/

open scoped Purelib.Data.Nat
open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor

@[expose] public section

set_option genInjectivity false in
/-- Retain value, displacement and quadratic-remainder coefficients for a finite Horner scan.

The three original rational fields bound accumulator quadrance, the squared
value difference relative to squared displacement, and the squared first-order
Taylor remainder relative to fourth-order displacement. -/
structure HornerTaylorNormBounds where
  /-- An upper bound for the squared norm of either value accumulator. -/ value : Fraction.Rational
  /-- The coefficient of squared displacement in the value-difference bound. -/ slope : Fraction.Rational
  /-- The coefficient of fourth-order displacement in the squared Taylor remainder bound. -/ remainder :
    Fraction.Rational

constructive_injectivity HornerTaylorNormBounds

end

end Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor

-- Preserve the original compiler-derived instance names and exposed decision body.
namespace Purelib.Polynomial.Bounds
@[expose] public section

deriving instance DecidableEq for Dense.Gaussian.Bounds.Taylor.HornerTaylorNormBounds

end
end Purelib.Polynomial.Bounds

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor

/-- Propagate value, displacement and quadratic Taylor bounds through one Horner step.

The update uses the common input quadrance bound and the current Gaussian coefficient. -/
@[expose] public def HornerTaylorNormBounds.step (radiusSq : Fraction.Rational)
    (bounds : Dense.Gaussian.Bounds.Taylor.HornerTaylorNormBounds) (coefficient : Gaussian.Basic.Canonical) :
    Dense.Gaussian.Bounds.Taylor.HornerTaylorNormBounds where
  value := 2 * (bounds.value * radiusSq + Gaussian.Norm.Basic.normSq coefficient)
  slope := 2 * (bounds.slope * radiusSq + bounds.value)
  remainder := 2 * (bounds.slope + radiusSq * bounds.remainder)

section
/-- A finite Horner fold preserves the three nonnegative Taylor bounds.

Assuming both inputs lie within the displayed squared radius and the initial accumulators satisfy the bounds, the final
values, difference and first-order Taylor error satisfy the folded bounds. -/
private theorem evalTaylorNormBoundsCoeffs_spec
    (coeffs : List Gaussian.Basic.Canonical) {radiusSq : Fraction.Rational} {x y : Gaussian.Basic.Canonical}
    (radiusNonnegative : 0 ≤ radiusSq)
    (xBound : Gaussian.Norm.Basic.normSq x ≤ radiusSq) (yBound : Gaussian.Norm.Basic.normSq y ≤
      radiusSq)
    (accX accY derivativeY : Gaussian.Basic.Canonical) (bounds : Dense.Gaussian.Bounds.Taylor.HornerTaylorNormBounds)
    (valueNonnegative : 0 ≤ bounds.value)
    (slopeNonnegative : 0 ≤ bounds.slope)
    (remainderNonnegative : 0 ≤ bounds.remainder)
    (accXBound : Gaussian.Norm.Basic.normSq accX ≤ bounds.value)
    (accYBound : Gaussian.Norm.Basic.normSq accY ≤ bounds.value)
    (differenceBound : Gaussian.Norm.Basic.normSq (accX - accY) ≤
      bounds.slope * Gaussian.Norm.Basic.normSq (x - y))
    (taylorBound : Gaussian.Norm.Basic.normSq
        (accX - accY - derivativeY * (x - y)) ≤
      bounds.remainder * Gaussian.Norm.Basic.normSq (x - y) ^ 2) :
    let finalX := coeffs.foldl
      (fun accumulator coefficient => accumulator * x + coefficient) accX
    let finalY := coeffs.foldl
      (fun accumulator coefficient => accumulator * y + coefficient) accY
    let finalDerivativeY := coeffs.foldl
      (Dense.Derivative.evalDerivativeStep y) (accY, derivativeY) |>.2
    let finalBounds := coeffs.foldl
      (Dense.Gaussian.Bounds.Taylor.HornerTaylorNormBounds.step radiusSq) bounds
    0 ≤ finalBounds.value ∧ 0 ≤ finalBounds.slope ∧
      0 ≤ finalBounds.remainder ∧
      Gaussian.Norm.Basic.normSq finalX ≤ finalBounds.value ∧
      Gaussian.Norm.Basic.normSq finalY ≤ finalBounds.value ∧
      Gaussian.Norm.Basic.normSq (finalX - finalY) ≤
        finalBounds.slope * Gaussian.Norm.Basic.normSq (x - y) ∧
      Gaussian.Norm.Basic.normSq (finalX - finalY - finalDerivativeY * (x - y)) ≤
        finalBounds.remainder * Gaussian.Norm.Basic.normSq (x - y) ^ 2 := by
  induction coeffs generalizing accX accY derivativeY bounds with
  | nil =>
      exact ⟨valueNonnegative, slopeNonnegative, remainderNonnegative,
        accXBound, accYBound, differenceBound, taylorBound⟩
  | cons coefficient coeffs inductionHypothesis =>
      simp only [List.foldl_cons]
      apply inductionHypothesis
      · apply Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        exact add_nonneg
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            valueNonnegative radiusNonnegative)
          (Gaussian.Norm.Basic.normSq_nonneg coefficient)
      · apply Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        exact add_nonneg
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            slopeNonnegative radiusNonnegative)
          valueNonnegative
      · apply Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        exact add_nonneg slopeNonnegative
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            radiusNonnegative remainderNonnegative)
      · have productBound : Gaussian.Norm.Basic.normSq accX * Gaussian.Norm.Basic.normSq x ≤
            bounds.value * radiusSq :=
          Fraction.Order.Arithmetic.mul_le_mul_direct accXBound xBound
            (Gaussian.Norm.Basic.normSq_nonneg x) valueNonnegative
        calc
          Gaussian.Norm.Basic.normSq (accX * x + coefficient) ≤
              2 * (Gaussian.Norm.Basic.normSq (accX * x) + Gaussian.Norm.Basic.normSq coefficient) :=
            Gaussian.Norm.Bounds.normSq_add_le_two _ _
          _ = 2 * (Gaussian.Norm.Basic.normSq accX * Gaussian.Norm.Basic.normSq x +
            Gaussian.Norm.Basic.normSq coefficient) := by
            rw [Gaussian.Norm.Basic.normSq_mul]
          _ ≤ 2 * (bounds.value * radiusSq + Gaussian.Norm.Basic.normSq coefficient) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (add_le_add productBound (le_refl _)) (by decide)
      · have productBound : Gaussian.Norm.Basic.normSq accY * Gaussian.Norm.Basic.normSq y ≤
            bounds.value * radiusSq :=
          Fraction.Order.Arithmetic.mul_le_mul_direct accYBound yBound
            (Gaussian.Norm.Basic.normSq_nonneg y) valueNonnegative
        calc
          Gaussian.Norm.Basic.normSq (accY * y + coefficient) ≤
              2 * (Gaussian.Norm.Basic.normSq (accY * y) + Gaussian.Norm.Basic.normSq coefficient) :=
            Gaussian.Norm.Bounds.normSq_add_le_two _ _
          _ = 2 * (Gaussian.Norm.Basic.normSq accY * Gaussian.Norm.Basic.normSq y +
            Gaussian.Norm.Basic.normSq coefficient) := by
            rw [Gaussian.Norm.Basic.normSq_mul]
          _ ≤ 2 * (bounds.value * radiusSq + Gaussian.Norm.Basic.normSq coefficient) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (add_le_add productBound (le_refl _)) (by decide)
      · have identity :
            (accX * x + coefficient) - (accY * y + coefficient) =
              (accX - accY) * x + accY * (x - y) := by
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
              Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;>
            ring1
        rw [identity]
        have firstProduct : Gaussian.Norm.Basic.normSq (accX - accY) * Gaussian.Norm.Basic.normSq x ≤
            (bounds.slope * Gaussian.Norm.Basic.normSq (x - y)) * radiusSq :=
          Fraction.Order.Arithmetic.mul_le_mul_direct differenceBound xBound
            (Gaussian.Norm.Basic.normSq_nonneg x)
            (Fraction.Order.Arithmetic.mul_nonneg_direct slopeNonnegative
              (Gaussian.Norm.Basic.normSq_nonneg (x - y)))
        have secondProduct : Gaussian.Norm.Basic.normSq accY * Gaussian.Norm.Basic.normSq (x - y) ≤
            bounds.value * Gaussian.Norm.Basic.normSq (x - y) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            accYBound (Gaussian.Norm.Basic.normSq_nonneg (x - y))
        calc
          Gaussian.Norm.Basic.normSq ((accX - accY) * x + accY * (x - y)) ≤
              2 * (Gaussian.Norm.Basic.normSq ((accX - accY) * x) +
                Gaussian.Norm.Basic.normSq (accY * (x - y))) := Gaussian.Norm.Bounds.normSq_add_le_two _ _
          _ = 2 * (Gaussian.Norm.Basic.normSq (accX - accY) * Gaussian.Norm.Basic.normSq x +
                Gaussian.Norm.Basic.normSq accY * Gaussian.Norm.Basic.normSq (x - y)) := by
            rw [Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul]
          _ ≤ 2 * ((bounds.slope * Gaussian.Norm.Basic.normSq (x - y)) * radiusSq +
                bounds.value * Gaussian.Norm.Basic.normSq (x - y)) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (add_le_add firstProduct secondProduct) (by decide)
          _ = 2 * (bounds.slope * radiusSq + bounds.value) *
                Gaussian.Norm.Basic.normSq (x - y) := by ring1
      · have identity :
            (accX * x + coefficient) - (accY * y + coefficient) -
                (derivativeY * y + accY) * (x - y) =
              (accX - accY) * (x - y) +
                (accX - accY - derivativeY * (x - y)) * y := by
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
              Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;>
            ring1
        rw [identity]
        have firstProduct :
            Gaussian.Norm.Basic.normSq (accX - accY) * Gaussian.Norm.Basic.normSq (x - y) ≤
              bounds.slope * Gaussian.Norm.Basic.normSq (x - y) ^ 2 := by
          calc
            Gaussian.Norm.Basic.normSq (accX - accY) * Gaussian.Norm.Basic.normSq (x - y) ≤
                (bounds.slope * Gaussian.Norm.Basic.normSq (x - y)) * Gaussian.Norm.Basic.normSq (x -
                  y) :=
              Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
                differenceBound (Gaussian.Norm.Basic.normSq_nonneg (x - y))
            _ = bounds.slope * Gaussian.Norm.Basic.normSq (x - y) ^ 2 := by ring1
        have taylorProductNonnegative :
            0 ≤ bounds.remainder * Gaussian.Norm.Basic.normSq (x - y) ^ 2 :=
          Fraction.Order.Arithmetic.mul_nonneg_direct remainderNonnegative
            (Fraction.Order.Arithmetic.pow_nonneg_direct
              (Gaussian.Norm.Basic.normSq_nonneg (x - y)) 2)
        have secondProduct :
            Gaussian.Norm.Basic.normSq (accX - accY - derivativeY * (x - y)) *
              Gaussian.Norm.Basic.normSq y ≤
              (bounds.remainder * Gaussian.Norm.Basic.normSq (x - y) ^ 2) * radiusSq :=
          Fraction.Order.Arithmetic.mul_le_mul_direct taylorBound yBound
            (Gaussian.Norm.Basic.normSq_nonneg y) taylorProductNonnegative
        calc
          Gaussian.Norm.Basic.normSq ((accX - accY) * (x - y) +
              (accX - accY - derivativeY * (x - y)) * y) ≤
            2 * (Gaussian.Norm.Basic.normSq ((accX - accY) * (x - y)) +
              Gaussian.Norm.Basic.normSq ((accX - accY - derivativeY * (x - y)) * y)) :=
                Gaussian.Norm.Bounds.normSq_add_le_two _ _
          _ = 2 * (Gaussian.Norm.Basic.normSq (accX - accY) * Gaussian.Norm.Basic.normSq (x - y) +
              Gaussian.Norm.Basic.normSq (accX - accY - derivativeY * (x - y)) *
                Gaussian.Norm.Basic.normSq y) := by rw [Gaussian.Norm.Basic.normSq_mul,
                  Gaussian.Norm.Basic.normSq_mul]
          _ ≤ 2 * (bounds.slope * Gaussian.Norm.Basic.normSq (x - y) ^ 2 +
              (bounds.remainder * Gaussian.Norm.Basic.normSq (x - y) ^ 2) * radiusSq) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (add_le_add firstProduct secondProduct) (by decide)
          _ = 2 * (bounds.slope + radiusSq * bounds.remainder) *
              Gaussian.Norm.Basic.normSq (x - y) ^ 2 := by ring1
end

end Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor
