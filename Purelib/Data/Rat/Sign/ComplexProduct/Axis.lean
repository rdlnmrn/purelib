module

public import Purelib.Data.Rat.Sign.Typed
import Purelib.Data.Rat.Sign.Typed.Compatibility
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

/-!
# Factor signs on the complex coordinate axes

A nonzero left factor has positive squared norm. Exact real and imaginary
product equations then recover both signs of the right factor by positive scaling.
-/

namespace Purelib.Data.Rat.Sign.ComplexProduct.Axis

open Purelib.Data.Rat
open Purelib.Data.Sign
open _root_.Purelib.Data renaming Sign -> FiniteSign

/-- A nonzero left complex factor and a real product determine both signs of the right factor.

The left factor has at least one nonzero component, while the supplied product equations set its imaginary component to
zero. Multiplication by the positive squared norm transports the two exact sign identities; the real product component
may itself be zero. -/
public theorem rightSigns_of_productImag_zero
    (A B C D E : Fraction.Rational)
    (leftNonzero : A ≠ 0 ∨ B ≠ 0)
    (realIdentity : E = A * C - B * D)
    (imaginaryZero : 0 = A * D + B * C) :
    FiniteSign.ofCoordinate C =
        FiniteSign.mul (FiniteSign.ofCoordinate E)
          (FiniteSign.ofCoordinate A) ∧
      FiniteSign.ofCoordinate D =
        FiniteSign.neg (FiniteSign.mul (FiniteSign.ofCoordinate E)
          (FiniteSign.ofCoordinate B)) := by
  let normSq := A ^ 2 + B ^ 2
  have normPositive : 0 < normSq := by
    simpa only [normSq] using Purelib.Data.Rat.Bounds.Square.sum_sq_pos_of_ne_zero leftNonzero
  have ADRelation : A * D = -(B * C) := by
    calc
      A * D = (A * D + B * C) - B * C := by ring1
      _ = 0 - B * C := by rw [← imaginaryZero]
      _ = -(B * C) := by ring1
  have BCRelation : B * C = -(A * D) := by
    calc
      B * C = (A * D + B * C) - A * D := by ring1
      _ = 0 - A * D := by rw [← imaginaryZero]
      _ = -(A * D) := by ring1
  have realScale : E * A = normSq * C := by
    rw [realIdentity]
    calc
      (A * C - B * D) * A = A ^ 2 * C - B * (A * D) := by ring1
      _ = A ^ 2 * C - B * (-(B * C)) := by rw [ADRelation]
      _ = normSq * C := by
        dsimp only [normSq]
        ring1
  have imagScale : E * B = -(normSq * D) := by
    rw [realIdentity]
    calc
      (A * C - B * D) * B = A * (B * C) - B ^ 2 * D := by ring1
      _ = A * (-(A * D)) - B ^ 2 * D := by rw [BCRelation]
      _ = -(normSq * D) := by
        dsimp only [normSq]
        ring1
  constructor
  · rw [← Purelib.Data.Rat.Sign.Typed.Compatibility.ofCoordinate_mul_pos_left normSq C normPositive,
      ← realScale, FiniteSign.ofCoordinate_mul]
  · have scaled := Purelib.Data.Rat.Sign.Typed.Compatibility.ofCoordinate_mul_pos_left normSq D normPositive
    have signEquation := congrArg FiniteSign.ofCoordinate imagScale
    rw [FiniteSign.ofCoordinate_mul, FiniteSign.ofCoordinate_neg,
      scaled] at signEquation
    exact Sign.eq_neg_of_eq_neg signEquation

/-- A nonzero left complex factor and an imaginary product determine both signs of the right factor.

The left factor has at least one nonzero component, while the supplied product equations set its real component to zero.
Multiplication by its positive squared norm gives the two signs of the right factor from the imaginary product
component. -/
public theorem rightSigns_of_productReal_zero
    (A B C D H : Fraction.Rational)
    (leftNonzero : A ≠ 0 ∨ B ≠ 0)
    (realZero : 0 = A * C - B * D)
    (imagIdentity : H = A * D + B * C) :
    FiniteSign.ofCoordinate C =
        FiniteSign.mul (FiniteSign.ofCoordinate H)
          (FiniteSign.ofCoordinate B) ∧
      FiniteSign.ofCoordinate D =
        FiniteSign.mul (FiniteSign.ofCoordinate H)
          (FiniteSign.ofCoordinate A) := by
  let normSq := A ^ 2 + B ^ 2
  have normPositive : 0 < normSq := by
    simpa only [normSq] using Purelib.Data.Rat.Bounds.Square.sum_sq_pos_of_ne_zero leftNonzero
  have ACRelation : A * C = B * D := by
    calc
      A * C = (A * C - B * D) + B * D := by ring1
      _ = 0 + B * D := by rw [← realZero]
      _ = B * D := by ring1
  have BDRelation : B * D = A * C := ACRelation.symm
  have realScale : H * B = normSq * C := by
    rw [imagIdentity]
    calc
      (A * D + B * C) * B = A * (B * D) + B ^ 2 * C := by ring1
      _ = A * (A * C) + B ^ 2 * C := by rw [BDRelation]
      _ = normSq * C := by
        dsimp only [normSq]
        ring1
  have imagScale : H * A = normSq * D := by
    rw [imagIdentity]
    calc
      (A * D + B * C) * A = A ^ 2 * D + B * (A * C) := by ring1
      _ = A ^ 2 * D + B * (B * D) := by rw [ACRelation]
      _ = normSq * D := by
        dsimp only [normSq]
        ring1
  constructor
  · rw [← Purelib.Data.Rat.Sign.Typed.Compatibility.ofCoordinate_mul_pos_left normSq C normPositive,
      ← realScale, FiniteSign.ofCoordinate_mul]
  · rw [← Purelib.Data.Rat.Sign.Typed.Compatibility.ofCoordinate_mul_pos_left normSq D normPositive,
      ← imagScale, FiniteSign.ofCoordinate_mul]

end Purelib.Data.Rat.Sign.ComplexProduct.Axis
