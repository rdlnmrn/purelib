module

public import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Field
public import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Data.Rat.Quadratic.Bounds
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Mathlib.Algebra.Field.Defs
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Exact rational retraction to the unit circle

An aligned real sign makes the conjugate denominator have quadrance at least
one. A single Gaussian division then gives a rational unit-circle point. Its
exact residual identity bounds displacement by the original norm defect.
-/

namespace Purelib.Geometry.Rational.Circle

open Purelib.Data
open Gaussian.Basic (Canonical)
open Rat.Fraction (Rational)
open Rat.Fraction.Order

/-- The original symmetric unit box containing the rational unit circle. -/
@[expose] public def boundingBox : Box := Box.symmetric 1 (by decide)

/-- Every rational unit-circle point belongs to the original symmetric unit box. -/
public theorem inside_boundingBox {point : Canonical} (unit : Canonical.normSq point = 1) :
    boundingBox.Contains point := by
  have realSquare : point.re ^ 2 ≤ 1 := by
    have bound := Arithmetic.add_le_add_direct (show point.re ^ 2 ≤ point.re ^ 2 from le_rfl)
      (Arithmetic.sq_nonneg_direct point.im)
    have realBound : point.re ^ 2 ≤ Canonical.normSq point := by
      calc
        point.re ^ 2 = point.re ^ 2 + 0 := by ring1
        _ ≤ point.re ^ 2 + point.im ^ 2 := bound
        _ = Canonical.normSq point := by rw [Canonical.normSq, pow_two, pow_two]
    exact realBound.trans_eq unit
  have imaginarySquare : point.im ^ 2 ≤ 1 := by
    have bound := Arithmetic.add_le_add_right_direct (Arithmetic.sq_nonneg_direct point.re) (point.im ^ 2)
    have imaginaryBound : point.im ^ 2 ≤ Canonical.normSq point := by
      calc
        point.im ^ 2 = 0 + point.im ^ 2 := by ring1
        _ ≤ point.re ^ 2 + point.im ^ 2 := bound
        _ = Canonical.normSq point := by rw [Canonical.normSq, pow_two, pow_two]
    exact imaginaryBound.trans_eq unit
  exact ⟨Rat.Quadratic.neg_one_le_of_sq_le_one realSquare, Rat.Quadratic.le_one_of_sq_le_one realSquare,
    Rat.Quadratic.neg_one_le_of_sq_le_one imaginarySquare, Rat.Quadratic.le_one_of_sq_le_one imaginarySquare⟩

set_option genInjectivity false in
/-- A retained rational unit-circle point near one original Gaussian rational.

The sign, numerator, denominator and quotient retain their exact construction
equations. The denominator is uniformly apart from zero, and the squared
displacement is bounded by the squared quadrance defect of the original point. -/
public structure Retraction (source : Canonical) where
  /-- The real sign selected from the original real coordinate. -/ sign : Rational
  /-- The sign is the exact executable half-plane decision. -/ sign_eq : sign = if 0 ≤ source.re then 1 else -1
  /-- The chosen sign has square one. -/ sign_square : sign ^ 2 = 1
  /-- The chosen sign is aligned with the original real coordinate. -/ aligned : 0 ≤ sign * source.re
  /-- The retained conjugate denominator. -/ denominator : Canonical
  /-- The denominator uses this original source and retained sign. -/ denominator_eq :
    denominator = Canonical.conj source + ⟨sign, 0⟩
  /-- The denominator quadrance, computed once. -/ denominatorNorm : Rational
  /-- This quadrance belongs to the exact retained denominator. -/ denominatorNorm_eq :
    denominatorNorm = Canonical.normSq denominator
  /-- The denominator quadrance is at least one. -/ denominatorNorm_one : 1 ≤ denominatorNorm
  /-- The retained signed numerator. -/ numerator : Canonical
  /-- The numerator uses this same source and sign. -/ numerator_eq :
    numerator = (⟨sign, 0⟩ : Canonical) * (source + ⟨sign, 0⟩)
  /-- The retained unit-circle point. -/ point : Canonical
  /-- The point is the actual quotient of the retained numerator and denominator. -/ point_eq :
    point = numerator * denominator⁻¹
  /-- The quotient lies exactly on the unit circle. -/ unit : Canonical.normSq point = 1
  /-- Clearing the displacement gives the original scalar quadrance defect. -/ residual_eq :
    (source - point) * denominator = ⟨Canonical.normSq source - 1, 0⟩
  /-- The displacement quadrance is bounded by the squared original norm defect. -/ distance_le :
    Canonical.normSq (source - point) ≤ (Canonical.normSq source - 1) ^ 2

constructive_injectivity Retraction

namespace Retraction

/-- Construct the quotient from one aligned sign and its exact selection equation. -/
@[expose] public def ofSign (source : Canonical) (sign : Rational)
    (signEq : sign = if 0 ≤ source.re then 1 else -1)
    (signSquare : sign ^ 2 = 1) (aligned : 0 ≤ sign * source.re) : Retraction source := by
  let scalar : Canonical := ⟨sign, 0⟩
  let denominator := Canonical.conj source + scalar
  let denominatorNorm := Canonical.normSq denominator
  have normOne : 1 ≤ denominatorNorm := by
    apply Arithmetic.le_of_sub_nonneg_direct
    have nonnegative : 0 ≤ Canonical.normSq source + 2 * (sign * source.re) :=
      add_nonneg (Canonical.normSq_nonneg source)
        (Arithmetic.mul_nonneg_direct (by decide) aligned)
    calc
      0 ≤ Canonical.normSq source + 2 * (sign * source.re) := nonnegative
      _ = denominatorNorm - 1 := by
        dsimp only [denominatorNorm, denominator, scalar, Canonical.conj, Canonical.normSq]
        simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im]
        have square : sign * sign = 1 := by simpa only [pow_two] using signSquare
        calc
          source.re * source.re + source.im * source.im + 2 * (sign * source.re) =
              (source.re + sign) * (source.re + sign) + (-source.im + 0) * (-source.im + 0) - sign * sign := by ring1
          _ = (source.re + sign) * (source.re + sign) + (-source.im + 0) * (-source.im + 0) - 1 := by rw [square]
  have denominatorNonzero : denominator ≠ 0 := by
    intro zero
    have zeroNorm : denominatorNorm = 0 := by
      change Canonical.normSq denominator = 0
      rw [zero, Canonical.normSq_zero]
    rw [zeroNorm] at normOne
    exact (show ¬ (1 : Rational) ≤ 0 by decide) normOne
  let numerator := scalar * (source + scalar)
  have scalarNorm : Canonical.normSq scalar = 1 := by
    change sign * sign + 0 * 0 = 1
    have square : sign * sign = 1 := by simpa only [pow_two] using signSquare
    rw [square]
    ring1
  have numeratorNorm : Canonical.normSq numerator = denominatorNorm := by
    rw [Canonical.normSq_mul, scalarNorm, Rat.Fraction.Field.one_mul]
    dsimp only [denominatorNorm, denominator, scalar, Canonical.conj, Canonical.normSq]
    simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im]
    ring1
  let point := numerator * denominator⁻¹
  have unit : Canonical.normSq point = 1 := by
    rw [Canonical.normSq_mul, Canonical.normSq_inv denominator denominatorNonzero, numeratorNorm]
    exact Rat.Fraction.Field.mul_inv_cancel _
      (lt_of_lt_of_le (show (0 : Rational) < 1 by decide) normOne).ne'
  have pointDenominator : point * denominator = numerator := by
    change (numerator * denominator⁻¹) * denominator = numerator
    rw [Gaussian.Basic.mul_assoc, Canonical.inv_mul_cancel denominator denominatorNonzero,
      Gaussian.Basic.mul_one]
  have residual : (source - point) * denominator = ⟨Canonical.normSq source - 1, 0⟩ := by
    calc
      (source - point) * denominator = source * denominator - point * denominator := by ring1
      _ = source * denominator - numerator := by rw [pointDenominator]
      _ = ⟨Canonical.normSq source - 1, 0⟩ := by
        apply Gaussian.Basic.ext
        · change source.re * (source.re + sign) - source.im * (-source.im + 0) -
            (sign * (source.re + sign) - 0 * (source.im + 0)) =
              Canonical.normSq source - 1
          dsimp only [Canonical.normSq]
          have square : sign * sign = 1 := by simpa only [pow_two] using signSquare
          calc
            source.re * (source.re + sign) - source.im * (-source.im + 0) -
                (sign * (source.re + sign) - 0 * (source.im + 0)) =
                source.re * source.re + source.im * source.im - sign * sign := by ring1
            _ = source.re * source.re + source.im * source.im - 1 := by rw [square]
        · change source.re * (-source.im + 0) + source.im * (source.re + sign) -
            (sign * (source.im + 0) + 0 * (source.re + sign)) = 0
          ring1
  have distanceScaled : Canonical.normSq (source - point) * denominatorNorm =
      (Canonical.normSq source - 1) ^ 2 := by
    change Canonical.normSq (source - point) * Canonical.normSq denominator = _
    rw [← Canonical.normSq_mul, residual]
    change (Canonical.normSq source - 1) * (Canonical.normSq source - 1) + 0 * 0 = _
    rw [Rat.Fraction.Field.zero_mul_direct, _root_.add_zero, pow_two]
  exact
    { sign, sign_eq := signEq, sign_square := signSquare, aligned
      denominator, denominator_eq := rfl
      denominatorNorm, denominatorNorm_eq := rfl, denominatorNorm_one := normOne
      numerator, numerator_eq := rfl, point, point_eq := rfl, unit
      residual_eq := residual
      distance_le := by
        calc
          Canonical.normSq (source - point) = Canonical.normSq (source - point) * 1 :=
            (Rat.Fraction.Field.mul_one_direct _).symm
          _ ≤ Canonical.normSq (source - point) * denominatorNorm :=
            Arithmetic.mul_le_mul_of_nonneg_left_direct normOne (Canonical.normSq_nonneg _)
          _ = (Canonical.normSq source - 1) ^ 2 := distanceScaled }

/-- Compute a rational unit-circle point with a certified quadrance-defect displacement bound.

The original point's real-coordinate sign selects the denominator. The
constructor computes and retains that denominator, its norm and the quotient
once; no square root or limiting operation is used. -/
@[expose] public def prepare (source : Canonical) : Retraction source :=
  if nonnegative : 0 ≤ source.re then
    ofSign source 1 (by rw [if_pos nonnegative]) (by decide)
      (by simpa only [Rat.Fraction.Field.one_mul] using nonnegative)
  else
    ofSign source (-1) (by rw [if_neg nonnegative]) (by decide)
      (by
        have nonpositive : source.re ≤ 0 := (lt_of_not_ge nonnegative).le
        have negated := Arithmetic.neg_le_neg_direct nonpositive
        calc
          0 = -(0 : Rational) := by decide
          _ ≤ -source.re := negated
          _ = (-1 : Rational) * source.re := by ring1)

/-- Retraction fixes an original point already on the rational unit circle. -/
public theorem fixed {source : Canonical} (data : Retraction source)
    (unit : Canonical.normSq source = 1) : data.point = source := by
  have squareZero : (Canonical.normSq source - 1) ^ 2 = 0 := by rw [unit]; decide
  have distance := data.distance_le
  rw [squareZero] at distance
  have normZero : Canonical.normSq (source - data.point) = 0 :=
    le_antisymm distance (Canonical.normSq_nonneg _)
  have differenceZero := (Canonical.normSq_eq_zero _).mp normZero
  calc
    data.point = source - (source - data.point) := by ring1
    _ = source := by rw [differenceZero]; ring1

end Retraction
end Purelib.Geometry.Rational.Circle
