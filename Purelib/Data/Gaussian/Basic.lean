module
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Basic
public import Purelib.Data.Rat.Fraction.Field

import Mathlib.Algebra.Ring.MinimalAxioms
-- The exposed Gaussian ring retains the constructor's original recursive operations.
import Purelib.Algebra.Ring.Basic
import Purelib.Algebra.Ring.Multiplication
import Purelib.Algebra.Group.Negation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Basic

open Purelib.Data
open Purelib.Data.Rat

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

set_option genInjectivity false in
/-- Retain a Gaussian rational as two canonical exact rational coordinates.

The real and imaginary fields are structural canonical rationals. Equality and
arithmetic inspect those retained finite representations directly. -/
@[ext]
structure Canonical where
  /-- The retained canonical real rational coordinate. -/ re : Fraction.Rational
  /-- The retained canonical imaginary rational coordinate. -/ im : Fraction.Rational
deriving DecidableEq

constructive_injectivity Canonical

namespace Canonical

end Canonical
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- The Gaussian zero pair has both rational coordinates zero. -/
instance : Zero Canonical := ⟨⟨0, 0⟩⟩

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- The Gaussian unit pair has real coordinate one and imaginary coordinate zero. -/
instance : One Canonical := ⟨⟨1, 0⟩⟩

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Add Gaussian pairs by adding their retained rational coordinates. -/
instance : Add Canonical :=
  ⟨fun left right => ⟨left.re + right.re, left.im + right.im⟩⟩

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Negate Gaussian pairs by negating both retained rational coordinates. -/
instance : Neg Canonical := ⟨fun source => ⟨-source.re, -source.im⟩⟩

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Subtract Gaussian pairs coordinatewise. -/
instance : Sub Canonical :=
  ⟨fun left right => ⟨left.re - right.re, left.im - right.im⟩⟩

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Multiply Gaussian pairs using the exact complex-coordinate product formula. -/
instance : Mul Canonical :=
  ⟨fun left right =>
    ⟨left.re * right.re - left.im * right.im,
      left.re * right.im + left.im * right.re⟩⟩

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Rational coordinate subtraction is definitionally addition of the negated second
coordinate. -/
private theorem coordinate_sub_eq_add_neg (left right : Fraction.Rational)
  :
    left - right = left + -right := rfl

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Interchange the first two rational summands under right association. -/
private theorem coordinate_add_left_comm (first second third :
  Fraction.Rational) :
    first + (second + third) = second + (first + third) := by
  calc
    first + (second + third) = (first + second) + third :=
      (_root_.add_assoc first second third).symm
    _ = (second + first) + third := by
      rw [_root_.add_comm first second]
    _ = second + (first + third) :=
      _root_.add_assoc second first third

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Reassociate four rational summands with the fourth moved beside the first. -/
private theorem coordinate_add_four_real
    (first second third fourth : Fraction.Rational) :
    (first + second) + (third + fourth) =
      (first + fourth) + (second + third) := by
  calc
    (first + second) + (third + fourth) =
        first + (second + (third + fourth)) :=
      _root_.add_assoc first second (third + fourth)
    _ = first + (fourth + (second + third)) := by
      rw [← _root_.add_assoc second third fourth,
        _root_.add_comm (second + third) fourth]
    _ = (first + fourth) + (second + third) :=
      (_root_.add_assoc first fourth (second + third)).symm

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Reassociate four rational summands with the third moved beside the first. -/
private theorem coordinate_add_four_imaginary
    (first second third fourth : Fraction.Rational) :
    (first + second) + (third + fourth) =
      (first + third) + (fourth + second) := by
  calc
    (first + second) + (third + fourth) =
        first + (second + (third + fourth)) :=
      _root_.add_assoc first second (third + fourth)
    _ = first + (third + (fourth + second)) := by
      rw [coordinate_add_left_comm second third fourth,
        _root_.add_comm second fourth]
    _ = (first + third) + (fourth + second) :=
      (_root_.add_assoc first third (fourth + second)).symm

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Read the exact real coordinate formula for Gaussian zero. -/
@[simp] theorem zero_re : (0 : Canonical).re = 0 := rfl

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Read the exact imaginary coordinate formula for Gaussian zero. -/
@[simp] theorem zero_im : (0 : Canonical).im = 0 := rfl

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Read the exact real coordinate formula for Gaussian one. -/
@[simp] theorem one_re : (1 : Canonical).re = 1 := rfl

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Read the exact imaginary coordinate formula for Gaussian one. -/
@[simp] theorem one_im : (1 : Canonical).im = 0 := rfl

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Read the exact real coordinate formula for Gaussian addition. -/
@[simp] theorem add_re (left right : Canonical) :
    (left + right).re = left.re + right.re := rfl

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Read the exact imaginary coordinate formula for Gaussian addition. -/
@[simp] theorem add_im (left right : Canonical) :
    (left + right).im = left.im + right.im := rfl

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Read the exact real coordinate formula for Gaussian negation. -/
@[simp] theorem neg_re (source : Canonical) : (-source).re = -source.re :=
  rfl

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Read the exact imaginary coordinate formula for Gaussian negation. -/
@[simp] theorem neg_im (source : Canonical) : (-source).im = -source.im :=
  rfl

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Read the exact real coordinate formula for Gaussian subtraction. -/
@[simp] theorem sub_re (left right : Canonical) :
    (left - right).re = left.re - right.re := rfl

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Read the exact imaginary coordinate formula for Gaussian subtraction. -/
@[simp] theorem sub_im (left right : Canonical) :
    (left - right).im = left.im - right.im := rfl

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Read the exact real coordinate formula for Gaussian multiplication. -/
@[simp] theorem mul_re (left right : Canonical) :
    (left * right).re = left.re * right.re - left.im * right.im := rfl

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Read the exact imaginary coordinate formula for Gaussian multiplication. -/
@[simp] theorem mul_im (left right : Canonical) :
    (left * right).im = left.re * right.im + left.im * right.re := rfl

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Gaussian subtraction equals addition of the negated second pair. -/
theorem sub_eq_add_neg (left right : Canonical) :
    left - right = left + -right := rfl

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Gaussian addition is associative. -/
theorem add_assoc (first second third : Canonical) :
    first + second + third = first + (second + third) := by
  apply Canonical.ext <;> simp only [add_re, add_im] <;> ring1

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Gaussian addition is commutative. -/
theorem add_comm (left right : Canonical) : left + right = right + left :=
  by
  apply Canonical.ext <;> simp only [add_re, add_im] <;> ring1

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Adding Gaussian zero on the left retains the original pair. -/
theorem zero_add (source : Canonical) : 0 + source = source := by
  apply Canonical.ext <;> change (0 : Fraction.Rational) + _ = _ <;> ring1

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- The negated Gaussian pair added to the original pair gives zero. -/
theorem neg_add_cancel (source : Canonical) : -source + source = 0 := by
  apply Canonical.ext <;> change -(_ : Fraction.Rational) + _ = 0 <;> ring1

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Gaussian multiplication is associative. -/
theorem mul_assoc (first second third : Canonical) :
    first * second * third = first * (second * third) := by
  apply Canonical.ext
  · simp only [mul_re, mul_im, coordinate_sub_eq_add_neg, _root_.add_mul,
      _root_.mul_add, _root_.neg_mul, _root_.mul_neg,
      _root_.neg_add_rev, Fraction.mul_assoc]
    exact coordinate_add_four_real
      (first.re * (second.re * third.re))
      (-(first.im * (second.im * third.re)))
      (-(first.im * (second.re * third.im)))
      (-(first.re * (second.im * third.im)))
  · simp only [mul_re, mul_im, coordinate_sub_eq_add_neg, _root_.add_mul,
      _root_.mul_add, _root_.neg_mul, _root_.mul_neg,
      Fraction.mul_assoc]
    exact coordinate_add_four_imaginary
      (first.re * (second.re * third.im))
      (-(first.im * (second.im * third.im)))
      (first.re * (second.im * third.re))
      (first.im * (second.re * third.re))

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Gaussian multiplication is commutative. -/
theorem mul_comm (left right : Canonical) : left * right = right * left :=
  by
  apply Canonical.ext <;>
    simp only [mul_re, mul_im, coordinate_sub_eq_add_neg] <;> ring1

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Multiplication by Gaussian one on the left retains the original pair. -/
theorem one_mul (source : Canonical) : 1 * source = source := by
  apply Canonical.ext
  · change (1 : Fraction.Rational) * source.re - 0 * source.im = source.re
    rw [coordinate_sub_eq_add_neg]
    ring1
  · change (1 : Fraction.Rational) * source.im + 0 * source.re = source.im
    ring1

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Gaussian multiplication distributes over addition in its right argument. -/
theorem left_distrib (first second third : Canonical) :
    first * (second + third) = first * second + first * third := by
  apply Canonical.ext <;>
    simp only [mul_re, mul_im, add_re, add_im,
      coordinate_sub_eq_add_neg] <;> ring1

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

open Purelib.Algebra

/-- Canonical Gaussian coordinates form a commutative ring.

The coordinate operations and the original recursive scalar, power and
cast operations are retained. The coordinate laws provide the ring
certificates, with subtraction retaining its two displayed differences. -/
instance instCommRing : CommRing Canonical :=
  Ring.commRingOfAxioms add_assoc zero_add neg_add_cancel mul_assoc mul_comm
    one_mul left_distrib (fun left right => ⟨left.re - right.re, left.im - right.im⟩)
    (fun _ _ => rfl)

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Subtracting the original Gaussian base from its corrected difference gives the
negated correction. -/
theorem sub_sub_right (base correction : Canonical) :
    (base - correction) - base = -correction := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  have cancel : base + -base = 0 := by
    rw [add_comm base (-base)]
    exact neg_add_cancel base
  calc
    base + -correction + -base = base + (-correction + -base) :=
      add_assoc base (-correction) (-base)
    _ = base + (-base + -correction) := by
      rw [add_comm (-correction) (-base)]
    _ = (base + -base) + -correction :=
      (add_assoc base (-base) (-correction)).symm
    _ = 0 + -correction := by rw [cancel]
    _ = -correction := zero_add (-correction)

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- The zero Gaussian rational differs from the unit Gaussian rational. -/
theorem zero_ne_one : (0 : Canonical) ≠ 1 := by
  intro equal
  have realEqual := congrArg Canonical.re equal
  exact Fraction.zero_ne_one realEqual

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- The distinct structural Gaussian values zero and one certify nontriviality. -/
instance : Nontrivial Canonical := ⟨0, 1, zero_ne_one⟩

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Conjugate the Gaussian pair by retaining its real coordinate and negating its
imaginary coordinate. -/
def conj (source : Canonical) : Canonical := ⟨source.re, -source.im⟩

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Conjugating a Gaussian pair twice returns the original pair. -/
@[simp] theorem conj_conj (source : Canonical) : conj
  (conj source) = source := by
  apply Canonical.ext
  · rfl
  · change -(-source.im) = source.im
    ring1

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Gaussian conjugation preserves addition. -/
@[simp] theorem conj_add (left right : Canonical) :
    conj (left + right) = conj left + conj right := by
  apply Canonical.ext
  · rfl
  · change -(left.im + right.im) = -left.im + -right.im
    ring1

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

open Purelib.Algebra Purelib.Data.Rat

/-- Conjugation preserves multiplication of canonical Gaussian pairs.

The real product is unchanged by negating both imaginary factors. The
imaginary product is negated, giving the product of the two conjugate pairs. -/
@[simp] theorem conj_mul (left right : Canonical) :
    conj (left * right) = conj left * conj right := by
  apply Canonical.ext
  · change left.re * right.re - left.im * right.im =
      left.re * right.re - (-left.im) * (-right.im)
    rw [Ring.Multiplication.neg_mul_neg]
  · change -(left.re * right.im + left.im * right.re) =
      left.re * (-right.im) + (-left.im) * right.re
    rw [Ring.Multiplication.mul_neg, Ring.Multiplication.neg_mul]
    exact (_root_.neg_add_rev _ _).trans (Fraction.add_comm _ _)

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

open Purelib.Data.Gaussian.Basic in
/-- The original canonical Gaussian carrier, retained as an exact reducible alias. -/
abbrev SourceEncodingEncoderGaussianAlias := Canonical

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic
section Compatibility

/-- The canonical rational coordinate carrier. -/
abbrev Coordinate := Fraction.Rational

end Compatibility
end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.ExplicitLegendrePreparedData

open Purelib.Data.Gaussian.Basic in
/-- Build the canonical Gaussian rational with the two supplied exact coordinates. -/
def point (x y : Fraction.Rational) : Canonical := ⟨x,
  y⟩

end Purelib.Data.Gaussian.Basic.ExplicitLegendrePreparedData
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.ExplicitLegendrePreparedPeriods

open Purelib.Data.Gaussian.Basic in
/-- Build the canonical Gaussian rational with the two supplied exact coordinates. -/
def point (x y : Fraction.Rational) : Canonical :=
  ⟨x, y⟩

end Purelib.Data.Gaussian.Basic.ExplicitLegendrePreparedPeriods
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Conjugate the Gaussian pair by retaining its real coordinate and negating its
imaginary coordinate. -/
def conj (source : Canonical) : Canonical := ⟨source.re, -source.im⟩

/-- The two retained Gaussian conjugation operations have identical coordinate
computations. -/
theorem conj_eq_canonical
    (source : Canonical) :
    conj source =
      Canonical.conj source := rfl

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- The original canonical Gaussian pair with independently reduced rational coordinates. -/
abbrev Number := Canonical

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Compute Gaussian addition on the retained working pair coordinates. -/
def add (left right : Number) : Number :=
  left + right

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Gaussian addition is associative. -/
theorem add_assoc (first second third : Canonical) :
    first + second + third = first + (second + third) :=
  _root_.add_assoc first second third

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Gaussian addition is commutative. -/
theorem add_comm (left right : Canonical) : left + right = right + left :=
  _root_.add_comm left right

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Read the exact imaginary coordinate formula for Gaussian addition. -/
@[simp] theorem add_im (left right : Canonical) :
    (left + right).im = left.im + right.im := rfl

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Read the exact real coordinate formula for Gaussian addition. -/
@[simp] theorem add_re (left right : Canonical) :
    (left + right).re = left.re + right.re := rfl

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Adding Gaussian zero on the right retains the original pair. -/
@[simp] theorem add_zero (source : Canonical) : source + 0 = source :=
  _root_.add_zero source

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Return the original Gaussian pair, whose coordinates are already canonical. -/
def canonical (source : Canonical) : Canonical := source

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Canonicalization retains the original Gaussian pair exactly. -/
theorem canonical_eq (source : Canonical) : canonical source = source
  := rfl

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Gaussian conjugation preserves addition. -/
@[simp] theorem conj_add (left right : Canonical) :
    conj (left + right) = conj left + conj right :=
  Canonical.conj_add left right

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Conjugating a Gaussian pair twice returns the original pair. -/
@[simp] theorem conj_conj (source : Canonical) : conj (conj source)
  = source :=
  Canonical.conj_conj source

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Gaussian conjugation preserves multiplication. -/
@[simp] theorem conj_mul (left right : Canonical) :
    conj (left * right) = conj left * conj right :=
  Canonical.conj_mul left right

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Gaussian conjugation preserves zero. -/
@[simp] theorem conj_zero : conj (0 : Canonical) = 0 := rfl

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Equality of both exact rational coordinates gives equality of Gaussian pairs. -/
@[ext] theorem ext {left right : Canonical}
    (real : left.re = right.re) (imaginary : left.im = right.im) :
    left = right :=
  Canonical.ext real imaginary

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Read the retained exact imaginary coordinate. -/
abbrev im : Canonical → Fraction.Rational := Canonical.im

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Number

/-- Read the retained exact imaginary coordinate. -/
abbrev im : Number → ReducedFraction :=
  Gaussian.Basic.im

end Purelib.Data.Gaussian.Basic.Number
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Gaussian multiplication distributes over addition in its right argument. -/
theorem left_distrib (first second third : Canonical) :
    first * (second + third) = first * second + first * third :=
  Canonical.left_distrib first second third

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Compute Gaussian multiplication on the retained working pair coordinates. -/
def mul (left right : Number) : Number :=
  left * right

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Gaussian multiplication is associative. -/
theorem mul_assoc (first second third : Canonical) :
    first * second * third = first * (second * third) :=
  _root_.mul_assoc first second third

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Gaussian multiplication is commutative. -/
theorem mul_comm (left right : Canonical) : left * right = right * left :=
  _root_.mul_comm left right

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Read the exact imaginary coordinate formula for Gaussian multiplication. -/
@[simp] theorem mul_im (left right : Canonical) :
    (left * right).im = left.re * right.im + left.im * right.re := rfl

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Multiplication by Gaussian one on the right retains the original pair. -/
@[simp] theorem mul_one (source : Canonical) : source * 1 = source :=
  _root_.mul_one source

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

open Purelib.Data.Gaussian.Basic in
/-- Reassociate a four-factor Gaussian product without changing the factor order. -/
theorem mul_pair_reassociate (a b c d : Canonical) :
    (a * b) * (c * d) = (a * (b * c)) * d := by
  calc
    (a * b) * (c * d) = ((a * b) * c) * d :=
      (_root_.mul_assoc (a * b) c d).symm
    _ = (a * (b * c)) * d := by
      rw [_root_.mul_assoc a b c]

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Read the exact real coordinate formula for Gaussian multiplication. -/
@[simp] theorem mul_re (left right : Canonical) :
    (left * right).re = left.re * right.re - left.im * right.im := rfl

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Multiplication by Gaussian zero on the left gives zero. -/
@[simp] theorem zero_mul (source : Canonical) : 0 * source = 0 := by
  apply ext
  · change (0 : Fraction.Rational) * source.re - 0 * source.im = 0
    rw [Field.zero_mul_direct,
      Field.zero_mul_direct,
      Arithmetic.sub_eq_add_neg_direct, neg_zero,
      _root_.zero_add]
  · change (0 : Fraction.Rational) * source.im + 0 * source.re = 0
    rw [Field.zero_mul_direct,
      Field.zero_mul_direct,
      _root_.zero_add]

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Multiplication by Gaussian zero on the right gives zero. -/
@[simp] theorem mul_zero (source : Canonical) : source * 0 = 0 := by
  rw [_root_.mul_comm]
  exact zero_mul source

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Compute Gaussian negation on the retained working pair coordinates. -/
def neg (source : Number) : Number :=
  -source

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Read the exact imaginary coordinate formula for Gaussian negation. -/
@[simp] theorem neg_im (source : Canonical) : (-source).im = -source.im := rfl

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Read the exact real coordinate formula for Gaussian negation. -/
@[simp] theorem neg_re (source : Canonical) : (-source).re = -source.re := rfl

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- View the canonical Gaussian pair as the identical working number. -/
def ofGaussian (source : Canonical) : Number :=
  source

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Read the exact imaginary coordinate formula for Gaussian one. -/
@[simp] theorem one_im : (1 : Canonical).im = 0 := rfl

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Multiplication by Gaussian one on the left retains the original pair. -/
@[simp] theorem one_mul (source : Canonical) : 1 * source = source :=
  _root_.one_mul source

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Read the exact real coordinate formula for Gaussian one. -/
@[simp] theorem one_re : (1 : Canonical).re = 1 := rfl

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

open Purelib.Data.Gaussian.Basic in
/-- Build the canonical Gaussian rational with the two supplied exact coordinates. -/
def point (x y : Fraction.Rational) : Canonical := ⟨x, y⟩

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- The displayed Gaussian pair has the supplied imaginary coordinate. -/
@[simp] private theorem pointImaginaryEighth (x y : Fraction.Rational) :
  (point x y).im = y := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- The displayed Gaussian pair has the supplied imaginary coordinate. -/
@[simp] private theorem pointImaginaryFifth (x y : Fraction.Rational) :
  (point x y).im = y := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- The displayed Gaussian pair has the supplied imaginary coordinate. -/
@[simp] private theorem pointImaginaryFourth (x y : Fraction.Rational) :
  (point x y).im = y := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- The displayed Gaussian pair has the supplied imaginary coordinate. -/
@[simp] private theorem pointImaginarySecond (x y : Fraction.Rational) :
  (point x y).im = y := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- The displayed Gaussian pair has the supplied imaginary coordinate. -/
@[simp] private theorem pointImaginarySeventh (x y : Fraction.Rational) :
  (point x y).im = y := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- The displayed Gaussian pair has the supplied imaginary coordinate. -/
@[simp] private theorem pointImaginarySixth (x y : Fraction.Rational) :
  (point x y).im = y := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- The displayed Gaussian pair has the supplied imaginary coordinate. -/
@[simp] private theorem pointImaginaryThird (x y : Fraction.Rational) :
  (point x y).im = y := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- The displayed Gaussian pair has the supplied real coordinate. -/
@[simp] private theorem pointRealEighth (x y : Fraction.Rational) :
  (point x y).re = x := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- The displayed Gaussian pair has the supplied real coordinate. -/
@[simp] private theorem pointRealFifth (x y : Fraction.Rational) :
  (point x y).re = x := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- The displayed Gaussian pair has the supplied real coordinate. -/
@[simp] private theorem pointRealFourth (x y : Fraction.Rational) :
  (point x y).re = x := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- The displayed Gaussian pair has the supplied real coordinate. -/
@[simp] private theorem pointRealSecond (x y : Fraction.Rational) :
  (point x y).re = x := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- The displayed Gaussian pair has the supplied real coordinate. -/
@[simp] private theorem pointRealSeventh (x y : Fraction.Rational) :
  (point x y).re = x := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- The displayed Gaussian pair has the supplied real coordinate. -/
@[simp] private theorem pointRealSixth (x y : Fraction.Rational) :
  (point x y).re = x := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- The displayed Gaussian pair has the supplied real coordinate. -/
@[simp] private theorem pointRealThird (x y : Fraction.Rational) :
  (point x y).re = x := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Read the retained exact real coordinate. -/
abbrev re : Canonical → Fraction.Rational := Canonical.re

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Number

/-- Read the retained exact real coordinate. -/
abbrev re : Number → ReducedFraction :=
  Gaussian.Basic.re

end Purelib.Data.Gaussian.Basic.Number
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Gaussian.Basic

/-- Conjugation preserves a nonzero canonical Gaussian pair. -/
theorem conj_ne_zero {z : Canonical} (nonzero : z ≠ 0) :
    conj z ≠ 0 := by
  intro conjugateZero
  have twice := congrArg conj conjugateZero
  rw [conj_conj] at twice
  exact nonzero twice

end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

open Purelib.Data.Rat

open Purelib.Data.Gaussian.Basic in
/-- A zero difference of canonical Gaussian pairs identifies their coordinates.

Each retained scalar difference gives an equality after additive
cancellation, and the two coordinate equalities identify the finite pair. -/
theorem gaussian_eq_of_sub_eq_zero
    {left right : Canonical} (difference : left - right = 0) :
    left = right := by
  apply ext
  · have realDifference := congrArg
        re difference
    change left.re - right.re = 0 at realDifference
    change left.re + -right.re = 0 at realDifference
    have realEquality := congrArg (fun value => value + right.re) realDifference
    rw [Fraction.add_assoc, Fraction.neg_add_cancel, _root_.add_zero,
      Fraction.zero_add] at realEquality
    exact realEquality
  · have imaginaryDifference := congrArg
        im difference
    change left.im - right.im = 0 at imaginaryDifference
    change left.im + -right.im = 0 at imaginaryDifference
    have imaginaryEquality := congrArg (fun value => value + right.im)
      imaginaryDifference
    rw [Fraction.add_assoc, Fraction.neg_add_cancel, _root_.add_zero,
      Fraction.zero_add] at imaginaryEquality
    exact imaginaryEquality

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- A displayed Gaussian pair with nonzero real coordinate is nonzero. -/
public theorem point_ne_zero_of_re_ne {x y : Fraction.Rational} (realNonzero : x ≠
  0) :
    point x y ≠ 0 := by
  intro equality
  have realEquality := congrArg re equality
  exact realNonzero realEquality

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Gaussian multiplication distributes over addition in its left argument. -/
theorem right_distrib (first second third : Canonical) :
    (first + second) * third = first * third + second * third :=
  _root_.add_mul first second third

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Compute Gaussian subtraction on the retained working pair coordinates. -/
def sub (left right : Number) : Number :=
  left - right

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Gaussian subtraction equals addition of the negated second pair. -/
theorem sub_eq_add_neg (left right : Canonical) :
    left - right = left + -right :=
  _root_.sub_eq_add_neg left right

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Read the exact imaginary coordinate formula for Gaussian subtraction. -/
@[simp] theorem sub_im (left right : Canonical) :
    (left - right).im = left.im - right.im := rfl

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Read the exact real coordinate formula for Gaussian subtraction. -/
@[simp] theorem sub_re (left right : Canonical) :
    (left - right).re = left.re - right.re := rfl

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Subtracting a Gaussian pair from itself gives zero. -/
@[simp] theorem sub_self (source : Canonical) : source - source = 0 :=
  _root_.sub_self source

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Subtracting canonical Gaussian zero preserves the original pair. -/
@[simp] theorem sub_zero (source : Canonical) : source - 0 = source := by
  rw [Canonical.sub_eq_add_neg, _root_.neg_zero, _root_.add_zero]

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Read the canonical Gaussian value of the identical working pair. -/
def value (source : Number) : Canonical :=
  source

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-! ## Semantic entry points -/

/-- Compute Gaussian addition through the identity working-pair representation. -/
def normalizedAdd (left right : Canonical) : Canonical :=
  value (add (ofGaussian left) (ofGaussian right))

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Compute Gaussian multiplication through the identity working-pair representation. -/
def normalizedMul (left right : Canonical) : Canonical :=
  value (mul (ofGaussian left) (ofGaussian right))

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Compute Gaussian negation through the identity working-pair representation. -/
def normalizedNeg (source : Canonical) : Canonical :=
  value (neg (ofGaussian source))

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Compute Gaussian subtraction through the identity working-pair representation. -/
def normalizedSub (left right : Canonical) : Canonical :=
  value (sub (ofGaussian left) (ofGaussian right))

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Reading and rewrapping a working Gaussian pair retains that pair. -/
theorem ofGaussian_value (source : Number) :
    ofGaussian (value source) = source := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Reading the Gaussian value commutes with addition. -/
theorem value_add (left right : Number) :
    value (add left right) = value left + value right := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Reading the Gaussian value commutes with addition. -/
@[simp] theorem value_add_instance (left right : Canonical) :
    value (left + right) = value left + value right := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- The identity readback of working Gaussian pairs is injective. -/
theorem value_injective : Function.Injective value := by
  intro left right equal
  exact equal

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Reading the Gaussian value commutes with multiplication. -/
theorem value_mul (left right : Number) :
    value (mul left right) = value left * value right := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Reading the Gaussian value commutes with multiplication. -/
@[simp] theorem value_mul_instance (left right : Canonical) :
    value (left * right) = value left * value right := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Reading the Gaussian value commutes with negation. -/
theorem value_neg (source : Number) :
    value (neg source) = -value source := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Reading the Gaussian value commutes with negation. -/
@[simp] theorem value_neg_instance (source : Canonical) :
    value (-source) = -value source := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Wrapping and reading a canonical Gaussian pair retains that pair. -/
theorem value_ofGaussian (source : Canonical) :
    value (ofGaussian source) = source := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Working-pair Gaussian addition equals the original canonical operation. -/
@[simp] theorem normalizedAdd_eq (left right : Canonical) :
    normalizedAdd left right = left + right := by
  rw [normalizedAdd, value_add, value_ofGaussian,
    value_ofGaussian]

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Working-pair Gaussian multiplication equals the original canonical operation. -/
@[simp] theorem normalizedMul_eq (left right : Canonical) :
    normalizedMul left right = left * right := by
  rw [normalizedMul, value_mul, value_ofGaussian,
    value_ofGaussian]

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Working-pair Gaussian negation equals the original canonical operation. -/
@[simp] theorem normalizedNeg_eq (source : Canonical) :
    normalizedNeg source = -source := by
  rw [normalizedNeg, value_neg, value_ofGaussian]

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- The working-pair readback retains Gaussian one. -/
@[simp] theorem value_one : value (1 : Canonical) = 1 := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Reading the Gaussian value commutes with subtraction. -/
theorem value_sub (left right : Number) :
    value (sub left right) = value left - value right := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Working-pair Gaussian subtraction equals the original canonical operation. -/
@[simp] theorem normalizedSub_eq (left right : Canonical) :
    normalizedSub left right = left - right := by
  rw [normalizedSub, value_sub, value_ofGaussian,
    value_ofGaussian]

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- Reading the Gaussian value commutes with subtraction. -/
@[simp] theorem value_sub_instance (left right : Canonical) :
    value (left - right) = value left - value right := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section

namespace Purelib.Data.Gaussian.Basic

open Purelib.Data.Gaussian.Basic in
/-- Readback commutes with coordinatewise Gaussian conjugation. -/
theorem value_workingConjugate (source : Number) :
    value (conj source) =
      conj
        (value source) := by
  rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic

/-- The working-pair readback retains Gaussian zero. -/
@[simp] theorem value_zero : value (0 : Canonical) = 0 := rfl

end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Adding Gaussian zero on the left retains the original pair. -/
@[simp] theorem zero_add (source : Canonical) : 0 + source = source :=
  _root_.zero_add source

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Read the exact imaginary coordinate formula for Gaussian zero. -/
@[simp] theorem zero_im : (0 : Canonical).im = 0 := rfl

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Read the exact real coordinate formula for Gaussian zero. -/
@[simp] theorem zero_re : (0 : Canonical).re = 0 := rfl

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic
section Basic

/-- Subtracting a Gaussian pair from zero gives its negation. -/
@[simp] theorem zero_sub (source : Canonical) : 0 - source = -source := by
  rw [_root_.sub_eq_add_neg, _root_.zero_add]

end Basic
end Purelib.Data.Gaussian.Basic
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.BoundaryCanonical

open Purelib.Data.Gaussian.Basic in
/-- The unit Gaussian rational differs from zero. -/
theorem one_ne_zero : (1 : Canonical) ≠ 0 := by
  intro oneZero
  have realOneZero := congrArg Gaussian.Basic.re oneZero
  exact Field.zero_ne_one realOneZero.symm

end Purelib.Data.Gaussian.BoundaryCanonical
end

section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedCertificates

open Purelib.Data.Gaussian.Basic in
/-- The original canonical Gaussian carrier, retained as an exact reducible alias. -/
private abbrev Gaussian := Canonical

end Purelib.Examples.Riemann.ExplicitQuarticPreparedCertificates
end

section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedCertificates

/-- The displayed Gaussian pair has the supplied imaginary coordinate. -/
@[simp] private theorem pointImaginary (x y : Fraction.Rational) : (Gaussian.Basic.point x y).im = y := rfl

end Purelib.Examples.Riemann.ExplicitQuarticPreparedCertificates
end

section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedCertificates

/-- The displayed Gaussian pair has the supplied real coordinate. -/
@[simp] private theorem pointReal (x y : Fraction.Rational) : (Gaussian.Basic.point x y).re = x := rfl

end Purelib.Examples.Riemann.ExplicitQuarticPreparedCertificates
end

section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedHorizontalCells

open Purelib.Data.Gaussian.Basic in
/-- The original canonical Gaussian carrier, retained as an exact reducible alias. -/
private abbrev Gaussian := Canonical

end Purelib.Examples.Riemann.ExplicitQuarticPreparedHorizontalCells
end

section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCell

/-- The displayed Gaussian pair has the supplied imaginary coordinate. -/
@[simp] private theorem pointImaginary (x y : Fraction.Rational) : (Gaussian.Basic.point x y).im = y := rfl

end Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCell
end

section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCell

/-- The displayed Gaussian pair has the supplied real coordinate. -/
@[simp] private theorem pointReal (x y : Fraction.Rational) : (Gaussian.Basic.point x y).re = x := rfl

end Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCell
end

section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated

open Purelib.Data.Gaussian.Basic

namespace ExplicitQuarticPreparedALeftSampleCertificatesPart1

/-- The original canonical Gaussian carrier, retained as an exact reducible alias. -/
private abbrev
  Gaussian
  := Canonical

end ExplicitQuarticPreparedALeftSampleCertificatesPart1
namespace ExplicitQuarticPreparedALeftSampleCertificatesPart2

/-- The original canonical Gaussian carrier, retained as an exact reducible alias. -/
private abbrev
  Gaussian
  := Canonical

end ExplicitQuarticPreparedALeftSampleCertificatesPart2
namespace ExplicitQuarticPreparedALeftSampleCertificatesPart3

/-- The original canonical Gaussian carrier, retained as an exact reducible alias. -/
private abbrev
  Gaussian
  := Canonical

end ExplicitQuarticPreparedALeftSampleCertificatesPart3
namespace ExplicitQuarticPreparedALeftSampleCertificatesPart4

/-- The original canonical Gaussian carrier, retained as an exact reducible alias. -/
private abbrev
  Gaussian
  := Canonical

end ExplicitQuarticPreparedALeftSampleCertificatesPart4
namespace ExplicitQuarticPreparedALeftSampleCertificatesPart5

/-- The original canonical Gaussian carrier, retained as an exact reducible alias. -/
private abbrev
  Gaussian
  := Canonical

end ExplicitQuarticPreparedALeftSampleCertificatesPart5
namespace ExplicitQuarticPreparedALeftSampleCertificatesPart6

/-- The original canonical Gaussian carrier, retained as an exact reducible alias. -/
private abbrev
  Gaussian
  := Canonical

end ExplicitQuarticPreparedALeftSampleCertificatesPart6
namespace ExplicitQuarticPreparedALeftSampleCertificatesPart7

/-- The original canonical Gaussian carrier, retained as an exact reducible alias. -/
private abbrev
  Gaussian
  := Canonical

end ExplicitQuarticPreparedALeftSampleCertificatesPart7
namespace ExplicitQuarticPreparedARightSampleCertificatesPart1

/-- The original canonical Gaussian carrier, retained as an exact reducible alias. -/
private abbrev
  Gaussian
  := Canonical

end ExplicitQuarticPreparedARightSampleCertificatesPart1
namespace ExplicitQuarticPreparedARightSampleCertificatesPart2

/-- The original canonical Gaussian carrier, retained as an exact reducible alias. -/
private abbrev
  Gaussian
  := Canonical

end ExplicitQuarticPreparedARightSampleCertificatesPart2
namespace ExplicitQuarticPreparedARightSampleCertificatesPart3

/-- The original canonical Gaussian carrier, retained as an exact reducible alias. -/
private abbrev
  Gaussian
  := Canonical

end ExplicitQuarticPreparedARightSampleCertificatesPart3
namespace ExplicitQuarticPreparedARightSampleCertificatesPart4

/-- The original canonical Gaussian carrier, retained as an exact reducible alias. -/
private abbrev
  Gaussian
  := Canonical

end ExplicitQuarticPreparedARightSampleCertificatesPart4
namespace ExplicitQuarticPreparedARightSampleCertificatesPart5

/-- The original canonical Gaussian carrier, retained as an exact reducible alias. -/
private abbrev
  Gaussian
  := Canonical

end ExplicitQuarticPreparedARightSampleCertificatesPart5
namespace ExplicitQuarticPreparedARightSampleCertificatesPart6

/-- The original canonical Gaussian carrier, retained as an exact reducible alias. -/
private abbrev
  Gaussian
  := Canonical

end ExplicitQuarticPreparedARightSampleCertificatesPart6
namespace ExplicitQuarticPreparedARightSampleCertificatesPart7

/-- The original canonical Gaussian carrier, retained as an exact reducible alias. -/
private abbrev
  Gaussian
  := Canonical

end ExplicitQuarticPreparedARightSampleCertificatesPart7
end Purelib.Examples.Riemann.QuarticPrepared.Generated
end

public section
namespace Purelib.Data.Gaussian.Basic.Canonical

/-- Gaussian conjugation preserves the original ordered subtraction.

The real-coordinate subtraction is retained and the imaginary-coordinate subtraction is negated, preserving the original
endpoint order. -/
theorem conj_sub (first last : Canonical) : conj (first - last) = conj first - conj last := by
  apply Basic.ext <;> simp only [conj, Basic.sub_re, Basic.sub_im, -eq_self, -iff_self] <;> ring1

end Purelib.Data.Gaussian.Basic.Canonical
