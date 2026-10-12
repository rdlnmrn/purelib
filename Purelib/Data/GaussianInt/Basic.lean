module

import Purelib.Data.Int.Arithmetic
-- Exposed coordinate printers retain the original signed decimal dictionary.
public import Purelib.Data.Int.Decimal
meta import Purelib.Elab.Deriving.Repr

public import Mathlib.Algebra.Ring.MinimalAxioms
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Integral Gaussian coordinates

Gaussian integers retain their original real and imaginary integer coordinates.
Coordinatewise arithmetic supplies the commutative ring, while the distinct
lattice-point carrier keeps its original horizontal and vertical fields.
-/

namespace Purelib.Data

open scoped Purelib.Data.Int.Decimal

@[expose] public section

set_option genInjectivity false in
/-- Retain a Gaussian integer as two exact integral coordinates.

The real and imaginary fields are executable integers; arithmetic uses their
displayed coordinate formulas and equality is decided componentwise. -/
@[ext]
structure GaussianInt where
  /-- The exact integral real coordinate. -/ re : Int
  /-- The exact integral imaginary coordinate. -/ im : Int
deriving DecidableEq

constructive_injectivity GaussianInt

derive_exposed_repr GaussianInt

end

end Purelib.Data

namespace Purelib.Data.GaussianInt.Basic

public section

/-- The original executable Gaussian-integer carrier with its two integral coordinates. -/
abbrev SourceEncodingEncoderGaussianIntAlias := Purelib.Data.GaussianInt

end

end Purelib.Data.GaussianInt.Basic

namespace Purelib.Data.GaussianInt

@[expose] public section

set_option genInjectivity false in
/-- Retain an integer lattice point with explicit horizontal and vertical coordinates.

The x and y fields remain original integral data; coordinatewise embedding supplies
their exact Gaussian-rational realization. -/
structure LatticePoint where
  /-- The exact horizontal integer coordinate. -/ x : Int
  /-- The exact vertical integer coordinate. -/ y : Int

constructive_injectivity LatticePoint

end

end Purelib.Data.GaussianInt

-- Public equality and printing instances for integer lattice points.
namespace Purelib.Topology.Knot.ExactPolynomialLoops

open scoped Purelib.Data.Int.Decimal

@[expose] public section

deriving instance DecidableEq for Purelib.Data.GaussianInt.LatticePoint

derive_exposed_repr Purelib.Data.GaussianInt.LatticePoint

end

end Purelib.Topology.Knot.ExactPolynomialLoops

namespace Purelib.Data.GaussianInt

public section

/-- The zero Gaussian integer has both coordinates zero. -/
instance : Zero GaussianInt := ⟨⟨0, 0⟩⟩

/-- The unit Gaussian integer has real coordinate one and imaginary coordinate zero. -/
instance : One GaussianInt := ⟨⟨1, 0⟩⟩

/-- Add Gaussian integers by adding their corresponding integral coordinates. -/
instance : Add GaussianInt :=
  ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

/-- Subtract Gaussian integers by subtracting their corresponding integral coordinates. -/
instance : Sub GaussianInt :=
  ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩

/-- Negate a Gaussian integer by negating both integral coordinates. -/
instance : Neg GaussianInt := ⟨fun z => ⟨-z.re, -z.im⟩⟩

/-- Multiply Gaussian integers using the displayed complex-coordinate product formula. -/
instance : Mul GaussianInt :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im,
    z.re * w.im + z.im * w.re⟩⟩

/-- The imaginary coordinate of Gaussian-integer sum is its displayed integral formula. -/
@[simp] theorem add_im (z w : GaussianInt) : (z + w).im = z.im + w.im := rfl

/-- The real coordinate of Gaussian-integer sum is its displayed integral formula. -/
@[simp] theorem add_re (z w : GaussianInt) : (z + w).re = z.re + w.re := rfl

/-- The imaginary coordinate of Gaussian-integer product is its displayed integral
formula. -/
@[simp] theorem mul_im (z w : GaussianInt) :
    (z * w).im = z.re * w.im + z.im * w.re := rfl

/-- The real coordinate of Gaussian-integer product is its displayed integral formula. -/
@[simp] theorem mul_re (z w : GaussianInt) :
    (z * w).re = z.re * w.re - z.im * w.im := rfl

/-- The imaginary coordinate of Gaussian-integer negation is its displayed integral
formula. -/
@[simp] theorem neg_im (z : GaussianInt) : (-z).im = -z.im := rfl

/-- The real coordinate of Gaussian-integer negation is its displayed integral formula. -/
@[simp] theorem neg_re (z : GaussianInt) : (-z).re = -z.re := rfl

/-- The imaginary coordinate of Gaussian-integer one is its displayed integral formula. -/
@[simp] theorem one_im : (1 : GaussianInt).im = 0 := rfl

/-- The real coordinate of Gaussian-integer one is its displayed integral formula. -/
@[simp] theorem one_re : (1 : GaussianInt).re = 1 := rfl

/-- The imaginary coordinate of Gaussian-integer difference is its displayed integral
formula. -/
@[simp] theorem sub_im (z w : GaussianInt) : (z - w).im = z.im - w.im := rfl

/-- The real coordinate of Gaussian-integer difference is its displayed integral formula. -/
@[simp] theorem sub_re (z w : GaussianInt) : (z - w).re = z.re - w.re := rfl

/-- The imaginary coordinate of Gaussian-integer zero is its displayed integral formula. -/
@[simp] theorem zero_im : (0 : GaussianInt).im = 0 := rfl

/-- The real coordinate of Gaussian-integer zero is its displayed integral formula. -/
@[simp] theorem zero_re : (0 : GaussianInt).re = 0 := rfl

/-- Gaussian-integer addition is associative.

Each original integral coordinate satisfies associativity separately. The two
scalar equalities reconstruct the original Gaussian record. -/
theorem add_assoc (x y z : GaussianInt) : x + y + z = x + (y + z) := by
  ext <;> simp only [add_re, add_im] <;> ring1

/-- Gaussian-integer multiplication distributes over addition in its right argument.

The displayed real and imaginary product formulas distribute over both
retained coordinate sums independently. -/
theorem left_distrib (x y z : GaussianInt) : x * (y + z) = x * y + x * z := by
  ext <;> simp only [mul_re, mul_im, add_re, add_im] <;> ring1

/-- Gaussian-integer multiplication is associative.

Expanding the original integral coordinate products gives the same real and
imaginary scalars for both parenthesizations. -/
theorem mul_assoc (x y z : GaussianInt) : x * y * z = x * (y * z) := by
  ext <;> simp only [mul_re, mul_im] <;> ring1

/-- Swapping Gaussian-integer factors preserves both product coordinates.

Integer multiplication commutes in each displayed scalar product. The real
difference and imaginary sum retain their original coordinate formulas. -/
theorem mul_comm (z w : GaussianInt) : z * w = w * z := by
  cases z with
  | mk real imaginary =>
      cases w with
      | mk otherReal otherImaginary =>
          apply congrArg₂ GaussianInt.mk
          · change real * otherReal - imaginary * otherImaginary =
              otherReal * real - otherImaginary * imaginary
            rw [Int.Arithmetic.mul_comm real otherReal,
              Int.Arithmetic.mul_comm imaginary otherImaginary]
          · change real * otherImaginary + imaginary * otherReal =
              otherReal * imaginary + otherImaginary * real
            rw [Int.Arithmetic.mul_comm real otherImaginary,
              Int.Arithmetic.mul_comm imaginary otherReal]
            exact Int.Arithmetic.add_comm _ _

/-- Adding a Gaussian integer to its negation cancels both coordinates.

The original coordinatewise negation and addition reduce each integral
coordinate to zero. -/
theorem neg_add_cancel (z : GaussianInt) : -z + z = 0 := by
  cases z with
  | mk real imaginary =>
      change GaussianInt.mk (-real + real) (-imaginary + imaginary) =
        GaussianInt.mk 0 0
      rw [Int.Arithmetic.neg_add_cancel, Int.Arithmetic.neg_add_cancel]

/-- Multiplying a Gaussian integer on the left by one preserves its coordinates. -/
@[simp] theorem one_mul (z : GaussianInt) : 1 * z = z := by
  cases z with
  | mk real imaginary =>
      apply congrArg₂ GaussianInt.mk
      · change 1 * real - 0 * imaginary = real
        rw [Int.one_mul, Int.Arithmetic.zero_mul, Int.Arithmetic.sub_zero]
      · change 1 * imaginary + 0 * real = imaginary
        rw [Int.one_mul, Int.Arithmetic.zero_mul, Int.add_zero]

/-- Adding the zero Gaussian integer preserves both displayed coordinates.

Each integer coordinate satisfies the left-zero law independently. -/
@[simp] theorem zero_add (z : GaussianInt) : 0 + z = z := by
  cases z with
  | mk real imaginary =>
      change GaussianInt.mk (0 + real) (0 + imaginary) =
        GaussianInt.mk real imaginary
      rw [Int.Arithmetic.zero_add, Int.Arithmetic.zero_add]

/-- Adding zero on the right preserves both Gaussian-integer coordinates. -/
@[simp] theorem add_zero (z : GaussianInt) : z + 0 = z := by
  cases z with
  | mk real imaginary =>
      change GaussianInt.mk (real + 0) (imaginary + 0) = GaussianInt.mk real imaginary
      rw [Int.add_zero, Int.add_zero]

/-- Zero and one are distinct Gaussian integers, as witnessed by their real coordinates. -/
instance instNontrivial : Nontrivial GaussianInt where
  exists_pair_ne := ⟨0, 1, by decide⟩

/-- Multiplying by one on the right preserves a Gaussian integer. -/
@[simp] theorem mul_one (z : GaussianInt) : z * 1 = z :=
  (mul_comm z 1).trans (one_mul z)

/-- Multiplying by zero on the right annihilates both displayed coordinates. -/
@[simp] theorem mul_zero (z : GaussianInt) : z * 0 = 0 := by
  cases z with
  | mk real imaginary =>
      change GaussianInt.mk (real * 0 - imaginary * 0) (real * 0 + imaginary * 0) =
        GaussianInt.mk 0 0
      rw [Int.mul_zero, Int.mul_zero, Int.Arithmetic.sub_zero, Int.add_zero]

/-- Embed a displayed natural as a real Gaussian integer with zero imaginary coordinate. -/
@[expose] def ofNat (value : Nat) : GaussianInt := ⟨(value : Int), 0⟩

/-- Gaussian-integer subtraction is coordinatewise addition of the negation. -/
theorem sub_eq_add_neg (z w : GaussianInt) : z - w = z + -w := rfl

/-- Multiplying by zero on the left annihilates both displayed coordinates. -/
@[simp] theorem zero_mul (z : GaussianInt) : 0 * z = 0 := by
  cases z with
  | mk real imaginary =>
      change GaussianInt.mk (0 * real - 0 * imaginary) (0 * imaginary + 0 * real) =
        GaussianInt.mk 0 0
      rw [Int.Arithmetic.zero_mul, Int.Arithmetic.zero_mul,
        Int.Arithmetic.sub_zero, Int.add_zero]

/-- Coordinatewise Gaussian-integer arithmetic forms a commutative ring.

The scalar repetitions, powers, subtraction and casts retain the original
default constructions. The direct coordinate laws supply all ring fields
without deriving them through a minimal-axioms constructor. -/
instance instCommRing : CommRing GaussianInt where
  add := (· + ·)
  mul := (· * ·)
  neg := Neg.neg
  zero := 0
  one := 1
  add_assoc := add_assoc
  add_comm left right := by
    cases left with
    | mk leftReal leftImaginary =>
        cases right with
        | mk rightReal rightImaginary =>
            change GaussianInt.mk (leftReal + rightReal) (leftImaginary + rightImaginary) =
              GaussianInt.mk (rightReal + leftReal) (rightImaginary + leftImaginary)
            rw [Int.Arithmetic.add_comm leftReal rightReal,
              Int.Arithmetic.add_comm leftImaginary rightImaginary]
  zero_add := zero_add
  add_zero := add_zero
  neg_add_cancel := neg_add_cancel
  nsmul := nsmulRec
  zsmul := zsmulRec nsmulRec
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  one_mul := one_mul
  mul_one := mul_one
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := left_distrib
  right_distrib left right factor := by
    rw [mul_comm (left + right), left_distrib,
      mul_comm factor left, mul_comm factor right]

end

end Purelib.Data.GaussianInt
