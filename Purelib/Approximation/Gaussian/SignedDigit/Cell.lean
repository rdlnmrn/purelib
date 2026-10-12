module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.SignedDigit.Binary.Basic
public import Purelib.Data.SignedDigit.Binary.Encoding
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Rational

open Purelib.Data.Rat

open Purelib.Data.SignedDigit

open Purelib.Data.SignedDigit.Binary

section
public section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

namespace Purelib.Approximation.Gaussian.SignedDigit

set_option genInjectivity false in
/-- One complex signed-digit cell with a shared scale and depth. -/
structure Cell where
  /-- The common rational scale of the two signed-digit coordinates. -/ scale : Fraction.Rational
  /-- The retained common scale is strictly positive. -/ scale_pos : 0 < scale
  /-- The retained shared digit depth. -/ depth : Nat
  /-- The retained finite signed-digit word for the real coordinate. -/ realDigits : List Binary.Basic.Digit
  /-- The retained finite signed-digit word for the imaginary coordinate. -/ imagDigits : List Binary.Basic.Digit
  /-- The real digit word has exactly the retained depth. -/ real_length : realDigits.length = depth
  /-- The imaginary digit word has exactly the retained depth. -/ imag_length : imagDigits.length = depth

constructive_injectivity Cell

namespace Cell

/-- The half-power corresponding to the retained digit depth. -/
@[expose] def factor (cell : Cell) : Fraction.Rational :=
  (1 / 2 : Fraction.Rational) ^ cell.depth

/-- The remaining coordinate radius given by the common scale times the depth factor. -/
@[expose] def tail (cell : Cell) : Fraction.Rational := cell.scale * cell.factor

/-- The remaining signed-digit coordinate radius is nonnegative. -/
theorem tail_nonneg (cell : Cell) : 0 ≤ cell.tail :=
  Fraction.Order.Arithmetic.mul_nonneg_direct cell.scale_pos.le
    (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) cell.depth)

/-- Read the Gaussian rational centre from the two retained signed-digit prefixes and common scale. -/
@[expose] def center (cell : Cell) : Data.Gaussian.Basic.Canonical :=
  ⟨cell.scale * Binary.Basic.prefixValue cell.realDigits,
    cell.scale * Binary.Basic.prefixValue cell.imagDigits⟩

/-- A reading lies in both closed coordinate intervals around the retained centre. -/
@[expose] def Contains (cell : Cell) (value : Data.Gaussian.Basic.Canonical) :
  Prop :=
  cell.center.re - cell.tail ≤ value.re ∧
    value.re ≤ cell.center.re + cell.tail ∧
    cell.center.im - cell.tail ≤ value.im ∧
    value.im ≤ cell.center.im + cell.tail

/-- Every signed-digit cell contains its own displayed centre. -/
theorem contains_center (cell : Cell) : cell.Contains cell.center :=
  ⟨(Fraction.Order.Arithmetic.sub_le_sub_left_direct cell.tail_nonneg _).trans_eq (by ring1),
    le_add_of_nonneg_right cell.tail_nonneg,
    (Fraction.Order.Arithmetic.sub_le_sub_left_direct cell.tail_nonneg _).trans_eq (by ring1),
    le_add_of_nonneg_right cell.tail_nonneg⟩

/-- Every reading admitted by the inner signed-digit cell is admitted by the outer cell. -/
@[expose] def Refines (inner outer : Cell) : Prop :=
  ∀ {value : Data.Gaussian.Basic.Canonical}, inner.Contains value → outer.Contains value

/-- Every signed-digit cell refines itself. -/
theorem refines_refl (cell : Cell) : cell.Refines cell :=
  fun inside => inside

/-- Compose two successive signed-digit cell refinements. -/
theorem refines_trans {inner middle outer : Cell}
    (innerMiddle : inner.Refines middle)
    (middleOuter : middle.Refines outer) : inner.Refines outer :=
  fun inside => middleOuter (innerMiddle inside)

/-- The scale-two squared-radius allowance at the retained signed-digit depth. -/
@[expose] def precisionSq (cell : Cell) : Fraction.Rational :=
  Geometric.Basic.quarterRadius (2 * cell.scale ^ 2) cell.depth

/-- The signed-digit squared-precision allowance is nonnegative. -/
theorem precisionSq_nonneg (cell : Cell) : 0 ≤ cell.precisionSq :=
  Geometric.Basic.quarterRadius_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.sq_nonneg_direct cell.scale)) cell.depth

end Cell

namespace Cell

/-- Encode one displayed Gaussian rational in a shared signed-digit square. -/
@[expose] def ofPoint (value : Data.Gaussian.Basic.Canonical) (scale : Fraction.Rational)
    (scalePositive : 0 < scale)
    (bounds : -scale ≤ value.re ∧ value.re ≤ scale ∧
      -scale ≤ value.im ∧ value.im ≤ scale)
    (depth : Nat) : Cell :=
  let realEncoding := Binary.Encoding.encode (value.re / scale)
    (Binary.Encoding.normalized_bounded scalePositive ⟨bounds.1, bounds.2.1⟩) depth
  let imagEncoding := Binary.Encoding.encode (value.im / scale)
    (Binary.Encoding.normalized_bounded scalePositive ⟨bounds.2.2.1, bounds.2.2.2⟩) depth
  { scale := scale
    scale_pos := scalePositive
    depth := depth
    realDigits := realEncoding.digits
    imagDigits := imagEncoding.digits
    real_length := realEncoding.length_eq
    imag_length := imagEncoding.length_eq }

/-- The finite signed-digit cell computed from a bounded point contains that original point. -/
theorem ofPoint_contains (value : Data.Gaussian.Basic.Canonical) (scale : Fraction.Rational)
    (scalePositive : 0 < scale)
    (bounds : -scale ≤ value.re ∧ value.re ≤ scale ∧
      -scale ≤ value.im ∧ value.im ≤ scale)
    (depth : Nat) :
    (ofPoint value scale scalePositive bounds depth).Contains value := by
  let realEncoding := Binary.Encoding.encode (value.re / scale)
    (Binary.Encoding.normalized_bounded scalePositive ⟨bounds.1, bounds.2.1⟩) depth
  let imagEncoding := Binary.Encoding.encode (value.im / scale)
    (Binary.Encoding.normalized_bounded scalePositive ⟨bounds.2.2.1, bounds.2.2.2⟩) depth
  have realInside := realEncoding.contains_value
  have imagInside := imagEncoding.contains_value
  have realLower :=
    (Fraction.Order.Field.le_div_iff_pos scalePositive).1 realInside.1
  have realUpper :=
    (Fraction.Order.Field.div_le_iff_pos scalePositive).1 realInside.2
  have imagLower :=
    (Fraction.Order.Field.le_div_iff_pos scalePositive).1 imagInside.1
  have imagUpper :=
    (Fraction.Order.Field.div_le_iff_pos scalePositive).1 imagInside.2
  change
    scale * Binary.Basic.prefixValue realEncoding.digits -
          scale * (1 / 2 : Fraction.Rational) ^ depth ≤ value.re ∧
      value.re ≤ scale * Binary.Basic.prefixValue realEncoding.digits +
          scale * (1 / 2 : Fraction.Rational) ^ depth ∧
      scale * Binary.Basic.prefixValue imagEncoding.digits -
          scale * (1 / 2 : Fraction.Rational) ^ depth ≤ value.im ∧
      value.im ≤ scale * Binary.Basic.prefixValue imagEncoding.digits +
          scale * (1 / 2 : Fraction.Rational) ^ depth
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      scale * Binary.Basic.prefixValue realEncoding.digits -
          scale * (1 / 2 : Fraction.Rational) ^ depth =
        (Binary.Basic.prefixValue realEncoding.digits -
          (1 / 2 : Fraction.Rational) ^ depth) * scale := by ring1
      _ ≤ value.re := realLower
  · calc
      value.re ≤ (Binary.Basic.prefixValue realEncoding.digits +
          (1 / 2 : Fraction.Rational) ^ depth) * scale := realUpper
      _ = scale * Binary.Basic.prefixValue realEncoding.digits +
          scale * (1 / 2 : Fraction.Rational) ^ depth := by ring1
  · calc
      scale * Binary.Basic.prefixValue imagEncoding.digits -
          scale * (1 / 2 : Fraction.Rational) ^ depth =
        (Binary.Basic.prefixValue imagEncoding.digits -
          (1 / 2 : Fraction.Rational) ^ depth) * scale := by ring1
      _ ≤ value.im := imagLower
  · calc
      value.im ≤ (Binary.Basic.prefixValue imagEncoding.digits +
          (1 / 2 : Fraction.Rational) ^ depth) * scale := imagUpper
      _ = scale * Binary.Basic.prefixValue imagEncoding.digits +
          scale * (1 / 2 : Fraction.Rational) ^ depth := by ring1

end Cell

end Purelib.Approximation.Gaussian.SignedDigit

end
