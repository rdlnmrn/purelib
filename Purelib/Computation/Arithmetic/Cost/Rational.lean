module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.BitWidth

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Computation.Arithmetic.Cost.Basic
public import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Algebra.Group.Nat.Defs

section
@[expose] public section

/-! Rational arithmetic and normalization work charges. -/

namespace Purelib.Computation.Arithmetic.Cost.Rational

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Computation.Arithmetic.Cost.Basic
open Purelib.Computation.Arithmetic.Cost

/-- A cubic width charge for normalizing a displayed rational value. -/
def normalizationCharge (value : Fraction.Rational) : Nat :=
  (BitWidth.rationalWidth value + 1) ^ 3

/-- Charge a rational operation using its displayed inputs and output.

Arithmetic work is quadratic in their combined binary widths. Normalization is charged separately from the output width;
this function itself imposes no relation between the three values. -/
def rationalOperationWork (left right output : Fraction.Rational) :
  Work :=
  { core :=
      (BitWidth.rationalWidth left + BitWidth.rationalWidth right + BitWidth.rationalWidth output + 1) ^ 2
    normalization := Rational.normalizationCharge output }

/-- Charge rational addition using the actual normalized sum. -/
def rationalAddWork (left right : Fraction.Rational) : Work :=
  Rational.rationalOperationWork left right (left + right)

/-- Charge rational subtraction using the actual normalized difference. -/
def rationalSubWork (left right : Fraction.Rational) : Work :=
  Rational.rationalOperationWork left right (left - right)

/-- Charge rational multiplication using the actual normalized product. -/
def rationalMulWork (left right : Fraction.Rational) : Work :=
  Rational.rationalOperationWork left right (left * right)

/-- Charge a rational comparison by the combined operand widths plus one. -/
def rationalEqualityCost (left right : Fraction.Rational) : Nat :=
  BitWidth.rationalWidth left + BitWidth.rationalWidth right + 1
end Purelib.Computation.Arithmetic.Cost.Rational

end
