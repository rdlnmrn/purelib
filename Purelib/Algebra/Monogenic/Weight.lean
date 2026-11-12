module

public import Purelib.Algebra.Monogenic.Algebra
public import Purelib.LinearAlgebra.Matrix.Weight
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Squared weights on the original cyclic coefficient algebra

The original algebra element keeps its structural matrix unchanged. Summing
the original scalar entry weights gives the next finite ring weight, with
an explicit multiplier determined by the original cyclic dimension.
-/

public section

namespace Purelib.Algebra.Monogenic.Cyclic.Element

open Purelib.Algebra.Ring (Weight)
open Purelib.Algebra.FiniteSum.Fin
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix
open Purelib.Data.Rat.Fraction

variable {K : Type*} [CommRing K] {dimension : Nat} {generator : SquareMatrix K dimension}

/-- Lift an original scalar weight to the same original cyclic matrix algebra.

The value is the total of all retained matrix entry weights. Its product
multiplier is the original coefficient multiplier times the explicit
squared-sum factor at the same original dimension.
-/
@[expose] def weight (cyclic : Cyclic generator) (parent : Ring.Weight K) : Ring.Weight (Element cyclic) where
  value value := SquareMatrix.Weight.total parent value.matrix
  nonnegative value := SquareMatrix.Weight.total_nonnegative parent value.matrix
  zero := SquareMatrix.Weight.total_zero parent
  neg value := by
    apply sumFin_congr
    intro row
    apply sumFin_congr
    intro column
    rewrite [neg_matrix, Arithmetic.scale_apply]
    have entry : (-1 : K) * value.matrix row column = -value.matrix row column := by ring0
    rewrite [entry, parent.neg]
    rfl
  add_le left right := SquareMatrix.Weight.total_add_le parent left.matrix right.matrix
  multiplier := (2 : Rational) ^ dimension * parent.multiplier
  one_le_multiplier := by
    have powerBound := Order.Arithmetic.pow_le_pow_direct
      (by decide : (0 : Rational) ≤ 1) (by decide : (1 : Rational) ≤ 2) dimension
    rewrite [one_pow] at powerBound
    have productBound := Order.Arithmetic.mul_le_mul_direct powerBound parent.one_le_multiplier
      (by decide : (0 : Rational) ≤ 1)
      (Order.Arithmetic.pow_nonneg_direct (by decide : (0 : Rational) ≤ 2) dimension)
    rewrite [_root_.one_mul] at productBound
    exact productBound
  mul_le left right := SquareMatrix.Weight.total_mul_le parent left.matrix right.matrix

end Purelib.Algebra.Monogenic.Cyclic.Element

end
