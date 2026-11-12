module

public import Purelib.LinearAlgebra.Matrix.Multiplication
public import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.LCM
public import Purelib.Data.Gaussian.Fraction.NaturalDenominator
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.GetD
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.LinearAlgebra.Vector.Dot
import Purelib.Tactic.Ring

/-! Exact Gaussian matrix actions with integer accumulation and shared column clearing. -/

namespace Purelib.LinearAlgebra.Matrix.Multiplication.Gaussian

open Data (GaussianInt)
open Data.Gaussian.Basic (Canonical)
open Data.Rat.Fraction (Rational)
open Data.Gaussian.Fraction.NaturalDenominator
open Data.Vector.Basic (vectorOfFn vectorOfFn_apply vector_ext)
open Data.List
open Data.GaussianInt
open Data.Gaussian.Basic.Canonical.Fraction (NaturalDenominator)
open Polynomial.Dense.Gaussian.Denominator.Clearing
open Algebra.FiniteSum.Fin
open LinearAlgebra.Vector
open LinearAlgebra renaming Matrix -> SquareMatrix

/-- Materialize the original cleared coefficient list as a structural integer vector. -/
private def integerVector {count : Nat} (cleared : Basic.ClearedCoefficients) :
    Data.Vector GaussianInt count :=
  vectorOfFn fun index => getD cleared.coefficients index.val 0

/-- Each cleared integer entry embeds as its original entry times the common scale. -/
private theorem integerVector_readback {count : Nat} (values : Data.Vector Canonical count)
    (index : Fin count) :
    let cleared := LCM.lcmClear (List.ofFn fun index => values index)
    toGaussian (integerVector cleared index) =
      ⟨(cleared.scale : Rational), 0⟩ * values index := by
  let entries := List.ofFn fun index => values index
  dsimp only
  unfold integerVector
  rewrite [vectorOfFn_apply]
  change toGaussian
    (getD (entries.map (ScaledNumerator.scaledGaussianCoefficient
      (LCM.lcmScale entries))) index.val 0) = _
  rewrite [OfFn.Basic.map_ofFn, OfFn.Basic.getD_ofFn]
  have divides := LCM.lcmScale_clears entries (values index) (OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩)
  exact ScaledNumerator.toGaussian_scaledGaussianCoefficient
    (LCM.lcmScale entries) (values index) divides.1 divides.2

/-- Read one integer dot product at the product of its two retained positive scales. -/
private def rowValue {count : Nat} (leftScale rightScale : Nat)
    (leftPositive : 0 < leftScale) (rightPositive : 0 < rightScale)
    (left right : Data.Vector GaussianInt count) : Canonical :=
  NaturalDenominator.value
    ⟨Dot.dot left right, leftScale * rightScale, Nat.mul_pos leftPositive rightPositive⟩

/-- Clearing both original vectors preserves their entire exact dot product. -/
private theorem rowValue_eq {count : Nat} (left right : Data.Vector Canonical count) :
    let first := LCM.lcmClear (List.ofFn fun index => left index)
    let second := LCM.lcmClear (List.ofFn fun index => right index)
    rowValue (count := count) first.scale second.scale first.scalePositive second.scalePositive
        (integerVector first) (integerVector second) = Dot.dot left right := by
  let first := LCM.lcmClear (List.ofFn fun index => left index)
  let second := LCM.lcmClear (List.ofFn fun index => right index)
  let fraction : NaturalDenominator :=
    ⟨Dot.dot (integerVector (count := count) first) (integerVector second), first.scale * second.scale,
      Nat.mul_pos first.scalePositive second.scalePositive⟩
  have nonzero : toGaussian (ofNat fraction.denominator) ≠ 0 := by
    intro zero
    have realZero := congrArg Data.Gaussian.Basic.re zero
    rewrite [toGaussian_ofNat] at realZero
    exact fraction.denominatorCast_ne realZero
  apply Data.Gaussian.Field.mul_right_cancel_of_ne nonzero
  change fraction.value * toGaussian (ofNat fraction.denominator) =
    Dot.dot left right * toGaussian (ofNat fraction.denominator)
  rewrite [NaturalDenominator.value_mul_denominator]
  change toGaussian (sumFin fun index => integerVector first index * integerVector second index) = _
  rewrite [map_sumFin toGaussian toGaussian_zero toGaussian_add]
  calc
    _ = sumFin (fun index =>
        (⟨(first.scale : Rational), 0⟩ * left index) *
          (⟨(second.scale : Rational), 0⟩ * right index)) := by
      apply sumFin_congr
      intro index
      rewrite [toGaussian_mul, integerVector_readback left index, integerVector_readback right index]
      rfl
    _ = sumFin (fun index =>
        (left index * right index) * toGaussian (ofNat fraction.denominator)) := by
      apply sumFin_congr
      intro index
      rewrite [toGaussian_ofNat]
      change _ = (left index * right index) *
        ⟨((first.scale * second.scale : Nat) : Rational), 0⟩
      rewrite [Algebra.NatCast.mul]
      have scales :
          (⟨(first.scale : Rational), 0⟩ : Canonical) *
              ⟨(second.scale : Rational), 0⟩ =
            ⟨(first.scale : Rational) * second.scale, 0⟩ := by
        apply Data.Gaussian.Basic.ext
        · change _ * _ - 0 * 0 = _
          ring1
        · change _ * 0 + 0 * _ = 0
          ring1
      rewrite [← scales]
      ring1
    _ = _ := sumFin_mul_right _ _

public section

/-- Multiply a Gaussian matrix by its original column using exact integer dot products.

The column's least common denominator and integer entries are retained outside
the row callback. Each matrix row is cleared once, and only its final two
coordinates are normalized as rational values. All output rows are retained.
-/
@[expose] def matrixVector {count : Nat} (matrix : SquareMatrix Canonical count)
    (values : Data.Vector Canonical count) : Data.Vector Canonical count :=
  let asVector (cleared : Basic.ClearedCoefficients) : Data.Vector GaussianInt count :=
    vectorOfFn fun index => getD cleared.coefficients index.val 0
  let column := LCM.lcmClear (List.ofFn fun index => values index)
  let columnIntegers := asVector column
  vectorOfFn fun row =>
    let cleared := LCM.lcmClear (List.ofFn fun index => matrix row index)
    NaturalDenominator.value
      ⟨Dot.dot (asVector cleared) columnIntegers, cleared.scale * column.scale,
        Nat.mul_pos cleared.scalePositive column.scalePositive⟩

/-- Integer accumulation preserves the complete original Gaussian matrix-vector product. -/
theorem matrixVector_eq {count : Nat} (matrix : SquareMatrix Canonical count)
    (values : Data.Vector Canonical count) :
    matrixVector matrix values = Multiplication.matrixVector matrix values := by
  apply vector_ext
  intro row
  unfold matrixVector Multiplication.matrixVector
  rewrite [vectorOfFn_apply, vectorOfFn_apply]
  exact rowValue_eq (matrix row) values

end

end Purelib.LinearAlgebra.Matrix.Multiplication.Gaussian
