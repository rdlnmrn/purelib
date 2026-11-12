module

import Purelib.Data.Fin
import Purelib.Polynomial.Dense.Companion.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Companion.Arithmetic.Bounds
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
meta import Purelib.Polynomial.Dense.Companion.Arithmetic
meta import Purelib.Polynomial.Dense.Gaussian.Companion.Arithmetic.Bounds
meta import Purelib.LinearAlgebra.Matrix.Basic
meta import Purelib.Data.Vector.Basic
meta import Purelib.Data.Gaussian.Basic
meta import Purelib.Data.Gaussian.Field

/-!
# Original polynomial arithmetic and retained companion caches

A nonmonic cubic with an original leading-zero prefix and an independent
linear source construct their sum/product polynomials. Cancellation and a
zero factor use different original inputs. Universal residual coverage retains
all original readings, including nonroots, rather than calling them exact roots.
-/

namespace TestPurelib.Polynomial.CompanionArithmetic

open Purelib
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Companion
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

/-- The original nonmonic cubic 2Z³-16 with a representation-only leading zero. -/
private def cubic : DensePolynomial Canonical := ⟨[0, 2, 0, 0, -16]⟩

/-- The independent original linear source Z-3. -/
private def linear : DensePolynomial Canonical := ⟨[1, -3]⟩

example (point : Canonical) : cubic.eval point =
    cubic.leadingCoeff * point ^ cubic.natDegree +
      Algebra.FiniteSum.Fin.sumFin (fun index : Fin cubic.natDegree =>
        Data.List.getD (Companion.ofPositive cubic (by decide +kernel)).coefficients index.val 0 * point ^ index.val) :=
  (Companion.ofPositive cubic (by decide +kernel)).source_evaluation point

example (operation : Operation)
    (elimination : Elimination operation (Companion.ofPositive cubic (by decide +kernel))
      (Companion.ofPositive linear (by decide +kernel))) :
    elimination.polynomial.eval (operation.value 2 3) = 0 :=
  elimination.source_zero 2 3 (by decide +kernel) (by decide +kernel)

example (operation : Operation)
    (elimination : Elimination operation (Companion.ofPositive cubic (by decide +kernel))
      (Companion.ofPositive linear (by decide +kernel))) (firstPoint secondPoint : Canonical)
    (row : Fin (cubic.natDegree * linear.natDegree)) :
    operation.value firstPoint secondPoint *
        SquareMatrix.Tensor.vector (elimination.first.powers firstPoint) (elimination.second.powers secondPoint) row -
        SquareMatrix.Multiplication.matrixVector elimination.matrix
          (SquareMatrix.Tensor.vector (elimination.first.powers firstPoint)
            (elimination.second.powers secondPoint)) row =
      operation.residual firstPoint secondPoint
        (elimination.first.powers firstPoint (Data.Fin.divNat row))
        (elimination.second.powers secondPoint (Data.Fin.modNat row))
        (elimination.first.residual firstPoint (Data.Fin.divNat row))
        (elimination.second.residual secondPoint (Data.Fin.modNat row)) :=
  elimination.source_residual firstPoint secondPoint row

/-- Execute source-owned cubic arithmetic, cancellation and zero-factor evidence through their actual caches. -/
private def checkArithmetic : IO Unit := do
  let first := Companion.ofPositive cubic (by decide +kernel)
  let second := Companion.ofPositive linear (by decide +kernel)
  unless first.coefficients = [-16, 0, 0] ∧ first.feedback first.firstIndex = 8 do
    throw (IO.userError "original nonmonic cubic coefficient cache or leading normalization was changed")
  let added := Elimination.ofCompanions .add first second
  let multiplied := Elimination.ofCompanions .mul first second
  unless added.polynomial.isZero = false ∧ added.polynomial.natDegree = 3 ∧
      added.polynomial.eval 5 = 0 ∧ added.polynomial.eval 0 ≠ 0 ∧
      multiplied.polynomial.isZero = false ∧ multiplied.polynomial.natDegree = 3 ∧
      multiplied.polynomial.eval 6 = 0 do
    throw (IO.userError "computed cubic sum/product polynomial lost its original source roots or finite degree")
  let addedBounds := Gaussian.Companion.Arithmetic.Bounds.prepare added 9 16
    (by decide +kernel) (by decide +kernel)
  let multipliedBounds := Gaussian.Companion.Arithmetic.Bounds.prepare multiplied 9 16
    (by decide +kernel) (by decide +kernel)
  unless Data.Gaussian.Norm.Basic.normSq (added.polynomial.eval 3) ≤
      addedBounds.polynomialBudget 1 2 do
    throw (IO.userError "computed sum budget did not bound the actual nonroot source readings")
  unless Data.Gaussian.Norm.Basic.normSq (multiplied.polynomial.eval 2) ≤
      multipliedBounds.polynomialBudget 1 2 do
    throw (IO.userError "computed product budget did not bound the actual nonroot source readings")
  unless addedBounds.first.powerBound > 0 ∧ multipliedBounds.second.powerBound > 0 ∧
      addedBounds.multiplier ≥ 0 ∧ multipliedBounds.multiplier ≥ 0 do
    throw (IO.userError "computed power or inverse-row multiplier lost its nonnegative certificate")
  let quadratic : DensePolynomial Canonical := ⟨[1, 0, -4]⟩
  let negative : DensePolynomial Canonical := ⟨[1, 2]⟩
  let left := Companion.ofPositive quadratic (by decide +kernel)
  let right := Companion.ofPositive negative (by decide +kernel)
  let cancelled := Elimination.ofCompanions .add left right
  unless cancelled.polynomial.isZero = false ∧ cancelled.polynomial.eval 0 = 0 do
    throw (IO.userError "exact cancellation incorrectly produced the zero coefficient polynomial")
  let withZero : DensePolynomial Canonical := ⟨[1, -2, 0]⟩
  let zeroFactor := Companion.ofPositive withZero (by decide +kernel)
  let zeroProduct := Elimination.ofCompanions .mul zeroFactor second
  unless zeroProduct.polynomial.isZero = false ∧ zeroProduct.polynomial.eval 0 = 0 do
    throw (IO.userError "zero factor incorrectly invalidated the computed nonzero annihilating polynomial")
  let positions := List.ofFn (fun index : Fin (2 * 3) => index)
  for position in positions do
    unless Fin.mkDivMod (Data.Fin.divNat position) (Data.Fin.modNat position) = position do
      throw (IO.userError "finite product indexing failed original-bound reconstruction")

#eval checkArithmetic

end TestPurelib.Polynomial.CompanionArithmetic
