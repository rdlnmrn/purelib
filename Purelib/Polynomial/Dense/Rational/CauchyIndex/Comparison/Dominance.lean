module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Clearance.Pair.Dominance
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Comparison.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.HalfPlane
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Assembly
import Purelib.Polynomial.Dense.Rational.Pair.ConjugateProduct
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
import Purelib.Polynomial.Clearance.Pair.Product

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Comparison.Dominance

/-- Boundary norm dominance resolves one complete finite Rouché edge. -/
theorem lineData_of_normDominance
    {A B C D U V : Dense.Rational.Basic.CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (proper : root.lower < root.upper)
    (left : Clearance.Pair.Basic.Certificate A B root)
    (margin : Fraction.Rational) (marginPositive : 0 < margin)
    (dominance : ∀ x : Fraction.Rational, root.Contains x →
      margin ≤ A.eval x ^ 2 + B.eval x ^ 2 -
        (C.eval x ^ 2 + D.eval x ^ 2))
    (sumReal : ∀ x : Fraction.Rational,
      U.eval x = A.eval x + C.eval x)
    (sumImag : ∀ x : Fraction.Rational,
      V.eval x = B.eval x + D.eval x) :
    Dense.Rational.CauchyIndex.Comparison.Basic.LineData A B U V root.lower root.upper := by
  let sum := Clearance.Pair.Dominance.sumCertificate_of_normDominance margin marginPositive
    dominance sumReal sumImag
  let E := Dense.Rational.Pair.ConjugateProduct.roucheReal A B U V
  let H := Dense.Rational.Pair.ConjugateProduct.roucheImag A B U V
  have realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * U.eval x - (-B).eval x * V.eval x := by
    intro x
    simp only [E, Dense.Rational.Pair.ConjugateProduct.eval_roucheReal, Dense.Basic.DensePolynomial.eval_neg]
    ring1
  have imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * V.eval x + (-B).eval x * U.eval x := by
    intro x
    simp only [H, Dense.Rational.Pair.ConjugateProduct.eval_roucheImag, Dense.Basic.DensePolynomial.eval_neg]
    ring1
  let conjugateClearance := left.negSecond
  let productClearance : Clearance.Pair.Basic.Certificate E H root :=
    conjugateClearance.complexProduct sum realIdentity imagIdentity
  have realPositive : ∀ x : Fraction.Rational, root.Contains x → 0 < E.eval x := by
    intro x inside
    have dominanceAtX := dominance x inside
    have sumNonnegative : 0 ≤ U.eval x ^ 2 + V.eval x ^ 2 :=
      add_nonneg
        (Fraction.Order.Arithmetic.sq_nonneg_direct (U.eval x))
        (Fraction.Order.Arithmetic.sq_nonneg_direct (V.eval x))
    have doubledIdentity :
        2 * E.eval x =
          (A.eval x ^ 2 + B.eval x ^ 2 -
            (C.eval x ^ 2 + D.eval x ^ 2)) +
              (U.eval x ^ 2 + V.eval x ^ 2) := by
      dsimp only [E]
      rw [Dense.Rational.Pair.ConjugateProduct.eval_roucheReal, sumReal x, sumImag x]
      ring1
    have doubledPositive : 0 < 2 * E.eval x := by
      rw [doubledIdentity]
      calc
        0 < margin := marginPositive
        _ ≤ A.eval x ^ 2 + B.eval x ^ 2 -
              (C.eval x ^ 2 + D.eval x ^ 2) := dominanceAtX
        _ ≤ (A.eval x ^ 2 + B.eval x ^ 2 -
              (C.eval x ^ 2 + D.eval x ^ 2)) +
                (U.eval x ^ 2 + V.eval x ^ 2) :=
          le_add_of_nonneg_right sumNonnegative
    apply lt_of_not_ge
    intro nonpositive
    have doubledNonpositive :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        nonpositive (show (0 : Fraction.Rational) ≤ 2 by decide)
    have atMostZero : 2 * E.eval x ≤ 0 := by
      calc
        2 * E.eval x ≤ 2 * 0 := doubledNonpositive
        _ = 0 := Fraction.Field.mul_zero_direct 2
    exact (not_lt_of_ge atMostZero) doubledPositive
  exact
    { halfPlane := Dense.Rational.CauchyIndex.HalfPlane.formula_of_positive_real
        productClearance proper realPositive
      product := Dense.Rational.CauchyIndex.Product.Assembly.auxiliaryProductFormula_of_clearances proper
        conjugateClearance sum realIdentity imagIdentity }
end Purelib.Polynomial.Dense.Rational.CauchyIndex.Comparison.Dominance

end
