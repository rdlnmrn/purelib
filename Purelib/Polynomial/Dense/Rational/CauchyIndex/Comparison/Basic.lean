module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Sign.CauchyComparison
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.HalfPlane
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic
public import Purelib.Polynomial.Dense.Rational.Pair.ConjugateProduct
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Assembly
import Purelib.Polynomial.Clearance.Pair.Product
import Purelib.Tactic.Ring

open Purelib.Data.Rat

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

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Comparison.Basic

open Purelib.Polynomial.Dense.Rational.Pair

/-- The two finite formulas attached to one oriented Rouché edge. -/
structure LineData
    (A B U V : Dense.Rational.Basic.CoordinatePolynomial) (a b : Fraction.Rational) : Prop where
  /-- The endpoint-jump identity for the real and imaginary coordinates of the conjugate product. -/ halfPlane :
    Dense.Rational.CauchyIndex.HalfPlane.Formula
    (ConjugateProduct.roucheReal A B U V) (ConjugateProduct.roucheImag A B U V)
      a b
  /-- The auxiliary product formula relating the conjugated first pair, second pair and their displayed product
    coordinates. -/ product : Dense.Rational.CauchyIndex.Product.Basic.AuxiliaryProductFormula A (-B) U V
    (ConjugateProduct.roucheReal A B U V) (ConjugateProduct.roucheImag A B U V)
      a b

/-- A positive conjugate dot product gives the original complete comparison formulas.

Both actual coordinate-pair margins are retained. The conjugate product
uses the existing dense tables and original auxiliary-product procedure;
its positive real coordinate supplies the original half-plane formula.
-/
theorem LineData.of_positiveDot
    {A B U V : Dense.Rational.Basic.CoordinatePolynomial} {root : Purelib.Data.Rat.Interval.Bounds}
    (source : Purelib.Polynomial.Clearance.Pair.Basic.Certificate A B root)
    (target : Purelib.Polynomial.Clearance.Pair.Basic.Certificate U V root)
    (proper : root.lower < root.upper)
    (positive : ∀ point : Fraction.Rational, root.Contains point →
      0 < A.eval point * U.eval point + B.eval point * V.eval point) :
    LineData A B U V root.lower root.upper := by
  let E := ConjugateProduct.roucheReal A B U V
  let H := ConjugateProduct.roucheImag A B U V
  have realIdentity (point : Fraction.Rational) :
      E.eval point = A.eval point * U.eval point - (-B).eval point * V.eval point := by
    rw [ConjugateProduct.eval_roucheReal, Dense.Basic.DensePolynomial.eval_neg]
    ring1
  have imagIdentity (point : Fraction.Rational) :
      H.eval point = A.eval point * V.eval point + (-B).eval point * U.eval point := by
    rw [ConjugateProduct.eval_roucheImag, Dense.Basic.DensePolynomial.eval_neg]
    ring1
  let productClearance := source.negSecond.complexProduct target realIdentity imagIdentity
  refine ⟨HalfPlane.formula_of_positive_real productClearance proper ?_,
    Product.Assembly.auxiliaryProductFormula_of_clearances proper source.negSecond target
      realIdentity imagIdentity⟩
  intro point inside
  change 0 < E.eval point
  rw [ConjugateProduct.eval_roucheReal]
  exact positive point inside

/-- Reverse both finite formulas while preserving their exact polynomial coordinate pairs. -/
theorem LineData.reverse
    {A B U V : Dense.Rational.Basic.CoordinatePolynomial} {a b : Fraction.Rational}
    (data : LineData A B U V a b) :
      LineData A B U V b a where
  halfPlane := data.halfPlane.reverse
  product := data.product.reverse

/-- A retained comparison changes the index only by its two endpoint corrections.

The source coordinate pair is nonzero at both displayed endpoints. The same
original conjugate-product and half-plane formulas then give the target index
with the uncancelled signed correction at each endpoint.
-/
theorem LineData.index_eq
    {A B U V : Dense.Rational.Basic.CoordinatePolynomial} {a b : Fraction.Rational}
    (data : LineData A B U V a b)
    (sourceAtA : A.eval a ≠ 0 ∨ B.eval a ≠ 0)
    (sourceAtB : A.eval b ≠ 0 ∨ B.eval b ≠ 0) :
    Basic.Sturm.cauchyIndex2 U V a b = Basic.Sturm.cauchyIndex2 A B a b +
      Purelib.Data.Gaussian.Sign.CauchyComparison.vertexHomotopyCorrection2
        ⟨A.eval a, B.eval a⟩ ⟨U.eval a, V.eval a⟩ -
      Purelib.Data.Gaussian.Sign.CauchyComparison.vertexHomotopyCorrection2
        ⟨A.eval b, B.eval b⟩ ⟨U.eval b, V.eval b⟩ := by
  have conjugate := Basic.cauchyIndex2_neg_denominator sourceAtA sourceAtB
  have half := data.halfPlane
  have product := data.product
  unfold HalfPlane.Formula at half
  unfold Product.Basic.AuxiliaryProductFormula Product.Basic.auxiliaryEndpointCorrection2 at product
  simp only [ConjugateProduct.eval_roucheReal,
    ConjugateProduct.eval_roucheImag, Dense.Basic.DensePolynomial.eval_neg] at half product
  rw [conjugate] at product
  unfold Purelib.Data.Gaussian.Sign.CauchyComparison.vertexHomotopyCorrection2
  dsimp only
  calc
    Basic.Sturm.cauchyIndex2 U V a b = Basic.Sturm.cauchyIndex2 A B a b +
        Basic.Sturm.cauchyIndex2 (ConjugateProduct.roucheReal A B U V)
          (ConjugateProduct.roucheImag A B U V) a b +
        (Purelib.Data.Rat.Sign.Jump.signJump 1
          ((A.eval a * V.eval a - B.eval a * U.eval a) * (-B.eval a * V.eval a)) : Int) -
        Purelib.Data.Rat.Sign.Jump.signJump 1
          ((A.eval b * V.eval b - B.eval b * U.eval b) * (-B.eval b * V.eval b)) := by
      rw [product]
      ring1
    _ = _ := by rw [half]; ring1
end Purelib.Polynomial.Dense.Rational.CauchyIndex.Comparison.Basic

end
