module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Components
public import Purelib.Polynomial.Dense.Gaussian.Path.Pair
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Assembly
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic
import Purelib.Polynomial.Dense.Rational.Pair.Product
import Purelib.RationalFunctions.Path.Polynomial
public import Purelib.RationalFunctions.Winding.Path.Correction
import Purelib.Tactic.Ring
import Purelib.Polynomial.Clearance.Pair.Operations

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Rational.Pair.Path.Basic (PolynomialEdge)

section
@[expose] public section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

namespace Purelib.RationalFunctions.Winding.Line.Quotient

section
open Purelib.Data
open Purelib.Polynomial
open Purelib.RationalFunctions
/-- The doubled quotient winding identity on an oriented affine interval.

It is numerator edge winding minus denominator edge winding, with the signed endpoint correction subtracted at the start
and added at the stop. -/
def LineQuotientFormula
    (numerator denominator : CoefficientPolynomial)
    (origin direction : Canonical) (a b : Rational) : Prop :=
  (Path.Polynomial.quotientEdge numerator denominator origin direction a b).doubledWinding =
    (PolynomialEdge.ofLine numerator origin direction a b).doubledWinding -
      (PolynomialEdge.ofLine denominator origin direction a b).doubledWinding -
      (Winding.Path.Correction.lineQuotientCorrection2 numerator denominator origin direction a : Int) +
      Winding.Path.Correction.lineQuotientCorrection2 numerator denominator origin direction b

/-- Numerator and denominator path clearances imply the quotient winding identity on an increasing interval.

Both certificates concern the displayed real and imaginary coordinate polynomials on the same interval. Conjugating the
denominator reverses its winding and yields the retained endpoint corrections. -/
theorem lineQuotientFormula_of_clearances
    (numerator denominator : CoefficientPolynomial)
    (origin direction : Canonical) {a b : Rational} (less : a < b)
    (numeratorClearance : Clearance.Pair.Basic.Certificate
      (Dense.Gaussian.Path.Components.pathReal numerator origin direction)
      (Dense.Gaussian.Path.Components.pathImag numerator origin direction) ⟨a, b, less.le⟩)
    (denominatorClearance : Clearance.Pair.Basic.Certificate
      (Dense.Gaussian.Path.Components.pathReal denominator origin direction)
      (Dense.Gaussian.Path.Components.pathImag denominator origin direction) ⟨a, b, less.le⟩) :
    LineQuotientFormula numerator denominator origin direction a b := by
  let A := Dense.Gaussian.Path.Components.pathReal numerator origin direction
  let B := Dense.Gaussian.Path.Components.pathImag numerator origin direction
  let C := Dense.Gaussian.Path.Components.pathReal denominator origin direction
  let D := Dense.Gaussian.Path.Components.pathImag denominator origin direction
  let E := Path.Polynomial.quotientPathReal numerator denominator origin direction
  let H := Path.Polynomial.quotientPathImag numerator denominator origin direction
  have formula :=
    Dense.Rational.CauchyIndex.Product.Assembly.auxiliaryProductFormula_of_clearances
      (A := A) (B := B) (C := C) (D := -D) (E := E) (H := H)
      less numeratorClearance denominatorClearance.negSecond
      (by
        intro x
        simp only [A, B, C, D, E, Path.Polynomial.quotientPathReal, Dense.Rational.Pair.Product.eval_productReal,
          Dense.Basic.DensePolynomial.eval_neg, -eq_self, -iff_self]
        rfl)
      (by
        intro x
        simp only [A, B, C, D, H, Path.Polynomial.quotientPathImag,
          Dense.Rational.Pair.Product.eval_productImag, Dense.Basic.DensePolynomial.eval_neg, -eq_self, -iff_self]
        rfl)
  have denominatorStart := denominatorClearance.eval_ne_zero
    (x := a) ⟨le_rfl, less.le⟩
  have denominatorStop := denominatorClearance.eval_ne_zero
    (x := b) ⟨less.le, le_rfl⟩
  have conjugate := Dense.Rational.CauchyIndex.Basic.cauchyIndex2_neg_denominator
    denominatorStart denominatorStop
  unfold Dense.Rational.CauchyIndex.Product.Basic.AuxiliaryProductFormula at formula
  change Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 E H a b =
      Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 A B a b + Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2
        C (-D) a b -
        (Dense.Rational.CauchyIndex.Product.Basic.auxiliaryEndpointCorrection2
          B (-D) H a : Int) +
        Dense.Rational.CauchyIndex.Product.Basic.auxiliaryEndpointCorrection2
          B (-D) H b at formula
  have formulaSub :
      Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 E H a b =
        Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 A B a b -
          Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 C D a b -
          (Dense.Rational.CauchyIndex.Product.Basic.auxiliaryEndpointCorrection2
            B (-D) H a : Int) +
          Dense.Rational.CauchyIndex.Product.Basic.auxiliaryEndpointCorrection2
            B (-D) H b := by
    rw [show Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 C (-D) a b =
      -Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 C D a b by
      simpa only [C, D] using conjugate] at formula
    exact formula.trans (by ring1)
  unfold LineQuotientFormula Path.Polynomial.quotientEdge
    PolynomialEdge.doubledWinding
  dsimp only [PolynomialEdge.ofLine]
  change Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 E H a b = _
  rw [← Winding.Path.Correction.auxiliaryEndpointCorrection2_quotient numerator denominator
      origin direction a,
    ← Winding.Path.Correction.auxiliaryEndpointCorrection2_quotient numerator denominator
      origin direction b]
  simpa only [A, B, C, D, E, H] using formulaSub

end

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- Reversing the interval preserves the quotient formula with reversed winding and swapped endpoint corrections. -/
theorem LineQuotientFormula.reverse
    {numerator denominator : CoefficientPolynomial}
    {origin direction : Canonical} {a b : Rational}
    (formula : LineQuotientFormula numerator denominator origin direction a b) :
    LineQuotientFormula numerator denominator origin direction b a := by
  unfold LineQuotientFormula at formula ⊢
  have quotientReverse := Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse
    (Path.Polynomial.quotientPathReal numerator denominator origin direction)
    (Path.Polynomial.quotientPathImag numerator denominator origin direction) a b
  have numeratorReverse := PolynomialEdge.doubledWinding_reverse
    (PolynomialEdge.ofLine numerator origin direction a b)
  have denominatorReverse := PolynomialEdge.doubledWinding_reverse
    (PolynomialEdge.ofLine denominator origin direction a b)
  change
    (Path.Polynomial.quotientEdge numerator denominator origin direction b a).doubledWinding =
      -(Path.Polynomial.quotientEdge numerator denominator origin direction a b).doubledWinding
      at quotientReverse
  change
    (PolynomialEdge.ofLine numerator origin direction b a).doubledWinding =
      -(PolynomialEdge.ofLine numerator origin direction a b).doubledWinding
      at numeratorReverse
  change
    (PolynomialEdge.ofLine denominator origin direction b a).doubledWinding =
      -(PolynomialEdge.ofLine denominator origin direction a b).doubledWinding
      at denominatorReverse
  rw [quotientReverse, numeratorReverse, denominatorReverse, formula]
  ring1
end Purelib.RationalFunctions.Winding.Line.Quotient

end
