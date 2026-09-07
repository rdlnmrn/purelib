import mathlib.Tactic.QuotientFreeRing
import RFAP.Winding.Homotopy

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

namespace RFAP.RationalWinding

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev CoordinatePolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Box := RFAP.Boxes.Box
abbrev BoundaryClearance := RFAP.BoxClearance.BoundaryClearance

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.PathPolynomial
open RFAP.PathClearance
open RFAP.Sturm
open RFAP.Winding

/-- Real numerator coordinate of a quotient on one affine parameter line. -/
def quotientPathReal
    (numerator denominator : GaussianPolynomial)
    (origin direction : Gaussian) : CoordinatePolynomial :=
  productReal
    (pathReal numerator origin direction)
    (pathImag numerator origin direction)
    (pathReal denominator origin direction)
    (-(pathImag denominator origin direction))

/-- Imaginary numerator coordinate of a quotient on one affine parameter
line. -/
def quotientPathImag
    (numerator denominator : GaussianPolynomial)
    (origin direction : Gaussian) : CoordinatePolynomial :=
  productImag
    (pathReal numerator origin direction)
    (pathImag numerator origin direction)
    (pathReal denominator origin direction)
    (-(pathImag denominator origin direction))

@[simp] theorem eval_quotientPathReal
    (numerator denominator : GaussianPolynomial)
    (origin direction : Gaussian) (t : Coordinate) :
    (quotientPathReal numerator denominator origin direction).eval t =
      (numerator.eval (line origin direction t)).re *
          (denominator.eval (line origin direction t)).re +
        (numerator.eval (line origin direction t)).im *
          (denominator.eval (line origin direction t)).im := by
  simp only [quotientPathReal, eval_productReal, eval_neg, eval_pathReal,
    eval_pathImag]
  ring1

@[simp] theorem eval_quotientPathImag
    (numerator denominator : GaussianPolynomial)
    (origin direction : Gaussian) (t : Coordinate) :
    (quotientPathImag numerator denominator origin direction).eval t =
      (numerator.eval (line origin direction t)).im *
          (denominator.eval (line origin direction t)).re -
        (numerator.eval (line origin direction t)).re *
          (denominator.eval (line origin direction t)).im := by
  simp only [quotientPathImag, eval_productImag, eval_neg, eval_pathReal,
    eval_pathImag]
  ring1

/-- One oriented rational-function edge, represented without division. -/
def quotientEdge
    (numerator denominator : GaussianPolynomial)
    (origin direction : Gaussian) (start stop : Coordinate) : PolynomialEdge :=
  { realPart := quotientPathReal numerator denominator origin direction
    imagPart := quotientPathImag numerator denominator origin direction
    start := start
    stop := stop }

/-- Four positively oriented quotient edges of a rational box. -/
def quotientBoundary
    (numerator denominator : GaussianPolynomial) (box : Box) :
    List PolynomialEdge :=
  [quotientEdge numerator denominator
      (horizontalBase box.yLower) horizontalDirection
      box.xLower box.xUpper,
    quotientEdge numerator denominator
      (verticalBase box.xUpper) verticalDirection
      box.yLower box.yUpper,
    quotientEdge numerator denominator
      (horizontalBase box.yUpper) horizontalDirection
      box.xUpper box.xLower,
    quotientEdge numerator denominator
      (verticalBase box.xLower) verticalDirection
      box.yUpper box.yLower]

/-- Quadrupled constructive winding of a displayed rational function. -/
def rationalQuadrupledWinding
    (numerator denominator : GaussianPolynomial) (box : Box) : Int :=
  ((quotientBoundary numerator denominator box).map
    PolynomialEdge.doubledWinding).sum

/-- Ordinary rational-function box winding after the repository's raw
quadrupled normalization. -/
def rationalBoxWinding
    (numerator denominator : GaussianPolynomial) (box : Box) : Int :=
  rationalQuadrupledWinding numerator denominator box / 4

theorem rationalBoxWinding_eq_of_quadrupled_eq_four_mul
    {numerator denominator : GaussianPolynomial} {box : Box} {value : Int}
    (raw : rationalQuadrupledWinding numerator denominator box = 4 * value) :
    rationalBoxWinding numerator denominator box = value := by
  rw [rationalBoxWinding, raw]
  exact Int.mul_ediv_cancel_left value (by decide)

theorem rationalQuadrupledWinding_eq
    (numerator denominator : GaussianPolynomial) (box : Box) :
    rationalQuadrupledWinding numerator denominator box =
      (quotientEdge numerator denominator
        (horizontalBase box.yLower) horizontalDirection
        box.xLower box.xUpper).doubledWinding +
      (quotientEdge numerator denominator
        (verticalBase box.xUpper) verticalDirection
        box.yLower box.yUpper).doubledWinding +
      (quotientEdge numerator denominator
        (horizontalBase box.yUpper) horizontalDirection
        box.xUpper box.xLower).doubledWinding +
      (quotientEdge numerator denominator
        (verticalBase box.xLower) verticalDirection
        box.yUpper box.yLower).doubledWinding := by
  simp only [rationalQuadrupledWinding, quotientBoundary, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  ring1

/-- Endpoint correction in the product formula, written at the displayed
Gaussian-rational boundary vertex so the four box corrections telescope. -/
def vertexQuotientCorrection2
    (numerator denominator : GaussianPolynomial) (z : Gaussian) : Nat :=
  let numeratorValue := numerator.eval z
  let denominatorValue := denominator.eval z
  signJump 1
    ((numeratorValue.im * denominatorValue.re -
        numeratorValue.re * denominatorValue.im) *
      (numeratorValue.im * (-denominatorValue.im)))

def lineQuotientCorrection2
    (numerator denominator : GaussianPolynomial)
    (origin direction : Gaussian) (t : Coordinate) : Nat :=
  vertexQuotientCorrection2 numerator denominator
    (line origin direction t)

theorem auxiliaryEndpointCorrection2_quotient
    (numerator denominator : GaussianPolynomial)
    (origin direction : Gaussian) (t : Coordinate) :
    RFAP.CauchyProduct.auxiliaryEndpointCorrection2
        (pathImag numerator origin direction)
        (-(pathImag denominator origin direction))
        (quotientPathImag numerator denominator origin direction) t =
      lineQuotientCorrection2 numerator denominator origin direction t := by
  unfold RFAP.CauchyProduct.auxiliaryEndpointCorrection2
    lineQuotientCorrection2 vertexQuotientCorrection2
  simp only [eval_quotientPathImag, eval_pathImag, eval_neg]

/-- The finite quotient identity on one oriented affine interval. -/
def LineQuotientFormula
    (numerator denominator : GaussianPolynomial)
    (origin direction : Gaussian) (a b : Coordinate) : Prop :=
  (quotientEdge numerator denominator origin direction a b).doubledWinding =
    (PolynomialEdge.ofLine numerator origin direction a b).doubledWinding -
      (PolynomialEdge.ofLine denominator origin direction a b).doubledWinding -
      (lineQuotientCorrection2 numerator denominator origin direction a : Int) +
      lineQuotientCorrection2 numerator denominator origin direction b

/-- Two explicit path clearances prove the quotient formula on an increasing
affine parameter interval. -/
theorem lineQuotientFormula_of_clearances
    (numerator denominator : GaussianPolynomial)
    (origin direction : Gaussian) {a b : Coordinate} (less : a < b)
    (numeratorClearance : RFAP.PathClearance.Certificate
      (pathReal numerator origin direction)
      (pathImag numerator origin direction) ⟨a, b, less.le⟩)
    (denominatorClearance : RFAP.PathClearance.Certificate
      (pathReal denominator origin direction)
      (pathImag denominator origin direction) ⟨a, b, less.le⟩) :
    LineQuotientFormula numerator denominator origin direction a b := by
  let A := pathReal numerator origin direction
  let B := pathImag numerator origin direction
  let C := pathReal denominator origin direction
  let D := pathImag denominator origin direction
  let E := quotientPathReal numerator denominator origin direction
  let H := quotientPathImag numerator denominator origin direction
  have formula :=
    RFAP.WindingHomotopy.auxiliaryProductFormula_of_clearances
      (A := A) (B := B) (C := C) (D := -D) (E := E) (H := H)
      less numeratorClearance denominatorClearance.negSecond
      (by
        intro x
        simp only [A, B, C, D, E, quotientPathReal, eval_productReal,
          eval_neg])
      (by
        intro x
        simp only [A, B, C, D, H, quotientPathImag,
          eval_productImag, eval_neg])
  have denominatorStart := denominatorClearance.eval_ne_zero
    (x := a) ⟨le_rfl, less.le⟩
  have denominatorStop := denominatorClearance.eval_ne_zero
    (x := b) ⟨less.le, le_rfl⟩
  have conjugate := cauchyIndex2_neg_denominator
    denominatorStart denominatorStop
  unfold RFAP.CauchyProduct.AuxiliaryProductFormula at formula
  change cauchyIndex2 E H a b =
      cauchyIndex2 A B a b + cauchyIndex2 C (-D) a b -
        (RFAP.CauchyProduct.auxiliaryEndpointCorrection2
          B (-D) H a : Int) +
        RFAP.CauchyProduct.auxiliaryEndpointCorrection2
          B (-D) H b at formula
  have formulaSub :
      cauchyIndex2 E H a b =
        cauchyIndex2 A B a b - cauchyIndex2 C D a b -
          (RFAP.CauchyProduct.auxiliaryEndpointCorrection2
            B (-D) H a : Int) +
          RFAP.CauchyProduct.auxiliaryEndpointCorrection2
            B (-D) H b := by
    rw [show cauchyIndex2 C (-D) a b = -cauchyIndex2 C D a b by
      simpa only [C, D] using conjugate] at formula
    exact formula.trans (by ring1)
  unfold LineQuotientFormula quotientEdge PolynomialEdge.doubledWinding
  dsimp only [PolynomialEdge.ofLine]
  change cauchyIndex2 E H a b = _
  rw [← auxiliaryEndpointCorrection2_quotient numerator denominator
      origin direction a,
    ← auxiliaryEndpointCorrection2_quotient numerator denominator
      origin direction b]
  simpa only [A, B, C, D, E, H] using formulaSub

/-- Reversing an interval reverses its quotient formula. -/
theorem LineQuotientFormula.reverse
    {numerator denominator : GaussianPolynomial}
    {origin direction : Gaussian} {a b : Coordinate}
    (formula : LineQuotientFormula numerator denominator origin direction a b) :
    LineQuotientFormula numerator denominator origin direction b a := by
  unfold LineQuotientFormula at formula ⊢
  have quotientReverse := cauchyIndex2_reverse
    (quotientPathReal numerator denominator origin direction)
    (quotientPathImag numerator denominator origin direction) a b
  have numeratorReverse := PolynomialEdge.doubledWinding_reverse
    (PolynomialEdge.ofLine numerator origin direction a b)
  have denominatorReverse := PolynomialEdge.doubledWinding_reverse
    (PolynomialEdge.ofLine denominator origin direction a b)
  change
    (quotientEdge numerator denominator origin direction b a).doubledWinding =
      -(quotientEdge numerator denominator origin direction a b).doubledWinding
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

/-- Four quotient formulas in positive box-boundary orientation. -/
structure BoxQuotientFormula
    (numerator denominator : GaussianPolynomial) (box : Box) : Prop where
  bottom : LineQuotientFormula numerator denominator
    (horizontalBase box.yLower) horizontalDirection
    box.xLower box.xUpper
  right : LineQuotientFormula numerator denominator
    (verticalBase box.xUpper) verticalDirection
    box.yLower box.yUpper
  top : LineQuotientFormula numerator denominator
    (horizontalBase box.yUpper) horizontalDirection
    box.xUpper box.xLower
  left : LineQuotientFormula numerator denominator
    (verticalBase box.xLower) verticalDirection
    box.yUpper box.yLower

/-- Polynomial boundary clearances supply every finite quotient edge
identity; top and left are obtained by exact interval reversal. -/
theorem boxQuotientFormula_of_boundaryClearances
    (numerator denominator : GaussianPolynomial) (box : Box)
    (proper : box.Proper)
    (numeratorClearance : BoundaryClearance numerator box)
    (denominatorClearance : BoundaryClearance denominator box) :
    BoxQuotientFormula numerator denominator box := by
  have bottom := lineQuotientFormula_of_clearances numerator denominator
    (horizontalBase box.yLower) horizontalDirection proper.1
    (RFAP.BoxClearance.bottomOfBoundary
      numeratorClearance).toPathCertificate
    (RFAP.BoxClearance.bottomOfBoundary
      denominatorClearance).toPathCertificate
  have right := lineQuotientFormula_of_clearances numerator denominator
    (verticalBase box.xUpper) verticalDirection proper.2
    (RFAP.BoxClearance.rightOfBoundary
      numeratorClearance).toPathCertificate
    (RFAP.BoxClearance.rightOfBoundary
      denominatorClearance).toPathCertificate
  have topIncreasing := lineQuotientFormula_of_clearances
    numerator denominator (horizontalBase box.yUpper) horizontalDirection
    proper.1
    (RFAP.BoxClearance.topOfBoundary
      numeratorClearance).toPathCertificate
    (RFAP.BoxClearance.topOfBoundary
      denominatorClearance).toPathCertificate
  have leftIncreasing := lineQuotientFormula_of_clearances
    numerator denominator (verticalBase box.xLower) verticalDirection
    proper.2
    (RFAP.BoxClearance.leftOfBoundary
      numeratorClearance).toPathCertificate
    (RFAP.BoxClearance.leftOfBoundary
      denominatorClearance).toPathCertificate
  exact
    { bottom := bottom
      right := right
      top := topIncreasing.reverse
      left := leftIncreasing.reverse }

/-- Constructive rational-function argument principle on one clear rational
box: quotient winding is numerator winding minus denominator winding. -/
theorem rationalQuadrupledWinding_eq_sub_of_boundaryClearances
    (numerator denominator : GaussianPolynomial) (box : Box)
    (proper : box.Proper)
    (numeratorClearance : BoundaryClearance numerator box)
    (denominatorClearance : BoundaryClearance denominator box) :
    rationalQuadrupledWinding numerator denominator box =
      quadrupledBoxWinding numerator box -
        quadrupledBoxWinding denominator box := by
  let formula := boxQuotientFormula_of_boundaryClearances
    numerator denominator box proper numeratorClearance denominatorClearance
  have bottom := formula.bottom
  have right := formula.right
  have top := formula.top
  have left := formula.left
  unfold LineQuotientFormula lineQuotientCorrection2 at bottom right top left
  simp only [line_horizontal] at bottom top
  simp only [line_vertical] at right left
  rw [rationalQuadrupledWinding_eq, quadrupledBoxWinding_eq,
    quadrupledBoxWinding_eq]
  simp only [horizontalEdge, verticalEdge]
  rw [bottom, right, top, left]
  ring1

end RFAP.RationalWinding
