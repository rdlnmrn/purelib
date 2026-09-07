import FTA.CauchyProduct

/-!
# Finite product certificates for algebraic winding

For two polynomial paths `A+iB` and `C+iD`, the product has coordinates
`AC-BD` and `AD+BC`.  Eisermann's auxiliary product formula says that the
doubled Cauchy index of the product is the sum of the two factor indices,
up to the endpoint variation of `(AD+BC)/(BD)`.

This module makes that identity a decidable finite certificate for every
rational polynomial edge, consumes proof-relevant finite event partitions,
and exposes the safe-cut partition builder on affine Gaussian-polynomial
edges.  It proves that endpoint corrections cancel around the four edges of a
closed rational box.  The completed coefficient-computed success depth now
constructs all four edge partitions and proves multiplicativity directly on
the nondegenerate coordinate branch.  A finite exhaustive split closes every
identically-zero factor or product coordinate row, so the direct affine-edge
and closed-box theorems now use exactly the paper's endpoint and vertex
nonvanishing hypotheses.  Modulo-two endpoint cancellation also proves the
closed raw sum even from vertex nonvanishing alone, removing the former
caller-supplied parity premise from the doubled winding product law; no
unproved assumption is introduced here.
-/

namespace FTA.WindingProduct

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.PathPolynomial
open FTA.Sturm
open FTA.Winding
open FTA.CauchyProduct

/-- The doubled two-entry endpoint variation in the auxiliary product
formula.  Multiplication by `BD` records the sign of `(AD+BC)/(BD)` whenever
the denominator is nonzero; zero records Eisermann's pole convention. -/
def vertexProductCorrection2
    (p q : GaussianPolynomial) (z : QI) : ℕ :=
  let pz := p.eval z
  let qz := q.eval z
  signJump 1 ((pz * qz).im * pz.im * qz.im)

/-- The same endpoint correction along the affine line `u+t*d`. -/
def lineProductCorrection2
    (p q : GaussianPolynomial) (u d : QI) (t : ℚ) : ℕ :=
  vertexProductCorrection2 p q (line u d t)

/-- The generic auxiliary endpoint variation specializes exactly to the
Gaussian-rational vertex correction on an affine polynomial path. -/
theorem auxiliaryEndpointCorrection2_ofLine
    (p q : GaussianPolynomial) (u d : QI) (a b t : ℚ) :
    auxiliaryEndpointCorrection2
        (PolynomialEdge.ofLine p u d a b).realPart
        (PolynomialEdge.ofLine p u d a b).imagPart
        (PolynomialEdge.ofLine q u d a b).realPart
        (PolynomialEdge.ofLine q u d a b).imagPart t =
      lineProductCorrection2 p q u d t := by
  rw [auxiliaryEndpointCorrection2,
    endpointFractionVariation2_eq_signJump]
  simp only [eval_productDenominator, eval_mul,
    PolynomialEdge.ofLine_real_eval, PolynomialEdge.ofLine_imag_eval]
  dsimp only [lineProductCorrection2, vertexProductCorrection2]
  apply congrArg (signJump 1)
  simp only [GaussianRat.mul_im]
  ring

/-- A fully executable certificate for the doubled auxiliary product formula
on one oriented affine edge. -/
def lineProductFormulaCheck
    (p q : GaussianPolynomial) (u d : QI) (a b : ℚ) : Bool :=
  auxiliaryProductFormulaCheck
    (PolynomialEdge.ofLine p u d a b).realPart
    (PolynomialEdge.ofLine p u d a b).imagPart
    (PolynomialEdge.ofLine q u d a b).realPart
    (PolynomialEdge.ofLine q u d a b).imagPart a b

/-- Soundness of the finite edge-product certificate. -/
theorem lineProductFormula_of_check
    (p q : GaussianPolynomial) (u d : QI) (a b : ℚ)
    (hcheck : lineProductFormulaCheck p q u d a b = true) :
    (PolynomialEdge.ofLine (p * q) u d a b).doubledWinding =
      (PolynomialEdge.ofLine p u d a b).doubledWinding +
      (PolynomialEdge.ofLine q u d a b).doubledWinding -
        (lineProductCorrection2 p q u d a : ℤ) +
        lineProductCorrection2 p q u d b := by
  have hauxiliary := auxiliaryProductFormula_of_check
    (PolynomialEdge.ofLine p u d a b).realPart
    (PolynomialEdge.ofLine p u d a b).imagPart
    (PolynomialEdge.ofLine q u d a b).realPart
    (PolynomialEdge.ofLine q u d a b).imagPart a b hcheck
  rw [AuxiliaryProductFormula] at hauxiliary
  rw [auxiliaryEndpointCorrection2_ofLine p q u d a b a,
    auxiliaryEndpointCorrection2_ofLine p q u d a b b] at hauxiliary
  rw [PolynomialEdge.doubledWinding,
    PolynomialEdge.ofLine_mul_real_eq p q u d a b,
    PolynomialEdge.ofLine_mul_imag_eq p q u d a b]
  simpa [PolynomialEdge.product, productNumerator, productDenominator,
    FTA.PathPolynomial.productReal, FTA.PathPolynomial.productImag,
    PolynomialEdge.doubledWinding, PolynomialEdge.ofLine] using hauxiliary

/-- A finite simultaneous-event partition specialized to one affine
Gaussian-polynomial edge. -/
def LineProductPartition
    (p q : GaussianPolynomial) (u d : QI) (a b : ℚ) : Type :=
  AuxiliaryProductPartition
    (PolynomialEdge.ofLine p u d a b).realPart
    (PolynomialEdge.ofLine p u d a b).imagPart
    (PolynomialEdge.ofLine q u d a b).realPart
    (PolynomialEdge.ofLine q u d a b).imagPart a b

/-- A proved finite event partition supplies the edge product identity
without evaluating the whole-formula Boolean checker. -/
theorem lineProductFormula_of_partition
    (p q : GaussianPolynomial) (u d : QI) (a b : ℚ)
    (partition : LineProductPartition p q u d a b) :
    (PolynomialEdge.ofLine (p * q) u d a b).doubledWinding =
      (PolynomialEdge.ofLine p u d a b).doubledWinding +
      (PolynomialEdge.ofLine q u d a b).doubledWinding -
        (lineProductCorrection2 p q u d a : ℤ) +
        lineProductCorrection2 p q u d b := by
  change AuxiliaryProductPartition
    (PolynomialEdge.ofLine p u d a b).realPart
    (PolynomialEdge.ofLine p u d a b).imagPart
    (PolynomialEdge.ofLine q u d a b).realPart
    (PolynomialEdge.ofLine q u d a b).imagPart a b at partition
  have hauxiliary := partition.auxiliaryProductFormula
  rw [AuxiliaryProductFormula] at hauxiliary
  rw [auxiliaryEndpointCorrection2_ofLine p q u d a b a,
    auxiliaryEndpointCorrection2_ofLine p q u d a b b] at hauxiliary
  rw [PolynomialEdge.doubledWinding,
    PolynomialEdge.ofLine_mul_real_eq p q u d a b,
    PolynomialEdge.ofLine_mul_imag_eq p q u d a b]
  simpa [LineProductPartition, PolynomialEdge.product, productNumerator,
    productDenominator, FTA.PathPolynomial.productReal,
    FTA.PathPolynomial.productImag, PolynomialEdge.doubledWinding,
    PolynomialEdge.ofLine] using hauxiliary

/-- A nonzero Gaussian value is exactly a nonzero pair of the two extracted
rational coordinate evaluations. -/
theorem ofLine_coordinatePair_ne_zero
    (p : GaussianPolynomial) (u d : QI) (a b t : ℚ)
    (hvalue : p.eval (line u d t) ≠ 0) :
    (PolynomialEdge.ofLine p u d a b).realPart.eval t ≠ 0 ∨
      (PolynomialEdge.ofLine p u d a b).imagPart.eval t ≠ 0 := by
  by_contra hpair
  rw [not_or, not_ne_iff, not_ne_iff] at hpair
  apply hvalue
  ext
  · simpa only [PolynomialEdge.ofLine_real_eval, GaussianRat.zero_re] using
      hpair.1
  · simpa only [PolynomialEdge.ofLine_imag_eval, GaussianRat.zero_im] using
      hpair.2

/-- One affine edge has the same parity as the difference of the two flags
recording whether its imaginary coordinate vanishes at a nonzero endpoint.
This remains valid when either whole coordinate polynomial is identically
zero. -/
theorem ofLine_doubledWinding_sub_imaginaryZeroFlags_even
    (p : GaussianPolynomial) (u d : QI) (a b : ℚ)
    (hpA : p.eval (line u d a) ≠ 0)
    (hpB : p.eval (line u d b) ≠ 0) :
    Even ((PolynomialEdge.ofLine p u d a b).doubledWinding -
      ((if (p.eval (line u d a)).im = 0 then 1 else 0) -
        (if (p.eval (line u d b)).im = 0 then 1 else 0))) := by
  have h := cauchyIndex2_sub_endpointFlags_even
    (ofLine_coordinatePair_ne_zero p u d a b a hpA)
    (ofLine_coordinatePair_ne_zero p u d a b b hpB)
  rw [PolynomialEdge.ofLine_imag_eval p u d a b a,
    PolynomialEdge.ofLine_imag_eval p u d a b b] at h
  change Even (cauchyIndex2 (PolynomialEdge.ofLine p u d a b).realPart
      (PolynomialEdge.ofLine p u d a b).imagPart a b - _)
  exact h

/-- The affine-edge product formula under exactly the endpoint hypotheses.
All finite coordinate-degeneracy rows and the nondegenerate recursive
partition construction are discharged internally. -/
theorem lineProductFormula_of_endpoint_nonzero
    (p q : GaussianPolynomial) (u d : QI) (a b : ℚ)
    (hpA : p.eval (line u d a) ≠ 0)
    (hqA : q.eval (line u d a) ≠ 0)
    (hpB : p.eval (line u d b) ≠ 0)
    (hqB : q.eval (line u d b) ≠ 0)
    (hab : a ≠ b) :
    (PolynomialEdge.ofLine (p * q) u d a b).doubledWinding =
      (PolynomialEdge.ofLine p u d a b).doubledWinding +
      (PolynomialEdge.ofLine q u d a b).doubledWinding -
        (lineProductCorrection2 p q u d a : ℤ) +
        lineProductCorrection2 p q u d b := by
  let A := (PolynomialEdge.ofLine p u d a b).realPart
  let B := (PolynomialEdge.ofLine p u d a b).imagPart
  let C := (PolynomialEdge.ofLine q u d a b).realPart
  let D := (PolynomialEdge.ofLine q u d a b).imagPart
  have hauxiliary : AuxiliaryProductFormula A B C D a b :=
    auxiliaryProductFormula_of_endpoint_nonzero_of_ne
      (ofLine_coordinatePair_ne_zero p u d a b a hpA)
      (ofLine_coordinatePair_ne_zero q u d a b a hqA)
      (ofLine_coordinatePair_ne_zero p u d a b b hpB)
      (ofLine_coordinatePair_ne_zero q u d a b b hqB) hab
  rw [AuxiliaryProductFormula] at hauxiliary
  rw [auxiliaryEndpointCorrection2_ofLine p q u d a b a,
    auxiliaryEndpointCorrection2_ofLine p q u d a b b] at hauxiliary
  rw [PolynomialEdge.doubledWinding,
    PolynomialEdge.ofLine_mul_real_eq p q u d a b,
    PolynomialEdge.ofLine_mul_imag_eq p q u d a b]
  simpa [A, B, C, D, PolynomialEdge.product, productNumerator,
    productDenominator, FTA.PathPolynomial.productReal,
    FTA.PathPolynomial.productImag, PolynomialEdge.doubledWinding,
    PolynomialEdge.ofLine] using hauxiliary

/-- The six decidable polynomial nondegeneracy facts used by the specialized
nondegenerate-coordinate API on one affine edge.  The general direct theorem
above no longer asks a caller for these facts. -/
structure LineProductCoordinateNondegenerate
    (p q : GaussianPolynomial) (u d : QI) (a b : ℚ) : Prop where
  leftReal : (PolynomialEdge.ofLine p u d a b).realPart.isZero = false
  leftImag : (PolynomialEdge.ofLine p u d a b).imagPart.isZero = false
  rightReal : (PolynomialEdge.ofLine q u d a b).realPart.isZero = false
  rightImag : (PolynomialEdge.ofLine q u d a b).imagPart.isZero = false
  productReal : (productNumerator
    (PolynomialEdge.ofLine p u d a b).realPart
    (PolynomialEdge.ofLine p u d a b).imagPart
    (PolynomialEdge.ofLine q u d a b).realPart
    (PolynomialEdge.ofLine q u d a b).imagPart).isZero = false
  productImag : (productDenominator
    (PolynomialEdge.ofLine p u d a b).realPart
    (PolynomialEdge.ofLine p u d a b).imagPart
    (PolynomialEdge.ofLine q u d a b).realPart
    (PolynomialEdge.ofLine q u d a b).imagPart).isZero = false

/-- The completed coefficient-width construction proves the affine edge
product identity directly, without a caller-supplied partition or resolution
program. -/
theorem lineProductFormula_of_nondegenerate_coordinates
    (p q : GaussianPolynomial) (u d : QI) (a b : ℚ)
    (coordinates : LineProductCoordinateNondegenerate p q u d a b)
    (hpA : p.eval (line u d a) ≠ 0)
    (hqA : q.eval (line u d a) ≠ 0)
    (hpB : p.eval (line u d b) ≠ 0)
    (hqB : q.eval (line u d b) ≠ 0)
    (hab : a ≠ b) :
    (PolynomialEdge.ofLine (p * q) u d a b).doubledWinding =
      (PolynomialEdge.ofLine p u d a b).doubledWinding +
      (PolynomialEdge.ofLine q u d a b).doubledWinding -
        (lineProductCorrection2 p q u d a : ℤ) +
        lineProductCorrection2 p q u d b := by
  let A := (PolynomialEdge.ofLine p u d a b).realPart
  let B := (PolynomialEdge.ofLine p u d a b).imagPart
  let C := (PolynomialEdge.ofLine q u d a b).realPart
  let D := (PolynomialEdge.ofLine q u d a b).imagPart
  have hauxiliary : AuxiliaryProductFormula A B C D a b :=
    auxiliaryProductFormula_of_nonzero_coordinates_of_ne
      coordinates.leftReal coordinates.leftImag
      coordinates.rightReal coordinates.rightImag
      coordinates.productReal coordinates.productImag
      (ofLine_coordinatePair_ne_zero p u d a b a hpA)
      (ofLine_coordinatePair_ne_zero q u d a b a hqA)
      (ofLine_coordinatePair_ne_zero p u d a b b hpB)
      (ofLine_coordinatePair_ne_zero q u d a b b hqB) hab
  rw [AuxiliaryProductFormula] at hauxiliary
  rw [auxiliaryEndpointCorrection2_ofLine p q u d a b a,
    auxiliaryEndpointCorrection2_ofLine p q u d a b b] at hauxiliary
  rw [PolynomialEdge.doubledWinding,
    PolynomialEdge.ofLine_mul_real_eq p q u d a b,
    PolynomialEdge.ofLine_mul_imag_eq p q u d a b]
  simpa [A, B, C, D, PolynomialEdge.product, productNumerator,
    productDenominator, FTA.PathPolynomial.productReal,
    FTA.PathPolynomial.productImag, PolynomialEdge.doubledWinding,
    PolynomialEdge.ofLine] using hauxiliary

/-- Executable safe-cut partition builder specialized to one affine
Gaussian-polynomial edge. -/
def buildLineProductPartition?
    (p q : GaussianPolynomial) (u d : QI) (fuel : ℕ) (a b : ℚ) :
    Option (LineProductPartition p q u d a b) :=
  buildAuxiliaryProductPartition?
    (PolynomialEdge.ofLine p u d a b).realPart
    (PolynomialEdge.ofLine p u d a b).imagPart
    (PolynomialEdge.ofLine q u d a b).realPart
    (PolynomialEdge.ofLine q u d a b).imagPart fuel a b

/-- Every returned affine-edge partition proves the edge product formula. -/
theorem buildLineProductPartition?_some_formula
    (p q : GaussianPolynomial) (u d : QI) (fuel : ℕ) (a b : ℚ)
    {partition : LineProductPartition p q u d a b}
    (_hbuild : buildLineProductPartition? p q u d fuel a b = some partition) :
    (PolynomialEdge.ofLine (p * q) u d a b).doubledWinding =
      (PolynomialEdge.ofLine p u d a b).doubledWinding +
      (PolynomialEdge.ofLine q u d a b).doubledWinding -
        (lineProductCorrection2 p q u d a : ℤ) +
        lineProductCorrection2 p q u d b :=
  lineProductFormula_of_partition p q u d a b partition

/-- Specialized executable check for a horizontal edge. -/
def horizontalProductFormulaCheck
    (p q : GaussianPolynomial) (y a b : ℚ) : Bool :=
  lineProductFormulaCheck p q (horizontalBase y) horizontalDirection a b

/-- Sound horizontal edge-product identity. -/
theorem horizontalProductFormula_of_check
    (p q : GaussianPolynomial) (y a b : ℚ)
    (hcheck : horizontalProductFormulaCheck p q y a b = true) :
    (horizontalEdge (p * q) y a b).doubledWinding =
      (horizontalEdge p y a b).doubledWinding +
        (horizontalEdge q y a b).doubledWinding -
        (vertexProductCorrection2 p q (CCL.GaussianRat.mk a y) : ℤ) +
        vertexProductCorrection2 p q (CCL.GaussianRat.mk b y) := by
  have h := lineProductFormula_of_check p q
    (horizontalBase y) horizontalDirection a b hcheck
  simpa only [horizontalProductFormulaCheck, horizontalEdge,
    lineProductCorrection2, line_horizontal] using h

/-- Finite product-event partition on a horizontal edge. -/
def HorizontalProductPartition
    (p q : GaussianPolynomial) (y a b : ℚ) : Type :=
  LineProductPartition p q (horizontalBase y) horizontalDirection a b

theorem horizontalProductFormula_of_partition
    (p q : GaussianPolynomial) (y a b : ℚ)
    (partition : HorizontalProductPartition p q y a b) :
    (horizontalEdge (p * q) y a b).doubledWinding =
      (horizontalEdge p y a b).doubledWinding +
        (horizontalEdge q y a b).doubledWinding -
        (vertexProductCorrection2 p q (CCL.GaussianRat.mk a y) : ℤ) +
        vertexProductCorrection2 p q (CCL.GaussianRat.mk b y) := by
  change LineProductPartition p q
    (horizontalBase y) horizontalDirection a b at partition
  have h := lineProductFormula_of_partition p q
    (horizontalBase y) horizontalDirection a b partition
  simpa only [horizontalEdge, lineProductCorrection2, line_horizontal] using h

/-- Specialized executable check for a vertical edge. -/
def verticalProductFormulaCheck
    (p q : GaussianPolynomial) (x a b : ℚ) : Bool :=
  lineProductFormulaCheck p q (verticalBase x) verticalDirection a b

/-- Sound vertical edge-product identity. -/
theorem verticalProductFormula_of_check
    (p q : GaussianPolynomial) (x a b : ℚ)
    (hcheck : verticalProductFormulaCheck p q x a b = true) :
    (verticalEdge (p * q) x a b).doubledWinding =
      (verticalEdge p x a b).doubledWinding +
        (verticalEdge q x a b).doubledWinding -
        (vertexProductCorrection2 p q (CCL.GaussianRat.mk x a) : ℤ) +
        vertexProductCorrection2 p q (CCL.GaussianRat.mk x b) := by
  have h := lineProductFormula_of_check p q
    (verticalBase x) verticalDirection a b hcheck
  simpa only [verticalProductFormulaCheck, verticalEdge,
    lineProductCorrection2, line_vertical] using h

/-- Finite product-event partition on a vertical edge. -/
def VerticalProductPartition
    (p q : GaussianPolynomial) (x a b : ℚ) : Type :=
  LineProductPartition p q (verticalBase x) verticalDirection a b

theorem verticalProductFormula_of_partition
    (p q : GaussianPolynomial) (x a b : ℚ)
    (partition : VerticalProductPartition p q x a b) :
    (verticalEdge (p * q) x a b).doubledWinding =
      (verticalEdge p x a b).doubledWinding +
        (verticalEdge q x a b).doubledWinding -
        (vertexProductCorrection2 p q (CCL.GaussianRat.mk x a) : ℤ) +
        vertexProductCorrection2 p q (CCL.GaussianRat.mk x b) := by
  change LineProductPartition p q
    (verticalBase x) verticalDirection a b at partition
  have h := lineProductFormula_of_partition p q
    (verticalBase x) verticalDirection a b partition
  simpa only [verticalEdge, lineProductCorrection2, line_vertical] using h

/-- The paper's vertex hypothesis for one Gaussian polynomial on a rational
box, recorded as four exact nonzero evaluations. -/
structure BoxVertexNonzero
    (p : GaussianPolynomial) (B : CCL.RatBox) : Prop where
  lowerLeft : p.eval (CCL.GaussianRat.mk B.xLower B.yLower) ≠ 0
  lowerRight : p.eval (CCL.GaussianRat.mk B.xUpper B.yLower) ≠ 0
  upperRight : p.eval (CCL.GaussianRat.mk B.xUpper B.yUpper) ≠ 0
  upperLeft : p.eval (CCL.GaussianRat.mk B.xLower B.yUpper) ≠ 0

/-- Vertex nonvanishing is closed under exact Gaussian-polynomial
multiplication. -/
theorem BoxVertexNonzero.mul
    {p q : GaussianPolynomial} {B : CCL.RatBox}
    (hp : BoxVertexNonzero p B) (hq : BoxVertexNonzero q B) :
    BoxVertexNonzero (p * q) B := by
  constructor
  · simpa only [eval_mul] using mul_ne_zero hp.lowerLeft hq.lowerLeft
  · simpa only [eval_mul] using mul_ne_zero hp.lowerRight hq.lowerRight
  · simpa only [eval_mul] using mul_ne_zero hp.upperRight hq.upperRight
  · simpa only [eval_mul] using mul_ne_zero hp.upperLeft hq.upperLeft

/-- A closed polynomial box path with nonzero vertex values has an even raw
doubled-index sum.  Each edge differs evenly from its two endpoint
denominator-zero flags, and the four vertex flags telescope cyclically. -/
theorem quadrupledBoxWinding_even_of_vertices
    (p : GaussianPolynomial) (B : CCL.RatBox)
    (hp : BoxVertexNonzero p B) :
    Even (quadrupledBoxWinding p B) := by
  have hbottom := ofLine_doubledWinding_sub_imaginaryZeroFlags_even p
    (horizontalBase B.yLower) horizontalDirection B.xLower B.xUpper
    (by simpa only [line_horizontal] using hp.lowerLeft)
    (by simpa only [line_horizontal] using hp.lowerRight)
  have hright := ofLine_doubledWinding_sub_imaginaryZeroFlags_even p
    (verticalBase B.xUpper) verticalDirection B.yLower B.yUpper
    (by simpa only [line_vertical] using hp.lowerRight)
    (by simpa only [line_vertical] using hp.upperRight)
  have htop := ofLine_doubledWinding_sub_imaginaryZeroFlags_even p
    (horizontalBase B.yUpper) horizontalDirection B.xUpper B.xLower
    (by simpa only [line_horizontal] using hp.upperRight)
    (by simpa only [line_horizontal] using hp.upperLeft)
  have hleft := ofLine_doubledWinding_sub_imaginaryZeroFlags_even p
    (verticalBase B.xLower) verticalDirection B.yUpper B.yLower
    (by simpa only [line_vertical] using hp.upperLeft)
    (by simpa only [line_vertical] using hp.lowerLeft)
  simp only [line_horizontal] at hbottom htop
  simp only [line_vertical] at hright hleft
  let lowerLeftFlag : ℤ :=
    if (p.eval (CCL.GaussianRat.mk B.xLower B.yLower)).im = 0 then 1 else 0
  let lowerRightFlag : ℤ :=
    if (p.eval (CCL.GaussianRat.mk B.xUpper B.yLower)).im = 0 then 1 else 0
  let upperRightFlag : ℤ :=
    if (p.eval (CCL.GaussianRat.mk B.xUpper B.yUpper)).im = 0 then 1 else 0
  let upperLeftFlag : ℤ :=
    if (p.eval (CCL.GaussianRat.mk B.xLower B.yUpper)).im = 0 then 1 else 0
  change Even ((horizontalEdge p B.yLower B.xLower B.xUpper).doubledWinding -
    (lowerLeftFlag - lowerRightFlag)) at hbottom
  change Even ((verticalEdge p B.xUpper B.yLower B.yUpper).doubledWinding -
    (lowerRightFlag - upperRightFlag)) at hright
  change Even ((horizontalEdge p B.yUpper B.xUpper B.xLower).doubledWinding -
    (upperRightFlag - upperLeftFlag)) at htop
  change Even ((verticalEdge p B.xLower B.yUpper B.yLower).doubledWinding -
    (upperLeftFlag - lowerLeftFlag)) at hleft
  rcases (((hbottom.add hright).add htop).add hleft) with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [quadrupledBoxWinding_eq]
  calc
    (horizontalEdge p B.yLower B.xLower B.xUpper).doubledWinding +
          (verticalEdge p B.xUpper B.yLower B.yUpper).doubledWinding +
          (horizontalEdge p B.yUpper B.xUpper B.xLower).doubledWinding +
          (verticalEdge p B.xLower B.yUpper B.yLower).doubledWinding =
        ((horizontalEdge p B.yLower B.xLower B.xUpper).doubledWinding -
            (lowerLeftFlag - lowerRightFlag)) +
          ((verticalEdge p B.xUpper B.yLower B.yUpper).doubledWinding -
            (lowerRightFlag - upperRightFlag)) +
          ((horizontalEdge p B.yUpper B.xUpper B.xLower).doubledWinding -
            (upperRightFlag - upperLeftFlag)) +
          ((verticalEdge p B.xLower B.yUpper B.yLower).doubledWinding -
            (upperLeftFlag - lowerLeftFlag)) := by ring
    _ = k + k := hk

/-- Six decidable coordinate-polynomial checks on each of the four oriented
box edges, retained for the specialized nondegenerate-coordinate API. -/
structure BoxProductCoordinateNondegenerate
    (p q : GaussianPolynomial) (B : CCL.RatBox) : Prop where
  bottom : LineProductCoordinateNondegenerate p q
    (horizontalBase B.yLower) horizontalDirection B.xLower B.xUpper
  right : LineProductCoordinateNondegenerate p q
    (verticalBase B.xUpper) verticalDirection B.yLower B.yUpper
  top : LineProductCoordinateNondegenerate p q
    (horizontalBase B.yUpper) horizontalDirection B.xUpper B.xLower
  left : LineProductCoordinateNondegenerate p q
    (verticalBase B.xLower) verticalDirection B.yUpper B.yLower

/-- Four finite checks, one for each positively oriented edge of a box. -/
def boxProductFormulaCheck
    (p q : GaussianPolynomial) (B : CCL.RatBox) : Bool :=
  horizontalProductFormulaCheck p q B.yLower B.xLower B.xUpper &&
  verticalProductFormulaCheck p q B.xUpper B.yLower B.yUpper &&
  horizontalProductFormulaCheck p q B.yUpper B.xUpper B.xLower &&
  verticalProductFormulaCheck p q B.xLower B.yUpper B.yLower

/-- The four endpoint corrections telescope, so successful edge checks prove
the raw closed-box product formula exactly. -/
theorem quadrupledBoxWinding_mul_of_check
    (p q : GaussianPolynomial) (B : CCL.RatBox)
    (hcheck : boxProductFormulaCheck p q B = true) :
    quadrupledBoxWinding (p * q) B =
      quadrupledBoxWinding p B + quadrupledBoxWinding q B := by
  have hchecks :
      ((horizontalProductFormulaCheck p q B.yLower B.xLower B.xUpper = true ∧
        verticalProductFormulaCheck p q B.xUpper B.yLower B.yUpper = true) ∧
        horizontalProductFormulaCheck p q B.yUpper B.xUpper B.xLower = true) ∧
        verticalProductFormulaCheck p q B.xLower B.yUpper B.yLower = true := by
    simpa [boxProductFormulaCheck] using hcheck
  have hbottom := horizontalProductFormula_of_check p q
    B.yLower B.xLower B.xUpper hchecks.1.1.1
  have hright := verticalProductFormula_of_check p q
    B.xUpper B.yLower B.yUpper hchecks.1.1.2
  have htop := horizontalProductFormula_of_check p q
    B.yUpper B.xUpper B.xLower hchecks.1.2
  have hleft := verticalProductFormula_of_check p q
    B.xLower B.yUpper B.yLower hchecks.2
  rw [quadrupledBoxWinding_eq, quadrupledBoxWinding_eq,
    quadrupledBoxWinding_eq, hbottom, hright, htop, hleft]
  ring

/-- Finite event partitions on the four edges prove the raw closed-box
product formula; all vertex corrections telescope exactly. -/
theorem quadrupledBoxWinding_mul_of_partitions
    (p q : GaussianPolynomial) (B : CCL.RatBox)
    (bottom : HorizontalProductPartition p q
      B.yLower B.xLower B.xUpper)
    (right : VerticalProductPartition p q
      B.xUpper B.yLower B.yUpper)
    (top : HorizontalProductPartition p q
      B.yUpper B.xUpper B.xLower)
    (left : VerticalProductPartition p q
      B.xLower B.yUpper B.yLower) :
    quadrupledBoxWinding (p * q) B =
      quadrupledBoxWinding p B + quadrupledBoxWinding q B := by
  have hbottom := horizontalProductFormula_of_partition p q
    B.yLower B.xLower B.xUpper bottom
  have hright := verticalProductFormula_of_partition p q
    B.xUpper B.yLower B.yUpper right
  have htop := horizontalProductFormula_of_partition p q
    B.yUpper B.xUpper B.xLower top
  have hleft := verticalProductFormula_of_partition p q
    B.xLower B.yUpper B.yLower left
  rw [quadrupledBoxWinding_eq, quadrupledBoxWinding_eq,
    quadrupledBoxWinding_eq, hbottom, hright, htop, hleft]
  ring

/-- Proposition 4.4 at the raw finite-index normalization: vertex
nonvanishing alone makes the four affine-edge product corrections telescope.
No coordinate nondegeneracy, event partition, classifier resolution, or fuel
is supplied by the caller. -/
theorem quadrupledBoxWinding_mul
    (p q : GaussianPolynomial) (B : CCL.RatBox)
    (hp : BoxVertexNonzero p B) (hq : BoxVertexNonzero q B)
    (hx : B.xLower < B.xUpper) (hy : B.yLower < B.yUpper) :
    quadrupledBoxWinding (p * q) B =
      quadrupledBoxWinding p B + quadrupledBoxWinding q B := by
  have hbottomLine := lineProductFormula_of_endpoint_nonzero p q
    (horizontalBase B.yLower) horizontalDirection B.xLower B.xUpper
    (by simpa only [line_horizontal] using hp.lowerLeft)
    (by simpa only [line_horizontal] using hq.lowerLeft)
    (by simpa only [line_horizontal] using hp.lowerRight)
    (by simpa only [line_horizontal] using hq.lowerRight) hx.ne
  have hrightLine := lineProductFormula_of_endpoint_nonzero p q
    (verticalBase B.xUpper) verticalDirection B.yLower B.yUpper
    (by simpa only [line_vertical] using hp.lowerRight)
    (by simpa only [line_vertical] using hq.lowerRight)
    (by simpa only [line_vertical] using hp.upperRight)
    (by simpa only [line_vertical] using hq.upperRight) hy.ne
  have htopLine := lineProductFormula_of_endpoint_nonzero p q
    (horizontalBase B.yUpper) horizontalDirection B.xUpper B.xLower
    (by simpa only [line_horizontal] using hp.upperRight)
    (by simpa only [line_horizontal] using hq.upperRight)
    (by simpa only [line_horizontal] using hp.upperLeft)
    (by simpa only [line_horizontal] using hq.upperLeft) hx.ne'
  have hleftLine := lineProductFormula_of_endpoint_nonzero p q
    (verticalBase B.xLower) verticalDirection B.yUpper B.yLower
    (by simpa only [line_vertical] using hp.upperLeft)
    (by simpa only [line_vertical] using hq.upperLeft)
    (by simpa only [line_vertical] using hp.lowerLeft)
    (by simpa only [line_vertical] using hq.lowerLeft) hy.ne'
  have hbottom := by
    simpa only [horizontalEdge, lineProductCorrection2, line_horizontal] using
      hbottomLine
  have hright := by
    simpa only [verticalEdge, lineProductCorrection2, line_vertical] using
      hrightLine
  have htop := by
    simpa only [horizontalEdge, lineProductCorrection2, line_horizontal] using
      htopLine
  have hleft := by
    simpa only [verticalEdge, lineProductCorrection2, line_vertical] using
      hleftLine
  rw [quadrupledBoxWinding_eq, quadrupledBoxWinding_eq,
    quadrupledBoxWinding_eq]
  simp only [horizontalEdge, verticalEdge]
  rw [hbottom, hright, htop, hleft]
  ring

/-- Closed-box product multiplicativity produced directly from the complete
coefficient-width partition construction on all four nondegenerate edges.
No caller-supplied event partition, classifier resolution, or fuel remains. -/
theorem quadrupledBoxWinding_mul_of_nondegenerate_coordinates
    (p q : GaussianPolynomial) (B : CCL.RatBox)
    (coordinates : BoxProductCoordinateNondegenerate p q B)
    (hp : BoxVertexNonzero p B) (hq : BoxVertexNonzero q B)
    (hx : B.xLower < B.xUpper) (hy : B.yLower < B.yUpper) :
    quadrupledBoxWinding (p * q) B =
      quadrupledBoxWinding p B + quadrupledBoxWinding q B := by
  have hbottomLine := lineProductFormula_of_nondegenerate_coordinates p q
    (horizontalBase B.yLower) horizontalDirection B.xLower B.xUpper
    coordinates.bottom
    (by simpa only [line_horizontal] using hp.lowerLeft)
    (by simpa only [line_horizontal] using hq.lowerLeft)
    (by simpa only [line_horizontal] using hp.lowerRight)
    (by simpa only [line_horizontal] using hq.lowerRight) hx.ne
  have hrightLine := lineProductFormula_of_nondegenerate_coordinates p q
    (verticalBase B.xUpper) verticalDirection B.yLower B.yUpper
    coordinates.right
    (by simpa only [line_vertical] using hp.lowerRight)
    (by simpa only [line_vertical] using hq.lowerRight)
    (by simpa only [line_vertical] using hp.upperRight)
    (by simpa only [line_vertical] using hq.upperRight) hy.ne
  have htopLine := lineProductFormula_of_nondegenerate_coordinates p q
    (horizontalBase B.yUpper) horizontalDirection B.xUpper B.xLower
    coordinates.top
    (by simpa only [line_horizontal] using hp.upperRight)
    (by simpa only [line_horizontal] using hq.upperRight)
    (by simpa only [line_horizontal] using hp.upperLeft)
    (by simpa only [line_horizontal] using hq.upperLeft) hx.ne'
  have hleftLine := lineProductFormula_of_nondegenerate_coordinates p q
    (verticalBase B.xLower) verticalDirection B.yUpper B.yLower
    coordinates.left
    (by simpa only [line_vertical] using hp.upperLeft)
    (by simpa only [line_vertical] using hq.upperLeft)
    (by simpa only [line_vertical] using hp.lowerLeft)
    (by simpa only [line_vertical] using hq.lowerLeft) hy.ne'
  have hbottom := by
    simpa only [horizontalEdge, lineProductCorrection2, line_horizontal] using
      hbottomLine
  have hright := by
    simpa only [verticalEdge, lineProductCorrection2, line_vertical] using
      hrightLine
  have htop := by
    simpa only [horizontalEdge, lineProductCorrection2, line_horizontal] using
      htopLine
  have hleft := by
    simpa only [verticalEdge, lineProductCorrection2, line_vertical] using
      hleftLine
  rw [quadrupledBoxWinding_eq, quadrupledBoxWinding_eq,
    quadrupledBoxWinding_eq]
  simp only [horizontalEdge, verticalEdge]
  rw [hbottom, hright, htop, hleft]
  ring

/-- Direct doubled-normalization product law from the complete four-edge
construction. -/
theorem doubledBoxWinding_mul_of_nondegenerate_coordinates
    (p q : GaussianPolynomial) (B : CCL.RatBox)
    (coordinates : BoxProductCoordinateNondegenerate p q B)
    (hpVertices : BoxVertexNonzero p B)
    (hqVertices : BoxVertexNonzero q B)
    (hx : B.xLower < B.xUpper) (hy : B.yLower < B.yUpper)
    (hpEven : Even (quadrupledBoxWinding p B))
    (hqEven : Even (quadrupledBoxWinding q B)) :
    doubledBoxWinding (p * q) B =
      doubledBoxWinding p B + doubledBoxWinding q B := by
  rcases hpEven with ⟨wp, hpEven⟩
  rcases hqEven with ⟨wq, hqEven⟩
  rw [doubledBoxWinding, doubledBoxWinding, doubledBoxWinding,
    quadrupledBoxWinding_mul_of_nondegenerate_coordinates
      p q B coordinates hpVertices hqVertices hx hy,
    hpEven, hqEven]
  omega

/-- Direct ordinary winding multiplicativity from the complete four-edge
construction. -/
theorem boxWinding_mul_of_nondegenerate_coordinates
    (p q : GaussianPolynomial) (B : CCL.RatBox)
    (coordinates : BoxProductCoordinateNondegenerate p q B)
    (hpVertices : BoxVertexNonzero p B)
    (hqVertices : BoxVertexNonzero q B)
    (hx : B.xLower < B.xUpper) (hy : B.yLower < B.yUpper)
    (hpFour : (4 : ℤ) ∣ quadrupledBoxWinding p B)
    (hqFour : (4 : ℤ) ∣ quadrupledBoxWinding q B) :
    boxWinding (p * q) B = boxWinding p B + boxWinding q B := by
  rcases hpFour with ⟨wp, hpFour⟩
  rcases hqFour with ⟨wq, hqFour⟩
  rw [boxWinding, boxWinding, boxWinding,
    quadrupledBoxWinding_mul_of_nondegenerate_coordinates
      p q B coordinates hpVertices hqVertices hx hy,
    hpFour, hqFour]
  omega

/-- Proposition 4.4 in the doubled closed-box normalization whenever the two
factor sums carry their required parity certificates. -/
theorem doubledBoxWinding_mul_of_parity
    (p q : GaussianPolynomial) (B : CCL.RatBox)
    (hpVertices : BoxVertexNonzero p B)
    (hqVertices : BoxVertexNonzero q B)
    (hx : B.xLower < B.xUpper) (hy : B.yLower < B.yUpper)
    (hpEven : Even (quadrupledBoxWinding p B))
    (hqEven : Even (quadrupledBoxWinding q B)) :
    doubledBoxWinding (p * q) B =
      doubledBoxWinding p B + doubledBoxWinding q B := by
  rcases hpEven with ⟨wp, hpEven⟩
  rcases hqEven with ⟨wq, hqEven⟩
  rw [doubledBoxWinding, doubledBoxWinding, doubledBoxWinding,
    quadrupledBoxWinding_mul p q B hpVertices hqVertices hx hy,
    hpEven, hqEven]
  omega

/-- Proposition 4.4 in the paper's doubled winding normalization, now under
exactly the two vertex-nonvanishing hypotheses and strict box bounds.  Closed
endpoint-sign cancellation computes both required parity proofs. -/
theorem doubledBoxWinding_mul
    (p q : GaussianPolynomial) (B : CCL.RatBox)
    (hpVertices : BoxVertexNonzero p B)
    (hqVertices : BoxVertexNonzero q B)
    (hx : B.xLower < B.xUpper) (hy : B.yLower < B.yUpper) :
    doubledBoxWinding (p * q) B =
      doubledBoxWinding p B + doubledBoxWinding q B :=
  doubledBoxWinding_mul_of_parity p q B hpVertices hqVertices hx hy
    (quadrupledBoxWinding_even_of_vertices p B hpVertices)
    (quadrupledBoxWinding_even_of_vertices q B hqVertices)

/-- Proposition 4.4 in the ordinary integer normalization whenever the two
factor raw sums have certified divisibility by four. -/
theorem boxWinding_mul
    (p q : GaussianPolynomial) (B : CCL.RatBox)
    (hpVertices : BoxVertexNonzero p B)
    (hqVertices : BoxVertexNonzero q B)
    (hx : B.xLower < B.xUpper) (hy : B.yLower < B.yUpper)
    (hpFour : (4 : ℤ) ∣ quadrupledBoxWinding p B)
    (hqFour : (4 : ℤ) ∣ quadrupledBoxWinding q B) :
    boxWinding (p * q) B = boxWinding p B + boxWinding q B := by
  rcases hpFour with ⟨wp, hpFour⟩
  rcases hqFour with ⟨wq, hqFour⟩
  rw [boxWinding, boxWinding, boxWinding,
    quadrupledBoxWinding_mul p q B hpVertices hqVertices hx hy,
    hpFour, hqFour]
  omega

/-- Successful finite product checks give the paper's doubled normalization
once both closed factor sums have the required parity. -/
theorem doubledBoxWinding_mul_of_check
    (p q : GaussianPolynomial) (B : CCL.RatBox)
    (hcheck : boxProductFormulaCheck p q B = true)
    (hp : Even (quadrupledBoxWinding p B))
    (hq : Even (quadrupledBoxWinding q B)) :
    doubledBoxWinding (p * q) B =
      doubledBoxWinding p B + doubledBoxWinding q B := by
  rcases hp with ⟨wp, hp⟩
  rcases hq with ⟨wq, hq⟩
  rw [doubledBoxWinding, doubledBoxWinding, doubledBoxWinding,
    quadrupledBoxWinding_mul_of_check p q B hcheck, hp, hq]
  omega

/-- Partition-certified product law in the paper's doubled normalization. -/
theorem doubledBoxWinding_mul_of_partitions
    (p q : GaussianPolynomial) (B : CCL.RatBox)
    (bottom : HorizontalProductPartition p q
      B.yLower B.xLower B.xUpper)
    (right : VerticalProductPartition p q
      B.xUpper B.yLower B.yUpper)
    (top : HorizontalProductPartition p q
      B.yUpper B.xUpper B.xLower)
    (left : VerticalProductPartition p q
      B.xLower B.yUpper B.yLower)
    (hp : Even (quadrupledBoxWinding p B))
    (hq : Even (quadrupledBoxWinding q B)) :
    doubledBoxWinding (p * q) B =
      doubledBoxWinding p B + doubledBoxWinding q B := by
  rcases hp with ⟨wp, hp⟩
  rcases hq with ⟨wq, hq⟩
  rw [doubledBoxWinding, doubledBoxWinding, doubledBoxWinding,
    quadrupledBoxWinding_mul_of_partitions p q B bottom right top left, hp, hq]
  omega

/-- Successful checks give ordinary winding multiplicativity when both raw
factor windings are divisible by four. -/
theorem boxWinding_mul_of_check
    (p q : GaussianPolynomial) (B : CCL.RatBox)
    (hcheck : boxProductFormulaCheck p q B = true)
    (hp : (4 : ℤ) ∣ quadrupledBoxWinding p B)
    (hq : (4 : ℤ) ∣ quadrupledBoxWinding q B) :
    boxWinding (p * q) B = boxWinding p B + boxWinding q B := by
  rcases hp with ⟨wp, hp⟩
  rcases hq with ⟨wq, hq⟩
  rw [boxWinding, boxWinding, boxWinding,
    quadrupledBoxWinding_mul_of_check p q B hcheck, hp, hq]
  omega

/-- Partition-certified ordinary winding multiplicativity. -/
theorem boxWinding_mul_of_partitions
    (p q : GaussianPolynomial) (B : CCL.RatBox)
    (bottom : HorizontalProductPartition p q
      B.yLower B.xLower B.xUpper)
    (right : VerticalProductPartition p q
      B.xUpper B.yLower B.yUpper)
    (top : HorizontalProductPartition p q
      B.yUpper B.xUpper B.xLower)
    (left : VerticalProductPartition p q
      B.xLower B.yUpper B.yLower)
    (hp : (4 : ℤ) ∣ quadrupledBoxWinding p B)
    (hq : (4 : ℤ) ∣ quadrupledBoxWinding q B) :
    boxWinding (p * q) B = boxWinding p B + boxWinding q B := by
  rcases hp with ⟨wp, hp⟩
  rcases hq with ⟨wq, hq⟩
  rw [boxWinding, boxWinding, boxWinding,
    quadrupledBoxWinding_mul_of_partitions p q B bottom right top left, hp, hq]
  omega

private def identityPolynomial : GaussianPolynomial := ⟨[1, 0]⟩
private def unitSquare : CCL.RatBox := CCL.RatBox.symmetric 1 (by norm_num)

/-- Native regression for the complete four-edge product certificate. -/
theorem identityProduct_unitSquare_check :
    boxProductFormulaCheck identityPolynomial identityPolynomial unitSquare = true := by
  native_decide

/-- The checked product law gives winding two for `Z^2` on the unit square. -/
theorem identityProduct_unitSquare_winding :
    quadrupledBoxWinding (identityPolynomial * identityPolynomial) unitSquare = 8 ∧
      doubledBoxWinding (identityPolynomial * identityPolynomial) unitSquare = 4 ∧
      boxWinding (identityPolynomial * identityPolynomial) unitSquare = 2 := by
  native_decide

end FTA.WindingProduct
