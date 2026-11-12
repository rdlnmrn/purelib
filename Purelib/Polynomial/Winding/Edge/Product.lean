module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Sign.Jump
import Purelib.Geometry.Rational.Affine
public import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Gaussian.Path.Components.Nonzero
public import Purelib.Polynomial.Dense.Gaussian.Path.Pair
public import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Degenerate.Partition
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Endpoint
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Partition
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Rational.Pair.Path.Basic
open Purelib.Polynomial.Dense.Rational.CauchyIndex.Product

/-!
# Product identities on affine polynomial edges

The original finite coordinate Cauchy indices carry one endpoint correction.
Typed local certificates establish that correction on the retained affine
edge and transport it through subdivision and orientation reversal.
-/

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

namespace Purelib.Polynomial.Winding.Edge.Product

public section

/-- Resolved local coordinate certificates on one affine parameter cell.

The two original Gaussian polynomial inputs supply their real and imaginary coefficient polynomials, together with the
corresponding coordinates of their actual product. -/
abbrev LineLocalEndpointData
    (p q : Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
      Gaussian.Basic.Canonical)
    (a b : Fraction.Rational) :=
  Endpoint.LocalEndpointData
    (Path.Components.pathReal p origin direction) (Path.Components.pathImag p origin
      direction)
    (Path.Components.pathReal q origin direction) (Path.Components.pathImag q origin
      direction)
    (Path.Components.pathReal (p * q) origin direction) (Path.Components.pathImag (p * q)
      origin direction)
    a b

/-- Compute the doubled product correction at a retained Gaussian point.

The original two polynomial evaluations supply three ordered imaginary factors: the actual product, the first input and
the second input. -/
@[expose] def vertexProductCorrection2
    (p q : Basic.CanonicalCoefficients.CoefficientPolynomial) (z : Gaussian.Basic.Canonical) : Nat :=
  let pz := p.eval z
  let qz := q.eval z
  Sign.Jump.signJump 1 ((pz * qz).im * pz.im * qz.im)

/-- Compute the product correction along the supplied affine path.

The same origin, direction and parameter select the Gaussian point at which the original two polynomial evaluations are
retained. -/
@[expose] def lineProductCorrection2
    (p q : Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
      Gaussian.Basic.Canonical)
    (t : Fraction.Rational) : Nat :=
  vertexProductCorrection2 p q (Affine.line origin direction t)

/-- The affine coordinate correction equals the product correction at the evaluated line point.

The supplied path parameter evaluates the original three imaginary coordinate polynomials, retaining the same factor
order in their sign-jump input. -/
theorem auxiliaryEndpointCorrection2_ofLine
    (p q : Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
      Gaussian.Basic.Canonical)
    (t : Fraction.Rational) :
    Basic.auxiliaryEndpointCorrection2
        (Path.Components.pathImag p origin direction) (Path.Components.pathImag q origin
          direction)
        (Path.Components.pathImag (p * q) origin direction) t =
      lineProductCorrection2 p q origin direction t := by
  unfold Basic.auxiliaryEndpointCorrection2
    lineProductCorrection2 vertexProductCorrection2
  simp only [Path.Components.eval_pathImag, Dense.Basic.DensePolynomial.eval_mul]
  apply congrArg (Sign.Jump.signJump 1)
  ring1

/-- State the corrected doubled winding identity on an oriented affine interval.

The product and both input edges retain the same origin, direction and endpoints. Their integer index readings include
the original correction at each endpoint. -/
@[expose] def LineProductFormula
    (p q : Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
      Gaussian.Basic.Canonical)
    (a b : Fraction.Rational) : Prop :=
  (PolynomialEdge.ofLine (p * q) origin direction a b).doubledWinding =
    (PolynomialEdge.ofLine p origin direction a b).doubledWinding +
      (PolynomialEdge.ofLine q origin direction a b).doubledWinding -
      (lineProductCorrection2 p q origin direction a : Int) +
      lineProductCorrection2 p q origin direction b

/-- Resolved local coordinate data certifies the corrected affine-edge winding identity.

The retained endpoint certificate supplies the original auxiliary coordinate identity; exact path readbacks give the
same oriented Gaussian edge formula. -/
theorem lineProductFormula_of_localEndpointData
    (p q : Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
      Gaussian.Basic.Canonical)
    (a b : Fraction.Rational)
    (data : LineLocalEndpointData p q origin direction a b) :
    LineProductFormula p q origin direction a b := by
  have formula :=
    Endpoint.auxiliaryProductFormula_of_localEndpointData
      data
  unfold Basic.AuxiliaryProductFormula at formula
  unfold LineProductFormula PolynomialEdge.doubledWinding
  dsimp only [PolynomialEdge.ofLine]
  rw [← auxiliaryEndpointCorrection2_ofLine p q origin direction a,
    ← auxiliaryEndpointCorrection2_ofLine p q origin direction b]
  exact formula

/-- An auxiliary coordinate formula certifies the represented affine Gaussian edge.

The original input and product coordinate polynomials determine the same path and correction readings at both displayed
endpoints. -/
theorem lineProductFormula_of_auxiliaryProductFormula
    (p q : Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
      Gaussian.Basic.Canonical)
    (a b : Fraction.Rational)
    (formula : Basic.AuxiliaryProductFormula
      (Path.Components.pathReal p origin direction) (Path.Components.pathImag p origin
        direction)
      (Path.Components.pathReal q origin direction) (Path.Components.pathImag q origin
        direction)
      (Path.Components.pathReal (p * q) origin direction)
      (Path.Components.pathImag (p * q) origin direction) a b) :
    LineProductFormula p q origin direction a b := by
  unfold Basic.AuxiliaryProductFormula at formula
  unfold LineProductFormula PolynomialEdge.doubledWinding
  dsimp only [PolynomialEdge.ofLine]
  rw [← auxiliaryEndpointCorrection2_ofLine p q origin direction a,
    ← auxiliaryEndpointCorrection2_ofLine p q origin direction b]
  exact formula

@[expose] public section

/-- Retain all six Boolean coordinate nonzero certificates of an affine product edge.

The original two real/imaginary input coordinate polynomials and the actual product coordinate polynomials are each
required to fail their own zero test. -/
structure LineProductCoordinateNondegenerate
    (p q : Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
      Gaussian.Basic.Canonical) : Prop where
  /-- The first factor's real coordinate polynomial is nonzero. -/ leftReal : (Path.Components.pathReal p
    origin direction).isZero = false
  /-- The first factor's imaginary coordinate polynomial is nonzero. -/ leftImag :
    (Path.Components.pathImag p origin direction).isZero = false
  /-- The second factor's real coordinate polynomial is nonzero. -/ rightReal : (Path.Components.pathReal
    q origin direction).isZero = false
  /-- The second factor's imaginary coordinate polynomial is nonzero. -/ rightImag :
    (Path.Components.pathImag q origin direction).isZero = false
  /-- The actual product's real coordinate polynomial is nonzero. -/ productReal :
    (Path.Components.pathReal (p * q) origin direction).isZero = false
  /-- The actual product's imaginary coordinate polynomial is nonzero. -/ productImag :
    (Path.Components.pathImag (p * q) origin direction).isZero = false

end

/-- The six nondegenerate coordinate certificates give the affine-edge product formula.

The original clearance certificates determine the finite central-third partition and depth. Exact coordinate evaluation
identities preserve both factors and their actual product. -/
theorem lineProductFormula_of_nondegenerate_coordinates
    (p q : Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
      Gaussian.Basic.Canonical)
    {a b : Fraction.Rational} (less : a < b)
    (coordinates : LineProductCoordinateNondegenerate p q origin direction)
    (left : Clearance.Pair.Basic.Certificate
      (Path.Components.pathReal p origin direction) (Path.Components.pathImag p origin
        direction)
      ⟨a, b, less.le⟩)
    (right : Clearance.Pair.Basic.Certificate
      (Path.Components.pathReal q origin direction) (Path.Components.pathImag q origin
        direction)
      ⟨a, b, less.le⟩)
    (leftStart : p.eval (Affine.line origin direction a) ≠ 0)
    (rightStart : q.eval (Affine.line origin direction a) ≠ 0)
    (leftStop : p.eval (Affine.line origin direction b) ≠ 0)
    (rightStop : q.eval (Affine.line origin direction b) ≠ 0) :
    LineProductFormula p q origin direction a b := by
  let root : Interval.Bounds := ⟨a, b, less.le⟩
  let A := Path.Components.pathReal p origin direction
  let B := Path.Components.pathImag p origin direction
  let C := Path.Components.pathReal q origin direction
  let D := Path.Components.pathImag q origin direction
  let E := Path.Components.pathReal (p * q) origin direction
  let H := Path.Components.pathImag (p * q) origin direction
  have realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x := by
    intro x
    dsimp only [A, B, C, D, E]
    rewrite [Path.Components.eval_pathReal,
      Path.Components.eval_pathReal,
      Path.Components.eval_pathReal,
      Path.Components.eval_pathImag,
      Path.Components.eval_pathImag,
      Dense.Basic.DensePolynomial.eval_mul, Gaussian.Basic.mul_re]
    exact Eq.refl _
  have imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x := by
    intro x
    dsimp only [A, B, C, D, H]
    rewrite [Path.Components.eval_pathImag,
      Path.Components.eval_pathReal,
      Path.Components.eval_pathReal,
      Path.Components.eval_pathImag,
      Path.Components.eval_pathImag,
      Dense.Basic.DensePolynomial.eval_mul, Gaussian.Basic.mul_im]
    exact Eq.refl _
  have formula :=
    Partition.auxiliaryProductFormula_of_nondegenerate_coordinates
      coordinates.leftReal coordinates.leftImag
      coordinates.rightReal coordinates.rightImag
      coordinates.productReal coordinates.productImag
      (root := root) less left right realIdentity imagIdentity
      (Path.Components.Nonzero.ofLine_coordinatePair_ne_zero p origin direction a leftStart)
      (Path.Components.Nonzero.ofLine_coordinatePair_ne_zero q origin direction a rightStart)
      (Path.Components.Nonzero.ofLine_coordinatePair_ne_zero p origin direction b leftStop)
      (Path.Components.Nonzero.ofLine_coordinatePair_ne_zero q origin direction b rightStop)
  exact lineProductFormula_of_auxiliaryProductFormula
    p q origin direction a b formula

/-- Two retained path-clearance certificates give the affine-edge product formula.

The original six coordinate zero tests select either the finite guard partition or an axis-event subdivision, with the
same input polynomials and endpoint nonzero witnesses. -/
theorem lineProductFormula_of_clearances
    (p q : Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
      Gaussian.Basic.Canonical)
    {a b : Fraction.Rational} (less : a < b)
    (left : Clearance.Pair.Basic.Certificate
      (Path.Components.pathReal p origin direction) (Path.Components.pathImag p origin
        direction)
      ⟨a, b, less.le⟩)
    (right : Clearance.Pair.Basic.Certificate
      (Path.Components.pathReal q origin direction) (Path.Components.pathImag q origin
        direction)
      ⟨a, b, less.le⟩)
    (leftStart : p.eval (Affine.line origin direction a) ≠ 0)
    (rightStart : q.eval (Affine.line origin direction a) ≠ 0)
    (leftStop : p.eval (Affine.line origin direction b) ≠ 0)
    (rightStop : q.eval (Affine.line origin direction b) ≠ 0) :
    LineProductFormula p q origin direction a b := by
  let root : Interval.Bounds := ⟨a, b, less.le⟩
  let A := Path.Components.pathReal p origin direction
  let B := Path.Components.pathImag p origin direction
  let C := Path.Components.pathReal q origin direction
  let D := Path.Components.pathImag q origin direction
  let E := Path.Components.pathReal (p * q) origin direction
  let H := Path.Components.pathImag (p * q) origin direction
  have realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x := by
    intro x
    dsimp only [A, B, C, D, E]
    rewrite [Path.Components.eval_pathReal,
      Path.Components.eval_pathReal,
      Path.Components.eval_pathReal,
      Path.Components.eval_pathImag,
      Path.Components.eval_pathImag,
      Dense.Basic.DensePolynomial.eval_mul, Gaussian.Basic.mul_re]
    exact Eq.refl _
  have imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x := by
    intro x
    dsimp only [A, B, C, D, H]
    rewrite [Path.Components.eval_pathImag,
      Path.Components.eval_pathReal,
      Path.Components.eval_pathReal,
      Path.Components.eval_pathImag,
      Path.Components.eval_pathImag,
      Dense.Basic.DensePolynomial.eval_mul, Gaussian.Basic.mul_im]
    exact Eq.refl _
  have leftStartPair : A.eval a ≠ 0 ∨ B.eval a ≠ 0 := by
    simpa only [A, B] using
      Path.Components.Nonzero.ofLine_coordinatePair_ne_zero p origin direction a leftStart
  have rightStartPair : C.eval a ≠ 0 ∨ D.eval a ≠ 0 := by
    simpa only [C, D] using
      Path.Components.Nonzero.ofLine_coordinatePair_ne_zero q origin direction a rightStart
  have leftStopPair : A.eval b ≠ 0 ∨ B.eval b ≠ 0 := by
    simpa only [A, B] using
      Path.Components.Nonzero.ofLine_coordinatePair_ne_zero p origin direction b leftStop
  have rightStopPair : C.eval b ≠ 0 ∨ D.eval b ≠ 0 := by
    simpa only [C, D] using
      Path.Components.Nonzero.ofLine_coordinatePair_ne_zero q origin direction b rightStop
  have degenerateFormula
      (degenerate : B.isZero = true ∨ D.isZero = true ∨
        A.isZero = true ∨ C.isZero = true ∨
        H.isZero = true ∨ E.isZero = true) :
      Basic.AuxiliaryProductFormula A B C D E H a b := by
    have result :=
      Degenerate.Partition.auxiliaryProductFormula_of_degenerate_coordinates
        (A := A) (B := B) (C := C) (D := D) (E := E) (H := H)
        (root := root) less left right realIdentity imagIdentity degenerate
    simpa only [root] using result
  have nondegenerateFormula
      (ANonzero : A.isZero = false) (BNonzero : B.isZero = false)
      (CNonzero : C.isZero = false) (DNonzero : D.isZero = false)
      (ENonzero : E.isZero = false) (HNonzero : H.isZero = false) :
      Basic.AuxiliaryProductFormula A B C D E H a b := by
    have result :=
      Partition.auxiliaryProductFormula_of_nondegenerate_coordinates
        (A := A) (B := B) (C := C) (D := D) (E := E) (H := H)
        ANonzero BNonzero CNonzero DNonzero ENonzero HNonzero
        (root := root) less left right realIdentity imagIdentity
        leftStartPair rightStartPair leftStopPair rightStopPair
    simpa only [root] using result
  have formula : Basic.AuxiliaryProductFormula
      A B C D E H a b := by
    cases BZero : B.isZero with
    | true =>
        exact degenerateFormula (Or.inl BZero)
    | false =>
        cases DZero : D.isZero with
        | true =>
            exact degenerateFormula (Or.inr (Or.inl DZero))
        | false =>
            cases AZero : A.isZero with
            | true =>
                exact degenerateFormula
                  (Or.inr (Or.inr (Or.inl AZero)))
            | false =>
                cases CZero : C.isZero with
                | true =>
                    exact degenerateFormula
                      (Or.inr (Or.inr (Or.inr (Or.inl CZero))))
                | false =>
                    cases HZero : H.isZero with
                    | true =>
                        exact degenerateFormula
                          (Or.inr (Or.inr (Or.inr
                            (Or.inr (Or.inl HZero)))))
                    | false =>
                        cases EZero : E.isZero with
                        | true =>
                            exact degenerateFormula
                              (Or.inr (Or.inr (Or.inr
                                (Or.inr (Or.inr EZero)))))
                        | false =>
                            exact nondegenerateFormula
                              AZero BZero CZero DZero EZero HZero
  exact lineProductFormula_of_auxiliaryProductFormula
    p q origin direction a b formula

/-- The product winding identity holds on a constant parameter interval.

Both endpoints have the same original coordinate and correction readings, so the integer difference vanishes. -/
theorem lineProductFormula_refl
    (p q : Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
      Gaussian.Basic.Canonical)
    (a : Fraction.Rational) :
    LineProductFormula p q origin direction a a := by
  unfold LineProductFormula PolynomialEdge.doubledWinding
  dsimp only [PolynomialEdge.ofLine]
  simp only [Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2]
  ring1

/-- Corrected affine-edge product formulas compose at a common parameter endpoint.

The retained product and two input edge indices each subdivide at that same point, and its original endpoint correction
cancels in the integer sum. -/
theorem LineProductFormula.add
    {p q : Basic.CanonicalCoefficients.CoefficientPolynomial} {origin direction :
      Gaussian.Basic.Canonical}
    {a b c : Fraction.Rational}
    (left : LineProductFormula p q origin direction a b)
    (right : LineProductFormula p q origin direction b c) :
    LineProductFormula p q origin direction a c := by
  unfold LineProductFormula at left right ⊢
  have productAdd := PolynomialEdge.doubledWinding_restrict_add
    (PolynomialEdge.ofLine (p * q) origin direction a c) a b c
  have leftAdd := PolynomialEdge.doubledWinding_restrict_add
    (PolynomialEdge.ofLine p origin direction a c) a b c
  have rightAdd := PolynomialEdge.doubledWinding_restrict_add
    (PolynomialEdge.ofLine q origin direction a c) a b c
  change
    (PolynomialEdge.ofLine (p * q) origin direction a b).doubledWinding +
        (PolynomialEdge.ofLine (p * q) origin direction b c).doubledWinding =
      (PolynomialEdge.ofLine (p * q) origin direction a c).doubledWinding
      at productAdd
  change
    (PolynomialEdge.ofLine p origin direction a b).doubledWinding +
        (PolynomialEdge.ofLine p origin direction b c).doubledWinding =
      (PolynomialEdge.ofLine p origin direction a c).doubledWinding
      at leftAdd
  change
    (PolynomialEdge.ofLine q origin direction a b).doubledWinding +
        (PolynomialEdge.ofLine q origin direction b c).doubledWinding =
      (PolynomialEdge.ofLine q origin direction a c).doubledWinding
      at rightAdd
  rw [← productAdd, ← leftAdd, ← rightAdd, left, right]
  ring1

/-- Reversing the parameter interval reverses its corrected product identity.

The same product and input edges retain their original endpoint readings in reverse order, including the two endpoint
corrections. -/
theorem LineProductFormula.reverse
    {p q : Basic.CanonicalCoefficients.CoefficientPolynomial} {origin direction :
      Gaussian.Basic.Canonical}
    {a b : Fraction.Rational}
    (formula : LineProductFormula p q origin direction a b) :
    LineProductFormula p q origin direction b a := by
  unfold LineProductFormula at formula ⊢
  have productReverse := PolynomialEdge.doubledWinding_reverse
    (PolynomialEdge.ofLine (p * q) origin direction a b)
  have leftReverse := PolynomialEdge.doubledWinding_reverse
    (PolynomialEdge.ofLine p origin direction a b)
  have rightReverse := PolynomialEdge.doubledWinding_reverse
    (PolynomialEdge.ofLine q origin direction a b)
  change
    (PolynomialEdge.ofLine (p * q) origin direction b a).doubledWinding =
      -(PolynomialEdge.ofLine (p * q) origin direction a b).doubledWinding
      at productReverse
  change
    (PolynomialEdge.ofLine p origin direction b a).doubledWinding =
      -(PolynomialEdge.ofLine p origin direction a b).doubledWinding
      at leftReverse
  change
    (PolynomialEdge.ofLine q origin direction b a).doubledWinding =
      -(PolynomialEdge.ofLine q origin direction a b).doubledWinding
      at rightReverse
  rw [productReverse, leftReverse, rightReverse, formula]
  ring1
end

end Purelib.Polynomial.Winding.Edge.Product
