import mathlib.Tactic.QuotientFreeRing
import RFAP.Geometry.HalfPlane
import RFAP.Winding.Product

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

namespace RFAP.WindingHomotopy

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Interval := RFAP.PathClearance.Interval
abbrev Certificate := RFAP.PathClearance.Certificate
abbrev Box := RFAP.Boxes.Box

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.PathPolynomial
open RFAP.PathClearance
open RFAP.Sturm
open RFAP.CauchyProduct
open RFAP.Winding

/-- Complete constructive auxiliary product formula for arbitrary displayed
coordinate polynomials.  The six finite zero tests select the ordinary or
coordinate-degenerate partition internally. -/
theorem auxiliaryProductFormula_of_clearances
    {A B C D E H : Polynomial} {root : Interval}
    (proper : root.lower < root.upper)
    (left : Certificate A B root) (right : Certificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    AuxiliaryProductFormula A B C D E H root.lower root.upper := by
  have leftStart := left.eval_ne_zero
    (x := root.lower) ⟨le_rfl, root.valid⟩
  have rightStart := right.eval_ne_zero
    (x := root.lower) ⟨le_rfl, root.valid⟩
  have leftStop := left.eval_ne_zero
    (x := root.upper) ⟨root.valid, le_rfl⟩
  have rightStop := right.eval_ne_zero
    (x := root.upper) ⟨root.valid, le_rfl⟩
  by_cases BZero : B.isZero = true
  · exact RFAP.CauchyDegenerate.auxiliaryProductFormula_of_degenerate_coordinates
      proper left right realIdentity imagIdentity (Or.inl BZero)
  have BNonzero : B.isZero = false := by simpa using BZero
  by_cases DZero : D.isZero = true
  · exact RFAP.CauchyDegenerate.auxiliaryProductFormula_of_degenerate_coordinates
      proper left right realIdentity imagIdentity
      (Or.inr (Or.inl DZero))
  have DNonzero : D.isZero = false := by simpa using DZero
  by_cases AZero : A.isZero = true
  · exact RFAP.CauchyDegenerate.auxiliaryProductFormula_of_degenerate_coordinates
      proper left right realIdentity imagIdentity
      (Or.inr (Or.inr (Or.inl AZero)))
  have ANonzero : A.isZero = false := by simpa using AZero
  by_cases CZero : C.isZero = true
  · exact RFAP.CauchyDegenerate.auxiliaryProductFormula_of_degenerate_coordinates
      proper left right realIdentity imagIdentity
      (Or.inr (Or.inr (Or.inr (Or.inl CZero))))
  have CNonzero : C.isZero = false := by simpa using CZero
  by_cases HZero : H.isZero = true
  · exact RFAP.CauchyDegenerate.auxiliaryProductFormula_of_degenerate_coordinates
      proper left right realIdentity imagIdentity
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl HZero)))))
  have HNonzero : H.isZero = false := by simpa using HZero
  by_cases EZero : E.isZero = true
  · exact RFAP.CauchyDegenerate.auxiliaryProductFormula_of_degenerate_coordinates
      proper left right realIdentity imagIdentity
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr EZero)))))
  have ENonzero : E.isZero = false := by simpa using EZero
  exact RFAP.CauchyPartition.auxiliaryProductFormula_of_nondegenerate_coordinates
    ANonzero BNonzero CNonzero DNonzero ENonzero HNonzero proper
    left right realIdentity imagIdentity
    leftStart rightStart leftStop rightStop

/-- Real coordinate of `conj(A+iB) * (U+iV)`. -/
def roucheReal (A B U V : Polynomial) : Polynomial :=
  productReal A (-B) U V

/-- Imaginary coordinate of `conj(A+iB) * (U+iV)`. -/
def roucheImag (A B U V : Polynomial) : Polynomial :=
  productImag A (-B) U V

@[simp] theorem eval_roucheReal (A B U V : Polynomial) (x : Coordinate) :
    (roucheReal A B U V).eval x =
      A.eval x * U.eval x + B.eval x * V.eval x := by
  simp [roucheReal, productReal]

@[simp] theorem eval_roucheImag (A B U V : Polynomial) (x : Coordinate) :
    (roucheImag A B U V).eval x =
      A.eval x * V.eval x - B.eval x * U.eval x := by
  simp [roucheImag, productImag]
  ring1

/-- The two finite formulas attached to one oriented Rouché edge. -/
structure LineData
    (A B U V : Polynomial) (a b : Coordinate) : Prop where
  halfPlane : RFAP.HalfPlane.Formula
    (roucheReal A B U V) (roucheImag A B U V) a b
  product : AuxiliaryProductFormula A (-B) U V
    (roucheReal A B U V) (roucheImag A B U V) a b

theorem LineData.reverse
    {A B U V : Polynomial} {a b : Coordinate}
    (data : LineData A B U V a b) : LineData A B U V b a where
  halfPlane := data.halfPlane.reverse
  product := data.product.reverse

private theorem dot_sq_le_product_sums
    (a b u v : Coordinate) :
    (a * u + b * v) ^ 2 ≤
      (a ^ 2 + b ^ 2) * (u ^ 2 + v ^ 2) := by
  apply sub_nonneg.mp
  calc
    0 ≤ (a * v - b * u) ^ 2 :=
      RFAP.ConstructiveFraction.sq_nonneg_direct _
    _ = (a ^ 2 + b ^ 2) * (u ^ 2 + v ^ 2) -
        (a * u + b * v) ^ 2 := by ring1

/-- A displayed positive squared-norm margin itself supplies quantitative
clearance for the sum path.  The denominator is a finite Horner bound for
the dominant path, not a root count or a global field argument. -/
def sumCertificate_of_normDominance
    {A B C D U V : Polynomial} {root : Interval}
    (margin : Coordinate) (marginPositive : 0 < margin)
    (dominance : ∀ x : Coordinate, root.Contains x →
      margin ≤ A.eval x ^ 2 + B.eval x ^ 2 -
        (C.eval x ^ 2 + D.eval x ^ 2))
    (sumReal : ∀ x : Coordinate,
      U.eval x = A.eval x + C.eval x)
    (sumImag : ∀ x : Coordinate,
      V.eval x = B.eval x + D.eval x) :
    Certificate U V root := by
  let majorant := max 1
    (RFAP.PathClearance.evalSqBound A root +
      RFAP.PathClearance.evalSqBound B root)
  have majorantPositive : 0 < majorant := by
    dsimp only [majorant]
    exact (show (0 : Coordinate) < 1 by decide).trans_le
      (le_max_left _ _)
  let denominator := 4 * majorant
  have denominatorPositive : 0 < denominator :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) majorantPositive
  exact
    { bound := margin ^ 2 / denominator
      positive := RFAP.ConstructiveFraction.div_pos_direct
        (RFAP.ConstructiveFraction.pow_pos_direct marginPositive 2)
        denominatorPositive
      lower := by
        intro x inside
        let leftSq := A.eval x ^ 2 + B.eval x ^ 2
        let sumSq := U.eval x ^ 2 + V.eval x ^ 2
        let dot := A.eval x * U.eval x + B.eval x * V.eval x
        have leftSqNonnegative : 0 ≤ leftSq :=
          add_nonneg
            (RFAP.ConstructiveFraction.sq_nonneg_direct _)
            (RFAP.ConstructiveFraction.sq_nonneg_direct _)
        have sumSqNonnegative : 0 ≤ sumSq :=
          add_nonneg
            (RFAP.ConstructiveFraction.sq_nonneg_direct _)
            (RFAP.ConstructiveFraction.sq_nonneg_direct _)
        have leftSqBound : leftSq ≤ majorant := by
          dsimp only [leftSq, majorant]
          exact (add_le_add
            (RFAP.PathClearance.eval_sq_le_evalSqBound A root inside)
            (RFAP.PathClearance.eval_sq_le_evalSqBound B root inside)).trans
            (le_max_right _ _)
        have doubledDot : 2 * dot =
            (A.eval x ^ 2 + B.eval x ^ 2 -
              (C.eval x ^ 2 + D.eval x ^ 2)) + sumSq := by
          dsimp only [dot, sumSq]
          rw [sumReal x, sumImag x]
          ring1
        have marginLeDoubledDot : margin ≤ 2 * dot := by
          rw [doubledDot]
          exact (dominance x inside).trans
            (le_add_of_nonneg_right sumSqNonnegative)
        have doubledDotNonnegative : 0 ≤ 2 * dot :=
          marginPositive.le.trans marginLeDoubledDot
        have squaredMargin : margin ^ 2 ≤ (2 * dot) ^ 2 :=
          RFAP.ConstructiveFraction.pow_le_pow_direct marginPositive.le
            marginLeDoubledDot 2
        have dotCauchy : dot ^ 2 ≤ leftSq * sumSq := by
          dsimp only [dot, leftSq, sumSq]
          exact dot_sq_le_product_sums _ _ _ _
        have scaledCauchy : (2 * dot) ^ 2 ≤
            denominator * sumSq := by
          calc
            (2 * dot) ^ 2 = 4 * dot ^ 2 := by ring1
            _ ≤ 4 * (leftSq * sumSq) :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                dotCauchy (by decide)
            _ ≤ 4 * (majorant * sumSq) :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
                  leftSqBound sumSqNonnegative) (by decide)
            _ = denominator * sumSq := by
              dsimp only [denominator]
              ring1
        apply (RFAP.ConstructiveFraction.div_le_iff_pos
          denominatorPositive).2
        rw [RFAP.ConstructiveFraction.mul_comm sumSq denominator]
        exact squaredMargin.trans scaledCauchy }

/-- Exact rational bound cached by the finite norm-dominance constructor. -/
@[simp] theorem sumCertificate_of_normDominance_bound
    {A B C D U V : Polynomial} {root : Interval}
    (margin : Coordinate) (marginPositive : 0 < margin)
    (dominance : ∀ x : Coordinate, root.Contains x →
      margin ≤ A.eval x ^ 2 + B.eval x ^ 2 -
        (C.eval x ^ 2 + D.eval x ^ 2))
    (sumReal : ∀ x : Coordinate,
      U.eval x = A.eval x + C.eval x)
    (sumImag : ∀ x : Coordinate,
      V.eval x = B.eval x + D.eval x) :
    (sumCertificate_of_normDominance margin marginPositive dominance sumReal
      sumImag).bound =
      margin ^ 2 /
        (4 * max 1
          (RFAP.PathClearance.evalSqBound A root +
            RFAP.PathClearance.evalSqBound B root)) := rfl

/-- Boundary norm dominance resolves one complete finite Rouché edge. -/
theorem lineData_of_normDominance
    {A B C D U V : Polynomial} {root : Interval}
    (proper : root.lower < root.upper)
    (left : Certificate A B root)
    (margin : Coordinate) (marginPositive : 0 < margin)
    (dominance : ∀ x : Coordinate, root.Contains x →
      margin ≤ A.eval x ^ 2 + B.eval x ^ 2 -
        (C.eval x ^ 2 + D.eval x ^ 2))
    (sumReal : ∀ x : Coordinate,
      U.eval x = A.eval x + C.eval x)
    (sumImag : ∀ x : Coordinate,
      V.eval x = B.eval x + D.eval x) :
    LineData A B U V root.lower root.upper := by
  let sum := sumCertificate_of_normDominance margin marginPositive
    dominance sumReal sumImag
  let E := roucheReal A B U V
  let H := roucheImag A B U V
  have realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * U.eval x - (-B).eval x * V.eval x := by
    intro x
    simp only [E, eval_roucheReal, eval_neg]
    ring1
  have imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * V.eval x + (-B).eval x * U.eval x := by
    intro x
    simp only [H, eval_roucheImag, eval_neg]
    ring1
  let conjugateClearance := left.negSecond
  let productClearance : Certificate E H root :=
    conjugateClearance.complexProduct sum realIdentity imagIdentity
  have realPositive : ∀ x : Coordinate, root.Contains x → 0 < E.eval x := by
    intro x inside
    have dominanceAtX := dominance x inside
    have sumNonnegative : 0 ≤ U.eval x ^ 2 + V.eval x ^ 2 :=
      add_nonneg
        (RFAP.ConstructiveFraction.sq_nonneg_direct (U.eval x))
        (RFAP.ConstructiveFraction.sq_nonneg_direct (V.eval x))
    have doubledIdentity :
        2 * E.eval x =
          (A.eval x ^ 2 + B.eval x ^ 2 -
            (C.eval x ^ 2 + D.eval x ^ 2)) +
              (U.eval x ^ 2 + V.eval x ^ 2) := by
      dsimp only [E]
      rw [eval_roucheReal, sumReal x, sumImag x]
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
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        nonpositive (show (0 : Coordinate) ≤ 2 by decide)
    have atMostZero : 2 * E.eval x ≤ 0 := by
      calc
        2 * E.eval x ≤ 2 * 0 := doubledNonpositive
        _ = 0 := RFAP.ConstructiveFraction.mul_zero_direct 2
    exact (not_lt_of_ge atMostZero) doubledPositive
  exact
    { halfPlane := RFAP.HalfPlane.formula_of_positive_real
        productClearance proper realPositive
      product := auxiliaryProductFormula_of_clearances proper
        conjugateClearance sum realIdentity imagIdentity }

/-- One positive rational margin for strict squared-norm dominance on every
point of a finite box boundary. -/
structure BoundaryNormDominance
    (p q : GaussianPolynomial) (box : Box) where
  margin : Coordinate
  positive : 0 < margin
  lower : ∀ z : Gaussian,
    RFAP.BoxClearance.OnBoxBoundary box z →
      margin ≤ normSq (p.eval z) - normSq (q.eval z)

abbrev PolynomialLineData
    (p q : GaussianPolynomial) (origin direction : Gaussian)
    (a b : Coordinate) :=
  LineData (pathReal p origin direction) (pathImag p origin direction)
    (pathReal (p + q) origin direction)
    (pathImag (p + q) origin direction) a b

/-- Convert geometric boundary dominance and two path clearances into the
finite Rouché data for one increasing affine side. -/
theorem lineData_of_boundaryNormDominance
    (p q : GaussianPolynomial) (box : Box)
    (dominance : BoundaryNormDominance p q box)
    (origin direction : Gaussian) {a b : Coordinate}
    (proper : a < b)
    (left : Certificate
      (pathReal p origin direction) (pathImag p origin direction)
      ⟨a, b, proper.le⟩)
    (onBoundary : ∀ t : Coordinate,
      Interval.Contains ⟨a, b, proper.le⟩ t →
        RFAP.BoxClearance.OnBoxBoundary box
          (line origin direction t)) :
    PolynomialLineData p q origin direction a b := by
  apply lineData_of_normDominance
    (C := pathReal q origin direction)
    (D := pathImag q origin direction)
    proper left
    dominance.margin dominance.positive
  · intro t inside
    have lower := dominance.lower (line origin direction t)
      (onBoundary t inside)
    rw [eval_pathReal, eval_pathImag, eval_pathReal, eval_pathImag]
    exact lower
  · intro t
    rw [eval_pathReal, eval_pathReal, eval_pathReal, eval_add]
    rfl
  · intro t
    rw [eval_pathImag, eval_pathImag, eval_pathImag, eval_add]
    rfl

/-- Geometric boundary dominance directly supplies quantitative clearance
for the sum path on one displayed increasing side. -/
def sumCertificate_of_boundaryNormDominance
    (p q : GaussianPolynomial) (box : Box)
    (dominance : BoundaryNormDominance p q box)
    (origin direction : Gaussian) {a b : Coordinate}
    (valid : a ≤ b)
    (onBoundary : ∀ t : Coordinate,
      Interval.Contains ⟨a, b, valid⟩ t →
        RFAP.BoxClearance.OnBoxBoundary box
          (line origin direction t)) :
    Certificate
      (pathReal (p + q) origin direction)
      (pathImag (p + q) origin direction) ⟨a, b, valid⟩ := by
  apply sumCertificate_of_normDominance
    (A := pathReal p origin direction)
    (B := pathImag p origin direction)
    (C := pathReal q origin direction)
    (D := pathImag q origin direction)
    dominance.margin dominance.positive
  · intro t inside
    have lower := dominance.lower (line origin direction t)
      (onBoundary t inside)
    rw [eval_pathReal, eval_pathImag, eval_pathReal, eval_pathImag]
    exact lower
  · intro t
    rw [eval_pathReal, eval_pathReal, eval_pathReal, eval_add]
    rfl
  · intro t
    rw [eval_pathImag, eval_pathImag, eval_pathImag, eval_add]
    rfl

/-- Exact rational bound stored by one boundary-dominance path certificate.
Exposing the finite Horner majorant separately lets downstream transport
proofs compare one side at a time instead of reducing a complete four-side
boundary certificate. -/
@[simp] theorem sumCertificate_of_boundaryNormDominance_bound
    (p q : GaussianPolynomial) (box : Box)
    (dominance : BoundaryNormDominance p q box)
    (origin direction : Gaussian) {a b : Coordinate}
    (valid : a ≤ b)
    (onBoundary : ∀ t : Coordinate,
      RFAP.PathClearance.Interval.Contains ⟨a, b, valid⟩ t →
        RFAP.BoxClearance.OnBoxBoundary box
          (line origin direction t)) :
    (sumCertificate_of_boundaryNormDominance p q box dominance
      origin direction valid onBoundary).bound =
      dominance.margin ^ 2 /
        (4 * max 1
          (RFAP.PathClearance.evalSqBound
              (pathReal p origin direction) ⟨a, b, valid⟩ +
            RFAP.PathClearance.evalSqBound
              (pathImag p origin direction) ⟨a, b, valid⟩)) := by
  rfl

/-- Finite Horner majorant appearing in one side of a boundary-dominance
clearance. -/
def boundarySideMajorant (p : GaussianPolynomial)
    (origin direction : Gaussian) (interval : Interval) : Coordinate :=
  max 1
    (evalSqBound (pathReal p origin direction) interval +
      evalSqBound (pathImag p origin direction) interval)

/-- One finite norm margin constructs boundary clearance for the sum on all
four sides, with no root search or coprimality inference. -/
def boundaryClearance_add_of_boundaryNormDominance
    (p q : GaussianPolynomial) (box : Box) (proper : box.Proper)
    (dominance : BoundaryNormDominance p q box) :
    RFAP.BoxClearance.BoundaryClearance (p + q) box := by
  let bottomCertificate := sumCertificate_of_boundaryNormDominance
    p q box dominance (horizontalBase box.yLower) horizontalDirection
    proper.1.le (by
      intro t inside
      rw [line_horizontal]
      exact ⟨⟨inside.1, inside.2, le_rfl, box.y_valid⟩,
        Or.inr (Or.inr (Or.inl rfl))⟩)
  let rightCertificate := sumCertificate_of_boundaryNormDominance
    p q box dominance (verticalBase box.xUpper) verticalDirection
    proper.2.le (by
      intro t inside
      rw [line_vertical]
      exact ⟨⟨box.x_valid, le_rfl, inside.1, inside.2⟩,
        Or.inr (Or.inl rfl)⟩)
  let topCertificate := sumCertificate_of_boundaryNormDominance
    p q box dominance (horizontalBase box.yUpper) horizontalDirection
    proper.1.le (by
      intro t inside
      rw [line_horizontal]
      exact ⟨⟨inside.1, inside.2, box.y_valid, le_rfl⟩,
        Or.inr (Or.inr (Or.inr rfl))⟩)
  let leftCertificate := sumCertificate_of_boundaryNormDominance
    p q box dominance (verticalBase box.xLower) verticalDirection
    proper.2.le (by
      intro t inside
      rw [line_vertical]
      exact ⟨⟨le_rfl, box.x_valid, inside.1, inside.2⟩, Or.inl rfl⟩)
  exact RFAP.BoxClearance.boundaryOfLines
    (RFAP.BoxClearance.verticalOfPathCertificate
      (p + q) box box.xLower leftCertificate)
    (RFAP.BoxClearance.verticalOfPathCertificate
      (p + q) box box.xUpper rightCertificate)
    (RFAP.BoxClearance.horizontalOfPathCertificate
      (p + q) box box.yLower bottomCertificate)
    (RFAP.BoxClearance.horizontalOfPathCertificate
      (p + q) box box.yUpper topCertificate)

/-- Exact four-side minimum stored by a boundary-dominance clearance. -/
@[simp] theorem boundaryClearance_add_of_boundaryNormDominance_bound
    (p q : GaussianPolynomial) (box : Box) (proper : box.Proper)
    (dominance : BoundaryNormDominance p q box) :
    (boundaryClearance_add_of_boundaryNormDominance
      p q box proper dominance).bound =
      min
        (dominance.margin ^ 2 /
          (4 * boundarySideMajorant p (verticalBase box.xLower)
            verticalDirection ⟨box.yLower, box.yUpper, box.y_valid⟩))
        (min
          (dominance.margin ^ 2 /
            (4 * boundarySideMajorant p (verticalBase box.xUpper)
              verticalDirection ⟨box.yLower, box.yUpper, box.y_valid⟩))
          (min
            (dominance.margin ^ 2 /
              (4 * boundarySideMajorant p (horizontalBase box.yLower)
                horizontalDirection
                ⟨box.xLower, box.xUpper, box.x_valid⟩))
            (dominance.margin ^ 2 /
              (4 * boundarySideMajorant p (horizontalBase box.yUpper)
                horizontalDirection
                ⟨box.xLower, box.xUpper, box.x_valid⟩)))) := by
  rfl

/-- Four finite Rouché records in positive box-boundary orientation. -/
structure BoxData
    (p q : GaussianPolynomial) (box : Box) : Prop where
  bottom : PolynomialLineData p q
    (horizontalBase box.yLower) horizontalDirection
    box.xLower box.xUpper
  right : PolynomialLineData p q
    (verticalBase box.xUpper) verticalDirection
    box.yLower box.yUpper
  top : PolynomialLineData p q
    (horizontalBase box.yUpper) horizontalDirection
    box.xUpper box.xLower
  left : PolynomialLineData p q
    (verticalBase box.xLower) verticalDirection
    box.yUpper box.yLower

/-- Boundary clearances for the dominant path and its sum, together with one
strict norm margin, construct all four finite Rouché records. -/
theorem boxData_of_boundaryNormDominance
    (p q : GaussianPolynomial) (box : Box) (proper : box.Proper)
    (pClearance : RFAP.BoxClearance.BoundaryClearance p box)
    (dominance : BoundaryNormDominance p q box) :
    BoxData p q box := by
  have bottom := lineData_of_boundaryNormDominance p q box dominance
    (horizontalBase box.yLower) horizontalDirection proper.1
    (RFAP.BoxClearance.bottomOfBoundary
      pClearance).toPathCertificate (by
        intro t inside
        rw [line_horizontal]
        exact ⟨⟨inside.1, inside.2, le_rfl, box.y_valid⟩,
          Or.inr (Or.inr (Or.inl rfl))⟩)
  have right := lineData_of_boundaryNormDominance p q box dominance
    (verticalBase box.xUpper) verticalDirection proper.2
    (RFAP.BoxClearance.rightOfBoundary
      pClearance).toPathCertificate (by
        intro t inside
        rw [line_vertical]
        exact ⟨⟨box.x_valid, le_rfl, inside.1, inside.2⟩,
          Or.inr (Or.inl rfl)⟩)
  have topIncreasing := lineData_of_boundaryNormDominance p q box dominance
    (horizontalBase box.yUpper) horizontalDirection proper.1
    (RFAP.BoxClearance.topOfBoundary
      pClearance).toPathCertificate (by
        intro t inside
        rw [line_horizontal]
        exact ⟨⟨inside.1, inside.2, box.y_valid, le_rfl⟩,
          Or.inr (Or.inr (Or.inr rfl))⟩)
  have leftIncreasing := lineData_of_boundaryNormDominance p q box dominance
    (verticalBase box.xLower) verticalDirection proper.2
    (RFAP.BoxClearance.leftOfBoundary
      pClearance).toPathCertificate (by
        intro t inside
        rw [line_vertical]
        exact ⟨⟨le_rfl, box.x_valid, inside.1, inside.2⟩, Or.inl rfl⟩)
  exact
    { bottom := bottom
      right := right
      top := topIncreasing.reverse
      left := leftIncreasing.reverse }

private theorem fourEdgeRoucheTelescope
    {p₀ p₁ p₂ p₃ s₀ s₁ s₂ s₃ h₀ h₁ h₂ h₃ : Int}
    {c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : Int}
    (product₀ : h₀ = -p₀ + s₀ - c₀ + c₁)
    (product₁ : h₁ = -p₁ + s₁ - c₁ + c₂)
    (product₂ : h₂ = -p₂ + s₂ - c₂ + c₃)
    (product₃ : h₃ = -p₃ + s₃ - c₃ + c₀)
    (half₀ : h₀ = d₀ - d₁) (half₁ : h₁ = d₁ - d₂)
    (half₂ : h₂ = d₂ - d₃) (half₃ : h₃ = d₃ - d₀) :
    s₀ + s₁ + s₂ + s₃ = p₀ + p₁ + p₂ + p₃ := by
  have s₀Identity : s₀ = p₀ + h₀ + c₀ - c₁ := by
    rw [product₀]
    ring1
  have s₁Identity : s₁ = p₁ + h₁ + c₁ - c₂ := by
    rw [product₁]
    ring1
  have s₂Identity : s₂ = p₂ + h₂ + c₂ - c₃ := by
    rw [product₂]
    ring1
  have s₃Identity : s₃ = p₃ + h₃ + c₃ - c₀ := by
    rw [product₃]
    ring1
  rw [s₀Identity, s₁Identity, s₂Identity, s₃Identity,
    half₀, half₁, half₂, half₃]
  ring1

/-- The four finite Rouché records telescope to equality of the two raw box
windings. -/
theorem quadrupledBoxWinding_add_of_data
    (p q : GaussianPolynomial) (box : Box)
    (pClearance : RFAP.BoxClearance.BoundaryClearance p box)
    (data : BoxData p q box) :
    quadrupledBoxWinding (p + q) box = quadrupledBoxWinding p box := by
  let bottomClearance :=
    (RFAP.BoxClearance.bottomOfBoundary
      pClearance).toPathCertificate
  let rightClearance :=
    (RFAP.BoxClearance.rightOfBoundary
      pClearance).toPathCertificate
  let topClearance :=
    (RFAP.BoxClearance.topOfBoundary
      pClearance).toPathCertificate
  let leftClearance :=
    (RFAP.BoxClearance.leftOfBoundary
      pClearance).toPathCertificate
  have bottomStart := bottomClearance.eval_ne_zero
    (x := box.xLower) ⟨le_rfl, box.x_valid⟩
  have bottomStop := bottomClearance.eval_ne_zero
    (x := box.xUpper) ⟨box.x_valid, le_rfl⟩
  have rightStart := rightClearance.eval_ne_zero
    (x := box.yLower) ⟨le_rfl, box.y_valid⟩
  have rightStop := rightClearance.eval_ne_zero
    (x := box.yUpper) ⟨box.y_valid, le_rfl⟩
  have topStart := topClearance.eval_ne_zero
    (x := box.xUpper) ⟨box.x_valid, le_rfl⟩
  have topStop := topClearance.eval_ne_zero
    (x := box.xLower) ⟨le_rfl, box.x_valid⟩
  have leftStart := leftClearance.eval_ne_zero
    (x := box.yUpper) ⟨box.y_valid, le_rfl⟩
  have leftStop := leftClearance.eval_ne_zero
    (x := box.yLower) ⟨le_rfl, box.y_valid⟩
  have bottomConjugate := cauchyIndex2_neg_denominator
    bottomStart bottomStop
  have rightConjugate := cauchyIndex2_neg_denominator
    rightStart rightStop
  have topConjugate := cauchyIndex2_neg_denominator
    topStart topStop
  have leftConjugate := cauchyIndex2_neg_denominator
    leftStart leftStop
  have bottomHalf := data.bottom.halfPlane
  have rightHalf := data.right.halfPlane
  have topHalf := data.top.halfPlane
  have leftHalf := data.left.halfPlane
  have bottomProduct := data.bottom.product
  have rightProduct := data.right.product
  have topProduct := data.top.product
  have leftProduct := data.left.product
  unfold RFAP.HalfPlane.Formula at bottomHalf rightHalf topHalf leftHalf
  unfold AuxiliaryProductFormula auxiliaryEndpointCorrection2 at bottomProduct rightProduct topProduct leftProduct
  simp only [eval_roucheReal, eval_roucheImag, eval_neg,
    eval_pathReal, eval_pathImag, line_horizontal] at bottomHalf topHalf bottomProduct topProduct
  simp only [eval_roucheReal, eval_roucheImag, eval_neg,
    eval_pathReal, eval_pathImag, line_vertical] at rightHalf leftHalf rightProduct leftProduct
  rw [bottomConjugate] at bottomProduct
  rw [rightConjugate] at rightProduct
  rw [topConjugate] at topProduct
  rw [leftConjugate] at leftProduct
  rw [quadrupledBoxWinding_eq, quadrupledBoxWinding_eq]
  simp only [horizontalEdge, verticalEdge,
    PolynomialEdge.doubledWinding, PolynomialEdge.ofLine]
  exact fourEdgeRoucheTelescope bottomProduct rightProduct topProduct
    leftProduct bottomHalf rightHalf topHalf leftHalf

/-- Finite constructive Rouché transfer on one box boundary. -/
theorem quadrupledBoxWinding_add_of_boundaryNormDominance
    (p q : GaussianPolynomial) (box : Box) (proper : box.Proper)
    (pClearance : RFAP.BoxClearance.BoundaryClearance p box)
    (dominance : BoundaryNormDominance p q box) :
    quadrupledBoxWinding (p + q) box = quadrupledBoxWinding p box :=
  quadrupledBoxWinding_add_of_data p q box pClearance
    (boxData_of_boundaryNormDominance p q box proper
      pClearance dominance)

end RFAP.WindingHomotopy
