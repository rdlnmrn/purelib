import mathlib.Tactic.QuotientFreeRing
import RFAP.Winding
import RFAP.Cauchy.Partition
import RFAP.Cauchy.Degenerate
import RFAP.Geometry.BoxClearance

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

namespace RFAP.WindingProduct

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev CoordinatePolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Box := RFAP.Boxes.Box
abbrev Interval := RFAP.PathClearance.Interval
abbrev ClearanceCertificate := RFAP.PathClearance.Certificate

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.PathPolynomial
open RFAP.Sturm
open RFAP.Winding

/-- Resolved local Cauchy-chain data for the two factors and their actual
pointwise product on one affine parameter cell. -/
abbrev LineLocalEndpointData
    (p q : GaussianPolynomial) (origin direction : Gaussian)
    (a b : Coordinate) :=
  RFAP.CauchyProduct.LocalEndpointData
    (pathReal p origin direction) (pathImag p origin direction)
    (pathReal q origin direction) (pathImag q origin direction)
    (pathReal (p * q) origin direction) (pathImag (p * q) origin direction)
    a b

/-- The endpoint correction in the doubled Cauchy-index product formula.
It is computed directly from the four finite Gaussian coordinates. -/
def vertexProductCorrection2
    (p q : GaussianPolynomial) (z : Gaussian) : Nat :=
  let pz := p.eval z
  let qz := q.eval z
  signJump 1 ((pz * qz).im * pz.im * qz.im)

/-- The same correction along one displayed affine path. -/
def lineProductCorrection2
    (p q : GaussianPolynomial) (origin direction : Gaussian)
    (t : Coordinate) : Nat :=
  vertexProductCorrection2 p q (line origin direction t)

theorem auxiliaryEndpointCorrection2_ofLine
    (p q : GaussianPolynomial) (origin direction : Gaussian)
    (t : Coordinate) :
    RFAP.CauchyProduct.auxiliaryEndpointCorrection2
        (pathImag p origin direction) (pathImag q origin direction)
        (pathImag (p * q) origin direction) t =
      lineProductCorrection2 p q origin direction t := by
  unfold RFAP.CauchyProduct.auxiliaryEndpointCorrection2
    lineProductCorrection2 vertexProductCorrection2
  simp only [eval_pathImag, eval_mul]
  apply congrArg (signJump 1)
  ring1

/-- Proof data for the local doubled product identity on one oriented
interval.  Every term is an executable finite Cauchy-index calculation. -/
def LineProductFormula
    (p q : GaussianPolynomial) (origin direction : Gaussian)
    (a b : Coordinate) : Prop :=
  (PolynomialEdge.ofLine (p * q) origin direction a b).doubledWinding =
    (PolynomialEdge.ofLine p origin direction a b).doubledWinding +
      (PolynomialEdge.ofLine q origin direction a b).doubledWinding -
      (lineProductCorrection2 p q origin direction a : Int) +
      lineProductCorrection2 p q origin direction b

/-- A resolved finite endpoint cell satisfies the affine-path product
formula.  The bridge uses only the four explicit product evaluation
identities carried by the local data. -/
theorem lineProductFormula_of_localEndpointData
    (p q : GaussianPolynomial) (origin direction : Gaussian)
    (a b : Coordinate)
    (data : LineLocalEndpointData p q origin direction a b) :
    LineProductFormula p q origin direction a b := by
  have formula :=
    RFAP.CauchyProduct.auxiliaryProductFormula_of_localEndpointData
      data
  unfold RFAP.CauchyProduct.AuxiliaryProductFormula at formula
  unfold LineProductFormula PolynomialEdge.doubledWinding
  dsimp only [PolynomialEdge.ofLine]
  rw [← auxiliaryEndpointCorrection2_ofLine p q origin direction a,
    ← auxiliaryEndpointCorrection2_ofLine p q origin direction b]
  exact formula

/-- Any already-assembled auxiliary coordinate formula specializes to the
represented affine Gaussian-polynomial line. -/
theorem lineProductFormula_of_auxiliaryProductFormula
    (p q : GaussianPolynomial) (origin direction : Gaussian)
    (a b : Coordinate)
    (formula : RFAP.CauchyProduct.AuxiliaryProductFormula
      (pathReal p origin direction) (pathImag p origin direction)
      (pathReal q origin direction) (pathImag q origin direction)
      (pathReal (p * q) origin direction)
      (pathImag (p * q) origin direction) a b) :
    LineProductFormula p q origin direction a b := by
  unfold RFAP.CauchyProduct.AuxiliaryProductFormula at formula
  unfold LineProductFormula PolynomialEdge.doubledWinding
  dsimp only [PolynomialEdge.ofLine]
  rw [← auxiliaryEndpointCorrection2_ofLine p q origin direction a,
    ← auxiliaryEndpointCorrection2_ofLine p q origin direction b]
  exact formula

/-- The six decidable nondegeneracy facts used by the finite guard partition
on one affine line. -/
structure LineProductCoordinateNondegenerate
    (p q : GaussianPolynomial) (origin direction : Gaussian) : Prop where
  leftReal : (pathReal p origin direction).isZero = false
  leftImag : (pathImag p origin direction).isZero = false
  rightReal : (pathReal q origin direction).isZero = false
  rightImag : (pathImag q origin direction).isZero = false
  productReal : (pathReal (p * q) origin direction).isZero = false
  productImag : (pathImag (p * q) origin direction).isZero = false

/-- A nonzero Gaussian path value is a nonzero displayed coordinate pair. -/
theorem ofLine_coordinatePair_ne_zero
    (p : GaussianPolynomial) (origin direction : Gaussian)
    (t : Coordinate)
    (valueNonzero : p.eval (line origin direction t) ≠ 0) :
    (pathReal p origin direction).eval t ≠ 0 ∨
      (pathImag p origin direction).eval t ≠ 0 := by
  by_cases realZero : (pathReal p origin direction).eval t = 0
  · right
    intro imagZero
    apply valueNonzero
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · rw [← eval_pathReal]
      exact realZero
    · rw [← eval_pathImag]
      exact imagZero
  · exact Or.inl realZero

/-- Complete affine-line product formula on the nondegenerate coordinate
branch.  The finite central-third partition and its depth are computed
internally from the two displayed clearance certificates. -/
theorem lineProductFormula_of_nondegenerate_coordinates
    (p q : GaussianPolynomial) (origin direction : Gaussian)
    {a b : Coordinate} (less : a < b)
    (coordinates : LineProductCoordinateNondegenerate p q origin direction)
    (left : ClearanceCertificate
      (pathReal p origin direction) (pathImag p origin direction)
      ⟨a, b, less.le⟩)
    (right : ClearanceCertificate
      (pathReal q origin direction) (pathImag q origin direction)
      ⟨a, b, less.le⟩)
    (leftStart : p.eval (line origin direction a) ≠ 0)
    (rightStart : q.eval (line origin direction a) ≠ 0)
    (leftStop : p.eval (line origin direction b) ≠ 0)
    (rightStop : q.eval (line origin direction b) ≠ 0) :
    LineProductFormula p q origin direction a b := by
  let root : Interval := ⟨a, b, less.le⟩
  let A := pathReal p origin direction
  let B := pathImag p origin direction
  let C := pathReal q origin direction
  let D := pathImag q origin direction
  let E := pathReal (p * q) origin direction
  let H := pathImag (p * q) origin direction
  have realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x := by
    intro x
    dsimp only [A, B, C, D, E]
    simp only [eval_pathReal, eval_pathImag, eval_mul,
      RFAP.ConstructiveGaussian.Gaussian.mul_re]
  have imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x := by
    intro x
    dsimp only [A, B, C, D, H]
    simp only [eval_pathReal, eval_pathImag, eval_mul,
      RFAP.ConstructiveGaussian.Gaussian.mul_im]
  have formula :=
    RFAP.CauchyPartition.auxiliaryProductFormula_of_nondegenerate_coordinates
      coordinates.leftReal coordinates.leftImag
      coordinates.rightReal coordinates.rightImag
      coordinates.productReal coordinates.productImag
      (root := root) less left right realIdentity imagIdentity
      (ofLine_coordinatePair_ne_zero p origin direction a leftStart)
      (ofLine_coordinatePair_ne_zero q origin direction a rightStart)
      (ofLine_coordinatePair_ne_zero p origin direction b leftStop)
      (ofLine_coordinatePair_ne_zero q origin direction b rightStop)
  exact lineProductFormula_of_auxiliaryProductFormula
    p q origin direction a b formula

/-- Complete affine-line product formula from two explicit path-clearance
certificates.  The six decidable coordinate tests select either the finite
guard partition or one of the axis-event subdivisions internally. -/
theorem lineProductFormula_of_clearances
    (p q : GaussianPolynomial) (origin direction : Gaussian)
    {a b : Coordinate} (less : a < b)
    (left : ClearanceCertificate
      (pathReal p origin direction) (pathImag p origin direction)
      ⟨a, b, less.le⟩)
    (right : ClearanceCertificate
      (pathReal q origin direction) (pathImag q origin direction)
      ⟨a, b, less.le⟩)
    (leftStart : p.eval (line origin direction a) ≠ 0)
    (rightStart : q.eval (line origin direction a) ≠ 0)
    (leftStop : p.eval (line origin direction b) ≠ 0)
    (rightStop : q.eval (line origin direction b) ≠ 0) :
    LineProductFormula p q origin direction a b := by
  let root : Interval := ⟨a, b, less.le⟩
  let A := pathReal p origin direction
  let B := pathImag p origin direction
  let C := pathReal q origin direction
  let D := pathImag q origin direction
  let E := pathReal (p * q) origin direction
  let H := pathImag (p * q) origin direction
  have realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x := by
    intro x
    dsimp only [A, B, C, D, E]
    simp only [eval_pathReal, eval_pathImag, eval_mul,
      RFAP.ConstructiveGaussian.Gaussian.mul_re]
  have imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x := by
    intro x
    dsimp only [A, B, C, D, H]
    simp only [eval_pathReal, eval_pathImag, eval_mul,
      RFAP.ConstructiveGaussian.Gaussian.mul_im]
  have leftStartPair : A.eval a ≠ 0 ∨ B.eval a ≠ 0 := by
    simpa only [A, B] using
      ofLine_coordinatePair_ne_zero p origin direction a leftStart
  have rightStartPair : C.eval a ≠ 0 ∨ D.eval a ≠ 0 := by
    simpa only [C, D] using
      ofLine_coordinatePair_ne_zero q origin direction a rightStart
  have leftStopPair : A.eval b ≠ 0 ∨ B.eval b ≠ 0 := by
    simpa only [A, B] using
      ofLine_coordinatePair_ne_zero p origin direction b leftStop
  have rightStopPair : C.eval b ≠ 0 ∨ D.eval b ≠ 0 := by
    simpa only [C, D] using
      ofLine_coordinatePair_ne_zero q origin direction b rightStop
  have degenerateFormula
      (degenerate : B.isZero = true ∨ D.isZero = true ∨
        A.isZero = true ∨ C.isZero = true ∨
        H.isZero = true ∨ E.isZero = true) :
      RFAP.CauchyProduct.AuxiliaryProductFormula A B C D E H a b := by
    have result :=
      RFAP.CauchyDegenerate.auxiliaryProductFormula_of_degenerate_coordinates
        (A := A) (B := B) (C := C) (D := D) (E := E) (H := H)
        (root := root) less left right realIdentity imagIdentity degenerate
    simpa only [root] using result
  have nondegenerateFormula
      (ANonzero : A.isZero = false) (BNonzero : B.isZero = false)
      (CNonzero : C.isZero = false) (DNonzero : D.isZero = false)
      (ENonzero : E.isZero = false) (HNonzero : H.isZero = false) :
      RFAP.CauchyProduct.AuxiliaryProductFormula A B C D E H a b := by
    have result :=
      RFAP.CauchyPartition.auxiliaryProductFormula_of_nondegenerate_coordinates
        (A := A) (B := B) (C := C) (D := D) (E := E) (H := H)
        ANonzero BNonzero CNonzero DNonzero ENonzero HNonzero
        (root := root) less left right realIdentity imagIdentity
        leftStartPair rightStartPair leftStopPair rightStopPair
    simpa only [root] using result
  have formula : RFAP.CauchyProduct.AuxiliaryProductFormula
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

/-- Fully executable checker for one local product identity. -/
def lineProductFormulaCheck
    (p q : GaussianPolynomial) (origin direction : Gaussian)
    (a b : Coordinate) : Bool :=
  decide
    ((PolynomialEdge.ofLine (p * q) origin direction a b).doubledWinding =
      (PolynomialEdge.ofLine p origin direction a b).doubledWinding +
        (PolynomialEdge.ofLine q origin direction a b).doubledWinding -
        (lineProductCorrection2 p q origin direction a : Int) +
        lineProductCorrection2 p q origin direction b)

theorem lineProductFormula_of_check
    (p q : GaussianPolynomial) (origin direction : Gaussian)
    (a b : Coordinate)
    (checked : lineProductFormulaCheck p q origin direction a b = true) :
    LineProductFormula p q origin direction a b := by
  simpa only [lineProductFormulaCheck, LineProductFormula,
    decide_eq_true_eq] using checked

theorem lineProductFormula_refl
    (p q : GaussianPolynomial) (origin direction : Gaussian)
    (a : Coordinate) :
    LineProductFormula p q origin direction a a := by
  unfold LineProductFormula PolynomialEdge.doubledWinding
  dsimp only [PolynomialEdge.ofLine]
  simp only [cauchyIndex2]
  ring1

/-- Local product formulas compose under exact interval subdivision; the
middle endpoint correction cancels. -/
theorem LineProductFormula.add
    {p q : GaussianPolynomial} {origin direction : Gaussian}
    {a b c : Coordinate}
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

/-- Reversing an interval reverses its local product identity. -/
theorem LineProductFormula.reverse
    {p q : GaussianPolynomial} {origin direction : Gaussian}
    {a b : Coordinate}
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

/-- Four local product formulas in positive box-boundary orientation. -/
structure BoxProductFormula
    (p q : GaussianPolynomial) (box : Box) : Prop where
  bottom : LineProductFormula p q
    (horizontalBase box.yLower) horizontalDirection
    box.xLower box.xUpper
  right : LineProductFormula p q
    (verticalBase box.xUpper) verticalDirection
    box.yLower box.yUpper
  top : LineProductFormula p q
    (horizontalBase box.yUpper) horizontalDirection
    box.xUpper box.xLower
  left : LineProductFormula p q
    (verticalBase box.xLower) verticalDirection
    box.yUpper box.yLower

/-- Boundary clearance for both factors supplies all four constructive line
formulas.  The top and left sides are obtained by exact orientation reversal. -/
theorem boxProductFormula_of_boundaryClearances
    (p q : GaussianPolynomial) (box : Box)
    (proper : box.Proper)
    (leftClearance : RFAP.BoxClearance.BoundaryClearance p box)
    (rightClearance : RFAP.BoxClearance.BoundaryClearance q box) :
    BoxProductFormula p q box := by
  open RFAP.BoxClearance in
  have pBottomLeft : p.eval (point box.xLower box.yLower) ≠ 0 :=
    leftClearance.eval_ne_zero
      ⟨⟨le_rfl, box.x_valid, le_rfl, box.y_valid⟩, Or.inl rfl⟩
  open RFAP.BoxClearance in
  have qBottomLeft : q.eval (point box.xLower box.yLower) ≠ 0 :=
    rightClearance.eval_ne_zero
      ⟨⟨le_rfl, box.x_valid, le_rfl, box.y_valid⟩, Or.inl rfl⟩
  open RFAP.BoxClearance in
  have pBottomRight : p.eval (point box.xUpper box.yLower) ≠ 0 :=
    leftClearance.eval_ne_zero
      ⟨⟨box.x_valid, le_rfl, le_rfl, box.y_valid⟩,
        Or.inr (Or.inl rfl)⟩
  open RFAP.BoxClearance in
  have qBottomRight : q.eval (point box.xUpper box.yLower) ≠ 0 :=
    rightClearance.eval_ne_zero
      ⟨⟨box.x_valid, le_rfl, le_rfl, box.y_valid⟩,
        Or.inr (Or.inl rfl)⟩
  open RFAP.BoxClearance in
  have pTopRight : p.eval (point box.xUpper box.yUpper) ≠ 0 :=
    leftClearance.eval_ne_zero
      ⟨⟨box.x_valid, le_rfl, box.y_valid, le_rfl⟩,
        Or.inr (Or.inl rfl)⟩
  open RFAP.BoxClearance in
  have qTopRight : q.eval (point box.xUpper box.yUpper) ≠ 0 :=
    rightClearance.eval_ne_zero
      ⟨⟨box.x_valid, le_rfl, box.y_valid, le_rfl⟩,
        Or.inr (Or.inl rfl)⟩
  open RFAP.BoxClearance in
  have pTopLeft : p.eval (point box.xLower box.yUpper) ≠ 0 :=
    leftClearance.eval_ne_zero
      ⟨⟨le_rfl, box.x_valid, box.y_valid, le_rfl⟩, Or.inl rfl⟩
  open RFAP.BoxClearance in
  have qTopLeft : q.eval (point box.xLower box.yUpper) ≠ 0 :=
    rightClearance.eval_ne_zero
      ⟨⟨le_rfl, box.x_valid, box.y_valid, le_rfl⟩, Or.inl rfl⟩
  have bottom := lineProductFormula_of_clearances p q
    (horizontalBase box.yLower) horizontalDirection proper.1
    (RFAP.BoxClearance.bottomOfBoundary
      leftClearance).toPathCertificate
    (RFAP.BoxClearance.bottomOfBoundary
      rightClearance).toPathCertificate
    (by simpa only [line_horizontal] using pBottomLeft)
    (by simpa only [line_horizontal] using qBottomLeft)
    (by simpa only [line_horizontal] using pBottomRight)
    (by simpa only [line_horizontal] using qBottomRight)
  have right := lineProductFormula_of_clearances p q
    (verticalBase box.xUpper) verticalDirection proper.2
    (RFAP.BoxClearance.rightOfBoundary
      leftClearance).toPathCertificate
    (RFAP.BoxClearance.rightOfBoundary
      rightClearance).toPathCertificate
    (by simpa only [line_vertical] using pBottomRight)
    (by simpa only [line_vertical] using qBottomRight)
    (by simpa only [line_vertical] using pTopRight)
    (by simpa only [line_vertical] using qTopRight)
  have topIncreasing := lineProductFormula_of_clearances p q
    (horizontalBase box.yUpper) horizontalDirection proper.1
    (RFAP.BoxClearance.topOfBoundary
      leftClearance).toPathCertificate
    (RFAP.BoxClearance.topOfBoundary
      rightClearance).toPathCertificate
    (by simpa only [line_horizontal] using pTopLeft)
    (by simpa only [line_horizontal] using qTopLeft)
    (by simpa only [line_horizontal] using pTopRight)
    (by simpa only [line_horizontal] using qTopRight)
  have leftIncreasing := lineProductFormula_of_clearances p q
    (verticalBase box.xLower) verticalDirection proper.2
    (RFAP.BoxClearance.leftOfBoundary
      leftClearance).toPathCertificate
    (RFAP.BoxClearance.leftOfBoundary
      rightClearance).toPathCertificate
    (by simpa only [line_vertical] using pBottomLeft)
    (by simpa only [line_vertical] using qBottomLeft)
    (by simpa only [line_vertical] using pTopLeft)
    (by simpa only [line_vertical] using qTopLeft)
  exact
    { bottom := bottom
      right := right
      top := topIncreasing.reverse
      left := leftIncreasing.reverse }

/-- Four executable local checks in positive boundary orientation. -/
def boxProductFormulaCheck
    (p q : GaussianPolynomial) (box : Box) : Bool :=
  lineProductFormulaCheck p q
      (horizontalBase box.yLower) horizontalDirection
      box.xLower box.xUpper &&
    lineProductFormulaCheck p q
      (verticalBase box.xUpper) verticalDirection
      box.yLower box.yUpper &&
    lineProductFormulaCheck p q
      (horizontalBase box.yUpper) horizontalDirection
      box.xUpper box.xLower &&
    lineProductFormulaCheck p q
      (verticalBase box.xLower) verticalDirection
      box.yUpper box.yLower

theorem boxProductFormula_of_check
    (p q : GaussianPolynomial) (box : Box)
    (checked : boxProductFormulaCheck p q box = true) :
    BoxProductFormula p q box := by
  have checks :
      ((lineProductFormulaCheck p q
          (horizontalBase box.yLower) horizontalDirection
          box.xLower box.xUpper = true ∧
        lineProductFormulaCheck p q
          (verticalBase box.xUpper) verticalDirection
          box.yLower box.yUpper = true) ∧
        lineProductFormulaCheck p q
          (horizontalBase box.yUpper) horizontalDirection
          box.xUpper box.xLower = true) ∧
        lineProductFormulaCheck p q
          (verticalBase box.xLower) verticalDirection
          box.yUpper box.yLower = true := by
    simpa only [boxProductFormulaCheck, Bool.and_eq_true] using checked
  exact
    { bottom := lineProductFormula_of_check _ _ _ _ _ _ checks.1.1.1
      right := lineProductFormula_of_check _ _ _ _ _ _ checks.1.1.2
      top := lineProductFormula_of_check _ _ _ _ _ _ checks.1.2
      left := lineProductFormula_of_check _ _ _ _ _ _ checks.2 }

/-- The four finite endpoint corrections telescope exactly, yielding raw
closed-box multiplicativity from the four local certificates. -/
theorem quadrupledBoxWinding_mul_of_formula
    (p q : GaussianPolynomial) (box : Box)
    (formula : BoxProductFormula p q box) :
    quadrupledBoxWinding (p * q) box =
      quadrupledBoxWinding p box + quadrupledBoxWinding q box := by
  have bottom := formula.bottom
  have right := formula.right
  have top := formula.top
  have left := formula.left
  unfold LineProductFormula lineProductCorrection2 at bottom right top left
  simp only [line_horizontal] at bottom top
  simp only [line_vertical] at right left
  rw [quadrupledBoxWinding_eq, quadrupledBoxWinding_eq,
    quadrupledBoxWinding_eq]
  simp only [horizontalEdge, verticalEdge]
  rw [bottom, right, top, left]
  ring1

/-- Choice-free closed-box winding multiplicativity from two quantitative
boundary-clearance certificates. -/
theorem quadrupledBoxWinding_mul_of_boundaryClearances
    (p q : GaussianPolynomial) (box : Box)
    (proper : box.Proper)
    (leftClearance : RFAP.BoxClearance.BoundaryClearance p box)
    (rightClearance : RFAP.BoxClearance.BoundaryClearance q box) :
    quadrupledBoxWinding (p * q) box =
      quadrupledBoxWinding p box + quadrupledBoxWinding q box :=
  quadrupledBoxWinding_mul_of_formula p q box
    (boxProductFormula_of_boundaryClearances
      p q box proper leftClearance rightClearance)

theorem quadrupledBoxWinding_mul_of_check
    (p q : GaussianPolynomial) (box : Box)
    (checked : boxProductFormulaCheck p q box = true) :
    quadrupledBoxWinding (p * q) box =
      quadrupledBoxWinding p box + quadrupledBoxWinding q box :=
  quadrupledBoxWinding_mul_of_formula p q box
    (boxProductFormula_of_check p q box checked)

end RFAP.WindingProduct
