import FTA.GaussianZeroDeflation
import FTA.RootTrackSeparation

/-!
# Winding certificates after constructive zero deflation

If a squarefree polynomial has an exact zero root, the executable controller
runs on the quotient `q` in the factorization `p(Z) = q(Z) Z`.  Its active
boxes are first refined until they exclude the origin.  This file proves,
using only rational inequalities and finite Cauchy-index product arithmetic,
that every such quotient winding-one box is also a winding-one box for the
original polynomial.  It also transports the quantitative boundary and side
clearance certificates needed by subsequent finite refinements.
-/

namespace FTA
namespace GaussianZeroDeflation

open CCL CCL.GaussianRat
open FTA.AffineWinding
open FTA.BoxClearance
open FTA.ComputablePolynomial.DensePolynomial
open FTA.LocalExtraction
open FTA.RootTrackSeparation
open FTA.Winding
open FTA.WindingHomotopy
open FTA.WindingProduct

/-- A positive rational lower bound for `N(z)` throughout a box known not to
contain the origin. -/
structure ZeroExclusionCertificate (B : RatBox) where
  bound : ℚ
  positive : 0 < bound
  lower : ∀ z : QI, B.Contains z → bound ≤ normSq z

/-- Exact rational box exclusion supplies a positive squared-coordinate
margin throughout the whole box. -/
def zeroExclusionCertificate {B : RatBox} (outside : ¬B.Contains 0) :
    ZeroExclusionCertificate B := by
  by_cases left : 0 < B.xLower
  · exact
      { bound := B.xLower ^ 2
        positive := sq_pos_of_pos left
        lower := by
          intro z contains
          have realPositive : 0 < z.re := left.trans_le contains.1
          have realSq : B.xLower ^ 2 ≤ z.re ^ 2 := by
            apply sq_le_sq.mpr
            rw [abs_of_pos left, abs_of_pos realPositive]
            exact contains.1
          rw [normSq]
          linarith [sq_nonneg z.im] }
  · by_cases right : B.xUpper < 0
    · exact
        { bound := B.xUpper ^ 2
          positive := sq_pos_of_neg right
          lower := by
            intro z contains
            have realNegative : z.re < 0 := contains.2.1.trans_lt right
            have realSq : B.xUpper ^ 2 ≤ z.re ^ 2 := by
              apply sq_le_sq.mpr
              rw [abs_of_neg right, abs_of_neg realNegative]
              linarith [contains.2.1]
            rw [normSq]
            linarith [sq_nonneg z.im] }
    · by_cases below : 0 < B.yLower
      · exact
        { bound := B.yLower ^ 2
          positive := sq_pos_of_pos below
          lower := by
            intro z contains
            have imagPositive : 0 < z.im := below.trans_le contains.2.2.1
            have imagSq : B.yLower ^ 2 ≤ z.im ^ 2 := by
              apply sq_le_sq.mpr
              rw [abs_of_pos below, abs_of_pos imagPositive]
              exact contains.2.2.1
            rw [normSq]
            linarith [sq_nonneg z.re] }
      · by_cases above : B.yUpper < 0
        · exact
          { bound := B.yUpper ^ 2
            positive := sq_pos_of_neg above
            lower := by
              intro z contains
              have imagNegative : z.im < 0 := contains.2.2.2.trans_lt above
              have imagSq : B.yUpper ^ 2 ≤ z.im ^ 2 := by
                apply sq_le_sq.mpr
                rw [abs_of_neg above, abs_of_neg imagNegative]
                linarith [contains.2.2.2]
              rw [normSq]
              linarith [sq_nonneg z.re] }
        · have contains : B.Contains (0 : QI) := by
            exact ⟨not_lt.mp left, not_lt.mp right,
              not_lt.mp below, not_lt.mp above⟩
          exact (outside contains).elim

/-- Quantitative boundary clearance implies the four exact vertex
nonvanishing facts consumed by the finite winding product theorem. -/
theorem boxVertexNonzero_of_boundaryClearance
    {p : GaussianPolynomial} {B : RatBox}
    (clearance : BoxBoundaryClearanceCertificate p B) :
    BoxVertexNonzero p B := by
  constructor
  · intro zero
    have lower := clearance.lower
      (CCL.GaussianRat.mk B.xLower B.yLower)
      ⟨⟨le_rfl, B.x_valid, le_rfl, B.y_valid⟩, Or.inl rfl⟩
    rw [zero, normSq_zero] at lower
    linarith [clearance.positive]
  · intro zero
    have lower := clearance.lower
      (CCL.GaussianRat.mk B.xUpper B.yLower)
      ⟨⟨B.x_valid, le_rfl, le_rfl, B.y_valid⟩,
        Or.inr (Or.inl rfl)⟩
    rw [zero, normSq_zero] at lower
    linarith [clearance.positive]
  · intro zero
    have lower := clearance.lower
      (CCL.GaussianRat.mk B.xUpper B.yUpper)
      ⟨⟨B.x_valid, le_rfl, B.y_valid, le_rfl⟩,
        Or.inr (Or.inr (Or.inr rfl))⟩
    rw [zero, normSq_zero] at lower
    linarith [clearance.positive]
  · intro zero
    have lower := clearance.lower
      (CCL.GaussianRat.mk B.xLower B.yUpper)
      ⟨⟨le_rfl, B.x_valid, B.y_valid, le_rfl⟩,
        Or.inl rfl⟩
    rw [zero, normSq_zero] at lower
    linarith [clearance.positive]

/-- The coordinate factor contributes zero winding outside the origin, so a
quotient winding-four certificate lifts exactly to the original polynomial. -/
theorem quadrupledBoxWinding_eq_four_of_quotient
    {p : GaussianPolynomial} (nonzero : p.isZero = false)
    (zero : p.eval 0 = 0) {B : RatBox} (proper : B.Proper)
    (outside : ¬B.Contains 0)
    (quotientClearance : BoxBoundaryClearanceCertificate (quotient p) B)
    (quotientWinding : quadrupledBoxWinding (quotient p) B = 4) :
    quadrupledBoxWinding p B = 4 := by
  let coordinate := translatedCoordinate 0
  have coordinateWinding : quadrupledBoxWinding coordinate B = 0 :=
    quadrupledBoxWinding_translatedCoordinate_eq_zero_of_not_contains
      0 proper outside
  have coordinateVertices : BoxVertexNonzero coordinate B :=
    translatedCoordinate_vertex_nonzero_of_not_contains 0 outside
  have quotientVertices : BoxVertexNonzero (quotient p) B :=
    boxVertexNonzero_of_boundaryClearance quotientClearance
  have productWinding := quadrupledBoxWinding_mul
    (quotient p) coordinate B quotientVertices coordinateVertices
      proper.1 proper.2
  have nonempty : p.normalize.coeffs ≠ [] := by
    simpa [FTA.ComputablePolynomial.DensePolynomial.isZero] using nonzero
  have coordinatePolynomialIdentity : coordinate.toPolynomial = Polynomial.X := by
    dsimp only [coordinate]
    rw [translatedCoordinate, toPolynomial_sub]
    simp only [GlobalWinding.gaussianConstant, toPolynomial_constant, map_zero]
    simp [GlobalWinding.coordinatePolynomial, toPolynomial_eq_foldl_horner]
  have polynomialIdentity :
      p.toPolynomial = ((quotient p) * coordinate).toPolynomial := by
    rw [toPolynomial_mul, coordinatePolynomialIdentity]
    exact toPolynomial_eq_quotient_mul_X nonempty zero
  calc
    quadrupledBoxWinding p B =
        quadrupledBoxWinding ((quotient p) * coordinate) B :=
      quadrupledBoxWinding_congr B polynomialIdentity
    _ = quadrupledBoxWinding (quotient p) B +
        quadrupledBoxWinding coordinate B := productWinding
    _ = 4 := by rw [quotientWinding, coordinateWinding]; omega

/-- Multiplying a quotient boundary clearance by the box's positive
origin-exclusion margin gives an original-polynomial boundary clearance. -/
def liftQuotientBoundaryClearance
    {p : GaussianPolynomial} (nonzero : p.isZero = false)
    (zero : p.eval 0 = 0) {B : RatBox}
    (outside : ¬B.Contains 0)
    (clearance : BoxBoundaryClearanceCertificate (quotient p) B) :
    BoxBoundaryClearanceCertificate p B := by
  let exclusion := zeroExclusionCertificate outside
  exact
    { bound := clearance.bound * exclusion.bound
      positive := mul_pos clearance.positive exclusion.positive
      lower := by
        intro z boundary
        calc
          clearance.bound * exclusion.bound ≤
              normSq ((quotient p).eval z) * exclusion.bound :=
            mul_le_mul_of_nonneg_right (clearance.lower z boundary)
              exclusion.positive.le
          _ ≤ normSq ((quotient p).eval z) * normSq z :=
            mul_le_mul_of_nonneg_left (exclusion.lower z boundary.1)
              (normSq_nonneg _)
          _ = normSq (p.eval z) := by
            rw [eval_eq_quotient_mul_of_nonzero nonzero zero z, normSq_mul] }

/-- Side-line version of quotient clearance transport. -/
def liftQuotientVerticalLineClearance
    {p : GaussianPolynomial} (nonzero : p.isZero = false)
    (zero : p.eval 0 = 0) {B : RatBox} (outside : ¬B.Contains 0)
    (x : ℚ) (xLower : B.xLower ≤ x) (xUpper : x ≤ B.xUpper)
    (clearance : VerticalLineClearance (quotient p) B x) :
    VerticalLineClearance p B x := by
  let exclusion := zeroExclusionCertificate outside
  exact
    { bound := clearance.bound * exclusion.bound
      positive := mul_pos clearance.positive exclusion.positive
      lower := by
        intro y yLower yUpper
        let z : QI := ⟨x, y⟩
        have contains : B.Contains z := ⟨xLower, xUpper, yLower, yUpper⟩
        calc
          clearance.bound * exclusion.bound ≤
              normSq ((quotient p).eval z) * exclusion.bound :=
            mul_le_mul_of_nonneg_right (clearance.lower y yLower yUpper)
              exclusion.positive.le
          _ ≤ normSq ((quotient p).eval z) * normSq z :=
            mul_le_mul_of_nonneg_left (exclusion.lower z contains)
              (normSq_nonneg _)
          _ = normSq (p.eval z) := by
            rw [eval_eq_quotient_mul_of_nonzero nonzero zero z, normSq_mul] }

/-- Horizontal side-line version of quotient clearance transport. -/
def liftQuotientHorizontalLineClearance
    {p : GaussianPolynomial} (nonzero : p.isZero = false)
    (zero : p.eval 0 = 0) {B : RatBox} (outside : ¬B.Contains 0)
    (y : ℚ) (yLower : B.yLower ≤ y) (yUpper : y ≤ B.yUpper)
    (clearance : HorizontalLineClearance (quotient p) B y) :
    HorizontalLineClearance p B y := by
  let exclusion := zeroExclusionCertificate outside
  exact
    { bound := clearance.bound * exclusion.bound
      positive := mul_pos clearance.positive exclusion.positive
      lower := by
        intro x xLower xUpper
        let z : QI := ⟨x, y⟩
        have contains : B.Contains z := ⟨xLower, xUpper, yLower, yUpper⟩
        calc
          clearance.bound * exclusion.bound ≤
              normSq ((quotient p).eval z) * exclusion.bound :=
            mul_le_mul_of_nonneg_right (clearance.lower x xLower xUpper)
              exclusion.positive.le
          _ ≤ normSq ((quotient p).eval z) * normSq z :=
            mul_le_mul_of_nonneg_left (exclusion.lower z contains)
              (normSq_nonneg _)
          _ = normSq (p.eval z) := by
            rw [eval_eq_quotient_mul_of_nonzero nonzero zero z, normSq_mul] }

/-- Repackage any winding-one state with its current box as ambient. -/
def WindingOneState.reambientSelf
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : WindingOneState p ambient) : WindingOneState p state.box where
  box := state.box
  refinesAmbient := RatBox.refines_refl state.box
  proper := state.proper
  rawWindingFour := state.rawWindingFour
  clearance := state.clearance
  ambientLeftClearance :=
    state.ambientLeftClearance.restrict state.refinesAmbient
  ambientRightClearance :=
    state.ambientRightClearance.restrict state.refinesAmbient
  ambientBottomClearance :=
    state.ambientBottomClearance.restrict state.refinesAmbient
  ambientTopClearance :=
    state.ambientTopClearance.restrict state.refinesAmbient

/-- A zero-excluding quotient winding-one state induces a complete
original-polynomial winding-one state on the same rational box. -/
def WindingOneState.liftQuotient
    {p : GaussianPolynomial} (nonzero : p.isZero = false)
    (zero : p.eval 0 = 0) {ambient : RatBox}
    (state : WindingOneState (quotient p) ambient)
    (outside : ¬state.box.Contains 0) : WindingOneState p state.box := by
  let left := state.ambientLeftClearance.restrict state.refinesAmbient
  let right := state.ambientRightClearance.restrict state.refinesAmbient
  let bottom := state.ambientBottomClearance.restrict state.refinesAmbient
  let top := state.ambientTopClearance.restrict state.refinesAmbient
  exact
    { box := state.box
      refinesAmbient := RatBox.refines_refl state.box
      proper := state.proper
      rawWindingFour := quadrupledBoxWinding_eq_four_of_quotient nonzero zero
        state.proper outside state.clearance state.rawWindingFour
      clearance := liftQuotientBoundaryClearance nonzero zero outside
        state.clearance
      ambientLeftClearance := liftQuotientVerticalLineClearance nonzero zero
        outside state.box.xLower le_rfl state.box.x_valid left
      ambientRightClearance := liftQuotientVerticalLineClearance nonzero zero
        outside state.box.xUpper state.box.x_valid le_rfl right
      ambientBottomClearance := liftQuotientHorizontalLineClearance nonzero zero
        outside state.box.yLower le_rfl state.box.y_valid bottom
      ambientTopClearance := liftQuotientHorizontalLineClearance nonzero zero
        outside state.box.yUpper state.box.y_valid le_rfl top }

end GaussianZeroDeflation
end FTA
